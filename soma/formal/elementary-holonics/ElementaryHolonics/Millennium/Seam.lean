import Mathlib.NumberTheory.LSeries.RiemannZeta
import ElementaryHolonics.Millennium.Hand

/-!
# The seam — the placement law, and the one factor that is in another chart

The comb's reflection law is an **involution**, and the locus it fixes is where the placement
question lives.  This file proves that the critical line *is* a fixed locus — of the
conjugate-reflection, not of the plain one — so "placement is the fixed locus of an involution"
is discharged rather than asserted, and the standard statement is then shown to be exactly the
composed one.

The second half names the asymmetry that separates the case that is proved from the case that is
open: **the local factors of the comb do not all live in the same chart.** The factors attached
to the irreducibles are rational in `p^{-s}`; the one attached to the place at infinity is not.

Every `theorem` here is discharged.  Every open statement is a named `Prop`.
-/

namespace Soma.Holonics.Millennium.Seam

open Complex

/-! ## 1. The seam is a fixed locus, and that is a theorem -/

/-- The **conjugate reflection**: the comb's reflection composed with the anti-linear
conjugation.  This is the involution whose fixed locus is a *line* rather than a point. -/
def conjugateReflection (s : ℂ) : ℂ := 1 - (starRingEnd ℂ) s

/-- The plain reflection `s ↦ 1 − s` of the comb's functional equation. -/
def combReflection (s : ℂ) : ℂ := 1 - s

/-- **Both reflections are involutions.** -/
theorem combReflection_involutive : Function.Involutive combReflection := by
  intro s; simp [combReflection]

theorem conjugateReflection_involutive : Function.Involutive conjugateReflection := by
  intro s; simp [conjugateReflection]

/-- **The plain reflection fixes exactly one point: the half.** -/
theorem theHalfIsTheOnlyPointThePlainReflectionFixes (s : ℂ) :
    combReflection s = s ↔ s = 1 / 2 := by
  simp only [combReflection, sub_eq_iff_eq_add]
  constructor <;> intro h
  · linear_combination -h / 2
  · rw [h]; norm_num

/-- **The seam is exactly the locus the conjugate reflection fixes.**

This is the placement doctrine discharged: the line on which the modes are conjectured to sit is
not chosen, it is the fixed locus of the involution the comb already carries.

*Aside: the critical line `Re s = 1/2` is `Fix(s ↦ 1 − s̄)`.* -/
theorem theSeamIsTheFixedLocusOfTheConjugateReflection (s : ℂ) :
    conjugateReflection s = s ↔ s.re = 1 / 2 := by
  simp only [conjugateReflection, sub_eq_iff_eq_add, Complex.add_conj]
  constructor
  · intro h
    have h' : (1 : ℝ) = 2 * s.re := by exact_mod_cast h
    linarith
  · intro h
    have h' : (1 : ℝ) = 2 * s.re := by linarith
    exact_mod_cast h'

/-- The seam, as a set. -/
def theSelfConjugateSeam : Set ℂ := {s : ℂ | conjugateReflection s = s}

theorem mem_seam_iff (s : ℂ) : s ∈ theSelfConjugateSeam ↔ s.re = 1 / 2 :=
  theSeamIsTheFixedLocusOfTheConjugateReflection s

/-! ## 2. The comb obeys the reflection law, and the standard statement is the composed one -/

/-- **The completed comb is reflection-symmetric.**

*Aside: the functional equation `ξ(1 − s) = ξ(s)`.* -/
theorem theCompletedCombObeysTheReflectionLaw (s : ℂ) :
    completedRiemannZeta (combReflection s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- A mode of the comb: a zero that is neither one of the reflection's own zeros nor the pole. -/
def IsMode (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- **Every mode sits on the self-conjugate seam.**

This is the open line, stated in the composed dialect.

*Aside: the Riemann Hypothesis.* -/
def EveryModeSitsOnTheSelfConjugateSeam : Prop :=
  ∀ s : ℂ, IsMode s → s ∈ theSelfConjugateSeam

/-- **The composed statement is the standard one.**

This theorem is the whole justification for the dialect: renaming is only legitimate if the
renamed statement is provably the same statement, and here it is, by the fixed-locus theorem
above rather than by fiat. -/
theorem theComposedStatementIsTheStandardOne :
    EveryModeSitsOnTheSelfConjugateSeam ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htriv hpole
    exact (mem_seam_iff s).mp (h s ⟨hz, htriv, hpole⟩)
  · intro h s hs
    exact (mem_seam_iff s).mpr (h s hs.1 hs.2.1 hs.2.2)

/-! ## 3. One local factor is not in the same chart as the others

The comb factors into one piece per place.  The pieces attached to the irreducibles are rational
functions of `p^{-s}`.  The piece attached to the place at infinity is the archimedean factor,
and it is not — it satisfies no algebraic differential equation at all.

**This asymmetry is the difference between the case that is proved and the case that is open.**
Over a function field there is no place at infinity; every local factor is algebraic, the comb
is a rational function, and the placement follows from the positivity of a pairing on a
finite-dimensional realizer population.  Over the rationals there is exactly one factor that is
not algebraic, and no realizer has been built at that place. -/

/-- The **archimedean local factor**, carrying the halves.

*Aside: `Gammaℝ s = π^{-s/2} Γ(s/2)`.  The two halves are the square root of the Jacobian of the
logarithmic substitution, which is why the seam sits at the half and not somewhere else.* -/
noncomputable def archimedeanFactor (s : ℂ) : ℂ := Gammaℝ s

/-- **The comb is the completed comb divided by its archimedean factor.**  Stated so the factor
is visible as a factor rather than as a normalization. -/
theorem theCombIsTheCompletedCombOverItsArchimedeanFactor {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s / archimedeanFactor s :=
  riemannZeta_def_of_ne_zero hs

/-! ### What the archimedean factor is, and what it does not return

The regularized product of the whole tower `s, s+1, s+2, …` is the reciprocal of the gamma
factor up to a constant — `∏_{n≥0}(s+n) = √(2π)/Γ(s)` under zeta regularization.  That is a
condensation of a far population into a compact representative, performed by a declared quotient
that discards a divergence **without exhibiting it**.  Under this project's compression
discipline it is a compression whose decoder is never run backwards.

No proposition is stated for this here.  The regularized product has no definition in scope, and
a `Prop` that could not fail would be worse than no `Prop` at all — it would read as an open
statement while carrying nothing.  The observation is recorded and the formalization is owed. -/

/-- **The bridge between the two charts of the same object.**

The seam statement and the hand's cancellation statement are classically equivalent.  The
equivalence is a real theorem and it is not formalized here; naming it open is the honest
position, and it is where a formalization effort would go next.

*Aside: RH ⟺ `Σ_{n≤x} λ(n) = O(x^{1/2+ε})`.* -/
def ThePlacementAndTheHandAreOneStatement : Prop :=
  EveryModeSitsOnTheSelfConjugateSeam ↔ Hand.TheHandCancelsToSquareRoot

/-- The same bridge on the orientation.

*Aside: RH ⟺ `M(x) = O(x^{1/2+ε})`.* -/
def ThePlacementAndTheOrientationAreOneStatement : Prop :=
  EveryModeSitsOnTheSelfConjugateSeam ↔ Hand.TheOrientationCancelsToSquareRoot

/-- **If the bridge holds, then the refuted magnitude claim implies the placement.**

This is discharged, and it is the useful shape: it shows exactly how much a refutation of the
magnitude claim costs — nothing at all for the placement, because the implication runs the other
way.  A refutation of `TheOrientationSumStaysUnderItsRoot` leaves
`EveryModeSitsOnTheSelfConjugateSeam` untouched. -/
theorem theRefutedMagnitudeClaimWouldHaveSufficed
    (bridge : ThePlacementAndTheOrientationAreOneStatement) :
    Hand.TheOrientationSumStaysUnderItsRoot → EveryModeSitsOnTheSelfConjugateSeam :=
  fun h => bridge.mpr (Hand.theMagnitudeClaimIsStrictlyStronger h)

end Soma.Holonics.Millennium.Seam

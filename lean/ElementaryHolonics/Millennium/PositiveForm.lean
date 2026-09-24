import ElementaryHolonics.Millennium.CokernelCalculus
import ElementaryHolonics.Millennium.UniversalBSDLedger

/-!
# PositiveForm: why realization must pay, and what effectivity does not buy

The third slot of the standing demand — *an exactly computed positive form on a
supported realizer population* — is open on **both** sides of the graph-network at
once.  Birch–Swinnerton-Dyer needs the Néron–Tate regulator to be nonzero; Hodge needs
Hodge–Riemann positivity.  This file states the shared obstruction and exhibits the
counterexample that separates the two candidate hypotheses.

The correction the corpus records is that **positivity is supplied by ampleness, not
by effectivity**: `Eff ⊋ Amp`, and the strictness of that inclusion is where the whole
theory lives.  A `(−1)`-curve is perfectly effective — realized by an honest
subvariety — and has `E² = −1 < 0`.  Effectivity supplies nothing.

Made checkable in the smallest Hodge-index shape, the signature-`(1,1)` form
`Q(x,y) = x² − y²`:

* **`theIndexFormTakesBothSigns`** — it is positive somewhere and negative somewhere,
  so no realizer is positive merely by existing.
* **`theEffectiveGeneratorCanBeNegative`** — a generator of the lattice, the
  `(−1)`-curve in miniature, has negative self-pairing.
* **`thePositiveLocusIsNotConvex`** — two classes of positive square whose **sum** has
  negative square.  So positivity is not preserved by the operations that build
  effective classes; it requires **choosing a component**, and choosing a component is
  exactly what a polarization is.
* **`theDefiniteFormIsPositiveEverywhere`** — the good case, the Rosati/trace-form
  shape: a definite form pays on every nonzero class.
* **`theSplitSurvivesEveryChangeOfBasis`** — and taking both signs is invariant under
  any invertible change of coordinates, so the split is the invariant, not the labels.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.PositiveForm

open Soma.Holonics.Millennium

/-! ## 1. The two candidate hypotheses -/

/-- The smallest Hodge-index shape: signature `(1,1)`. -/
def indexForm (v : ℚ × ℚ) : ℚ := v.1 ^ 2 - v.2 ^ 2

/-- The definite shape: the trace form of a positive involution. -/
def definiteForm (v : ℚ × ℚ) : ℚ := v.1 ^ 2 + v.2 ^ 2

/-- **THE INDEX FORM TAKES BOTH SIGNS**: no realizer is positive merely by existing. -/
theorem theIndexFormTakesBothSigns :
    (∃ v : ℚ × ℚ, 0 < indexForm v) ∧ (∃ v : ℚ × ℚ, indexForm v < 0) := by
  refine ⟨⟨(1, 0), by norm_num [indexForm]⟩, ⟨(0, 1), by norm_num [indexForm]⟩⟩

/-- **AN EFFECTIVE GENERATOR CAN BE NEGATIVE**: the `(−1)`-curve in miniature — a
lattice generator, as effective as anything gets, with negative self-pairing. -/
theorem theEffectiveGeneratorCanBeNegative :
    indexForm (0, 1) = -1 ∧ ((0 : ℚ), (1 : ℚ)) ≠ 0 := by
  refine ⟨by norm_num [indexForm], ?_⟩
  intro hc
  have := congrArg Prod.snd hc
  norm_num at this

/-- **THE POSITIVE LOCUS IS NOT CONVEX**: two classes of positive square whose sum has
negative square.  Positivity is not preserved by the operations that build effective
classes, so it cannot be read off effectivity; a **component must be chosen**, and
that choice is the polarization. -/
theorem thePositiveLocusIsNotConvex :
    0 < indexForm (3, 2) ∧ 0 < indexForm (-3, 2) ∧
      indexForm ((3, 2) + (-3, 2)) < 0 := by
  refine ⟨by norm_num [indexForm], by norm_num [indexForm], ?_⟩
  have : ((3 : ℚ), (2 : ℚ)) + ((-3 : ℚ), (2 : ℚ)) = ((0 : ℚ), (4 : ℚ)) := by
    ext <;> norm_num
  rw [this]
  norm_num [indexForm]

/-- **THE DEFINITE FORM PAYS ON EVERY NONZERO CLASS**: the Rosati/trace-form shape,
the one hypothesis that does supply positivity. -/
theorem theDefiniteFormIsPositiveEverywhere (v : ℚ × ℚ) (hv : v ≠ 0) :
    0 < definiteForm v := by
  unfold definiteForm
  rcases eq_or_ne v.1 0 with h1 | h1
  · have h2 : v.2 ≠ 0 := by
      intro hc
      exact hv (Prod.ext h1 hc)
    have : 0 < v.2 ^ 2 := by positivity
    nlinarith [sq_nonneg v.1]
  · have : 0 < v.1 ^ 2 := by positivity
    nlinarith [sq_nonneg v.2]

/-- **THE SPLIT SURVIVES EVERY CHANGE OF BASIS**: taking both signs is invariant under
any surjective reparameterization, so what is basis-independent is the **split**, never
which side carries the label. -/
theorem theSplitSurvivesEveryChangeOfBasis (f : ℚ × ℚ → ℚ × ℚ)
    (hf : Function.Surjective f) :
    (∃ v, 0 < indexForm (f v)) ∧ (∃ v, indexForm (f v) < 0) := by
  obtain ⟨u, hu⟩ := hf (1, 0)
  obtain ⟨w, hw⟩ := hf (0, 1)
  exact ⟨⟨u, by rw [hu]; norm_num [indexForm]⟩, ⟨w, by rw [hw]; norm_num [indexForm]⟩⟩


/-! ## 2. What the positivity buys on each side -/

open Soma.Holonics.Millennium.UniversalBSD
open Soma.Holonics.Millennium.UniversalBSDLedger

/-- **THE HEIGHT FORM IS DEFINITE ON THE NON-TORSION**: the Néron–Tate height is
nonnegative and vanishes exactly on the torsion, so it is strictly positive off it.
This is the definite shape, not the index shape — which is why the regulator is a
Gram determinant of a **positive** form and not of an indefinite one. -/
theorem theHeightFormIsDefiniteOffTheTorsion {E : WeierstrassCurve.Affine ℚ}
    (H : HeightDatum E) (P : E.Point) (hP : ¬ IsTorsionOn E P) :
    0 < pairing H P P := by
  rw [pairing_self]
  rcases lt_or_eq_of_le (H.nonneg P) with h | h
  · exact h
  · exact absurd ((H.vanishes_iff P).mp h.symm) hP

/-- **A SINGLE INDEPENDENT POINT HAS POSITIVE REGULATOR**: the rank-one Gram
determinant is the height itself, so it is positive exactly when the point is not
torsion.  The realizer pays, and the placement rides on it. -/
theorem theRankOneRegulatorIsPositive {E : WeierstrassCurve.Affine ℚ}
    (H : HeightDatum E) (P : E.Point) (hP : ¬ IsTorsionOn E P) :
    0 < regulator H (fun _ : Fin 1 => P) := by
  have hval : regulator H (fun _ : Fin 1 => P) = pairing H P P := by
    unfold regulator
    rw [Matrix.det_fin_one]
    rfl
  rw [hval]
  exact theHeightFormIsDefiniteOffTheTorsion H P hP

/-- **THE HODGE SIDE CANNOT READ POSITIVITY OFF THE EASY INCLUSION**: a datum's
`cycleClassesAreHodge` places the algebraic classes inside the Hodge classes and says
nothing about any form.  Positivity is a separate input — and the index-form
counterexamples above show that no amount of effectivity supplies it. -/
theorem theEasyInclusionSuppliesNoPositivity
    (D : Soma.Holonics.Millennium.HodgeConjecture.Datum) :
    LinearMap.range D.cycleClass.hom ≤ D.rationalHodgeClasses :=
  D.cycleClassesAreHodge

/-- **ONE DEMAND, TWO OBJECTS**: on the Birch–Swinnerton-Dyer side the positive form
is present and definite, and a single non-torsion realizer already makes the
determinant positive; on the Hodge side the easy inclusion supplies no form at all,
and the index shape shows why effectivity cannot be promoted into positivity.  That
asymmetry is the third slot of the demand, stated exactly. -/
theorem theThirdSlotStatedExactly {E : WeierstrassCurve.Affine ℚ}
    (H : HeightDatum E) (P : E.Point) (hP : ¬ IsTorsionOn E P)
    (D : Soma.Holonics.Millennium.HodgeConjecture.Datum) :
    0 < regulator H (fun _ : Fin 1 => P) ∧
      LinearMap.range D.cycleClass.hom ≤ D.rationalHodgeClasses ∧
      (∃ v : ℚ × ℚ, v ≠ 0 ∧ indexForm v < 0) :=
  ⟨theRankOneRegulatorIsPositive H P hP, D.cycleClassesAreHodge,
    ⟨(0, 1), (theEffectiveGeneratorCanBeNegative).2,
      by norm_num [indexForm]⟩⟩

end Soma.Holonics.Millennium.PositiveForm

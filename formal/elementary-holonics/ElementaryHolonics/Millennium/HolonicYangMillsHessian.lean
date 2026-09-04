import ElementaryHolonics.Millennium.HolonicYangMillsDescent

/-!
# The Yang--Mills Hessian: the second variation of the energy

Along any linear path `A + εB` the Yang--Mills energy is a quartic polynomial in `ε`.  Its first
coefficient is the first variation `∫ Σ B((D_A B)_ij, F_ij)`, and its second coefficient is the
Hessian quadratic form

```text
Hess_A(B, B) = ∫_box Σ_{ij} ( B((D_A B)_ij, (D_A B)_ij) + 2 B([B_i, B_j], F_ij) ),
```

the linearized Weitzenböck operator paired with itself.  Only `C¹` regularity of `A` and `B` is
needed for the expansion; the identities are exact.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.HolonicYangMillsHessian

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
open Soma.Holonics.Millennium.HolonicYangMillsDescent

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- The first variation of the energy along `B`. -/
def firstVariation (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤) : ℝ :=
  ∫ x in unitBox (n + 1), ∑ i, ∑ j, P.B (covariantVariation A B i j x) (curvature A i j x)

/-- **The Hessian quadratic form** of the energy along `B`. -/
def hessian (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤) : ℝ :=
  ∫ x in unitBox (n + 1), ∑ i, ∑ j,
    (P.B (covariantVariation A B i j x) (covariantVariation A B i j x) +
      2 * P.B (bracket (B i x) (B j x)) (curvature A i j x))

/-- The cubic and quartic coefficients. -/
def cubicCoefficient (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤) : ℝ :=
  ∫ x in unitBox (n + 1), ∑ i, ∑ j,
    P.B (bracket (B i x) (B j x)) (covariantVariation A B i j x)

def quarticCoefficient (P : SymmetricPairing 𝔤) (_A B : Connection (n + 1) 𝔤) : ℝ :=
  ∫ x in unitBox (n + 1), ∑ i, ∑ j, P.B (bracket (B i x) (B j x)) (bracket (B i x) (B j x))

/-- **The energy along a linear path is a quartic in `ε`.** -/
theorem yangMillsEnergy_add_smul (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 1 (A i)) (hB : ∀ i, ContDiff ℝ 1 (B i)) (ε : ℝ) :
    yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y) =
      yangMillsEnergy P.toInvariantPairing A + ε * firstVariation P A B +
        ε ^ 2 * ((1 / 2) * hessian P A B) + ε ^ 3 * cubicCoefficient P A B +
        ε ^ 4 * ((1 / 2) * quarticCoefficient P A B) := by
  have hAd : ∀ i x, DifferentiableAt ℝ (A i) x := fun i x => differentiableAt_of_contDiff_one (hA i) x
  have hBd : ∀ i x, DifferentiableAt ℝ (B i) x := fun i x => differentiableAt_of_contDiff_one (hB i) x
  set V : Fin (n + 1) → Fin (n + 1) → Base (n + 1) → 𝔤 := fun i j => covariantVariation A B i j with hV
  set W : Fin (n + 1) → Fin (n + 1) → Base (n + 1) → 𝔤 := fun i j x => bracket (B i x) (B j x) with hW
  set c0 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (curvature A i j x) (curvature A i j x) with hc0
  set c1 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (V i j x) (curvature A i j x) with hc1
  set c2 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j,
    (P.B (V i j x) (V i j x) + 2 * P.B (W i j x) (curvature A i j x)) with hc2
  set c3 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (W i j x) (V i j x) with hc3
  set c4 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (W i j x) (W i j x) with hc4
  have hpt : ∀ x : Base (n + 1),
      (∑ i, ∑ j, P.B (curvature (fun k y => A k y + ε • B k y) i j x)
        (curvature (fun k y => A k y + ε • B k y) i j x)) =
      c0 x + ε * (2 * c1 x) + ε ^ 2 * c2 x + ε ^ 3 * (2 * c3 x) + ε ^ 4 * c4 x := by
    intro x
    have hterm : ∀ i j, P.B (curvature (fun k y => A k y + ε • B k y) i j x)
        (curvature (fun k y => A k y + ε • B k y) i j x) =
        P.B (curvature A i j x) (curvature A i j x) +
          ε * (2 * P.B (V i j x) (curvature A i j x)) +
          ε ^ 2 * (P.B (V i j x) (V i j x) + 2 * P.B (W i j x) (curvature A i j x)) +
          ε ^ 3 * (2 * P.B (W i j x) (V i j x)) +
          ε ^ 4 * P.B (W i j x) (W i j x) := by
      intro i j
      rw [curvature_add_smul A B hAd hBd ε i j x, pairing_expand P.toInvariantPairing]
      have s1 := P.symm (curvature A i j x) (V i j x)
      have s2 := P.symm (curvature A i j x) (W i j x)
      have s3 := P.symm (V i j x) (W i j x)
      simp only [hV, hW] at s1 s2 s3 ⊢
      rw [s1, s2, s3]
      ring
    simp only [hterm, hc0, hc1, hc2, hc3, hc4, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  -- continuity
  have hFc : ∀ i j, Continuous (curvature A i j) :=
    fun i j => contDiff_zero.mp (contDiff_curvature A hA i j)
  have hVc : ∀ i j, Continuous (V i j) := by
    intro i j
    simp only [hV]
    exact ((contDiff_zero.mp (contDiff_covariantDerivative A hA (hB j) i)).sub
      (contDiff_zero.mp (contDiff_covariantDerivative A hA (hB i) j)))
  have hWc : ∀ i j, Continuous (W i j) := fun i j =>
    contDiff_zero.mp (contDiff_bracket ((hB i).of_le (by norm_num)) ((hB j).of_le (by norm_num)))
  have hpair : ∀ {f g : Base (n + 1) → 𝔤}, Continuous f → Continuous g →
      Continuous fun x => P.B (f x) (g x) :=
    fun hf hg => (P.B.continuous.comp hf).clm_apply hg
  have hcompact : IsCompact (unitBox (n + 1)) := isCompact_Icc
  have hint : ∀ {c : Base (n + 1) → ℝ}, Continuous c → IntegrableOn c (unitBox (n + 1)) :=
    fun hc => hc.continuousOn.integrableOn_compact hcompact
  have h0c : Continuous c0 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hFc i j) (hFc i j)
  have h1c : Continuous c1 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hVc i j) (hFc i j)
  have h2c : Continuous c2 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (hpair (hVc i j) (hVc i j)).add ((hpair (hWc i j) (hFc i j)).const_mul 2)
  have h3c : Continuous c3 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hWc i j) (hVc i j)
  have h4c : Continuous c4 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hWc i j) (hWc i j)
  unfold yangMillsEnergy firstVariation hessian cubicCoefficient quarticCoefficient
  rw [setIntegral_congr_fun hcompact.measurableSet (fun x _ => hpt x)]
  rw [integral_add, integral_add, integral_add, integral_add, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  · simp only [hc0, hc1, hc2, hc3, hc4, hV, hW]
    ring
  · exact hint h0c
  · exact ((hint h1c).const_mul 2).const_mul _
  · exact (hint h0c).add (((hint h1c).const_mul 2).const_mul _)
  · exact (hint h2c).const_mul _
  · exact ((hint h0c).add (((hint h1c).const_mul 2).const_mul _)).add ((hint h2c).const_mul _)
  · exact ((hint h3c).const_mul 2).const_mul _
  · exact (((hint h0c).add (((hint h1c).const_mul 2).const_mul _)).add ((hint h2c).const_mul _)).add
      (((hint h3c).const_mul 2).const_mul _)
  · exact (hint h4c).const_mul _

/-- **The first derivative is the first variation.** -/
theorem hasDerivAt_yangMillsEnergy (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 1 (A i)) (hB : ∀ i, ContDiff ℝ 1 (B i)) (ε : ℝ) :
    HasDerivAt (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y))
      (firstVariation P A B + 2 * ε * ((1 / 2) * hessian P A B) +
        3 * ε ^ 2 * cubicCoefficient P A B + 4 * ε ^ 3 * ((1 / 2) * quarticCoefficient P A B)) ε := by
  have hfun : (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y)) =
      fun ε : ℝ => yangMillsEnergy P.toInvariantPairing A + ε * firstVariation P A B +
        ε ^ 2 * ((1 / 2) * hessian P A B) + ε ^ 3 * cubicCoefficient P A B +
        ε ^ 4 * ((1 / 2) * quarticCoefficient P A B) :=
    funext fun ε => yangMillsEnergy_add_smul P A B hA hB ε
  rw [hfun]
  have h1 : HasDerivAt (fun ε : ℝ => ε * firstVariation P A B) (firstVariation P A B) ε := by
    simpa using (hasDerivAt_id ε).mul_const (firstVariation P A B)
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * ((1 / 2) * hessian P A B))
      (2 * ε * ((1 / 2) * hessian P A B)) ε := by
    have := (hasDerivAt_pow 2 ε).mul_const ((1 / 2) * hessian P A B)
    simpa using this
  have h3 : HasDerivAt (fun ε : ℝ => ε ^ 3 * cubicCoefficient P A B)
      (3 * ε ^ 2 * cubicCoefficient P A B) ε := by
    have := (hasDerivAt_pow 3 ε).mul_const (cubicCoefficient P A B)
    simpa using this
  have h4 : HasDerivAt (fun ε : ℝ => ε ^ 4 * ((1 / 2) * quarticCoefficient P A B))
      (4 * ε ^ 3 * ((1 / 2) * quarticCoefficient P A B)) ε := by
    have := (hasDerivAt_pow 4 ε).mul_const ((1 / 2) * quarticCoefficient P A B)
    simpa using this
  have := ((((hasDerivAt_const ε (yangMillsEnergy P.toInvariantPairing A)).add h1).add h2).add h3).add h4
  exact (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv (by ring)

/-- **The second derivative at zero is the Hessian.** -/
theorem deriv_deriv_yangMillsEnergy (P : SymmetricPairing 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 1 (A i)) (hB : ∀ i, ContDiff ℝ 1 (B i)) :
    deriv (deriv fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y)) 0 =
      hessian P A B := by
  have hd : deriv (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y)) =
      fun ε : ℝ => firstVariation P A B + 2 * ε * ((1 / 2) * hessian P A B) +
        3 * ε ^ 2 * cubicCoefficient P A B + 4 * ε ^ 3 * ((1 / 2) * quarticCoefficient P A B) :=
    funext fun ε => (hasDerivAt_yangMillsEnergy P A B hA hB ε).deriv
  rw [hd]
  have h2 : HasDerivAt (fun ε : ℝ => 2 * ε * ((1 / 2) * hessian P A B)) (hessian P A B) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const ((1 / 2) * hessian P A B)
    simpa using this
  have h3 : HasDerivAt (fun ε : ℝ => 3 * ε ^ 2 * cubicCoefficient P A B) 0 0 := by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).const_mul 3).mul_const (cubicCoefficient P A B)
    simpa using this
  have h4 : HasDerivAt (fun ε : ℝ => 4 * ε ^ 3 * ((1 / 2) * quarticCoefficient P A B)) 0 0 := by
    have := ((hasDerivAt_pow 3 (0 : ℝ)).const_mul 4).mul_const ((1 / 2) * quarticCoefficient P A B)
    simpa using this
  have := (((hasDerivAt_const (0 : ℝ) (firstVariation P A B)).add h2).add h3).add h4
  have h : HasDerivAt (fun ε : ℝ => firstVariation P A B + 2 * ε * ((1 / 2) * hessian P A B) +
      3 * ε ^ 2 * cubicCoefficient P A B + 4 * ε ^ 3 * ((1 / 2) * quarticCoefficient P A B))
      (0 + hessian P A B + 0 + 0) 0 :=
    this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  rw [h.deriv]
  ring

section Audit

#print axioms yangMillsEnergy_add_smul
#print axioms deriv_deriv_yangMillsEnergy

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsHessian

import ElementaryHolonics.Millennium.HolonicYangMillsGlobalEnergy

/-!
# The Yang--Mills direction is a descent direction for the energy

Along the linear path `A + εG` the curvature is a quadratic polynomial in `ε`, so the Yang--Mills
energy is a quartic polynomial in `ε` with integral coefficients, and its derivative at `ε = 0` is
the first-variation integral.  By the global energy identity that derivative is
`−2 Σ_j ∫_box B(G_j, G_j)`: for a symmetric ad-invariant pairing with nonnegative squares the
Yang--Mills direction never increases the energy, and strictly decreases it unless `G = 0`
almost everywhere.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.HolonicYangMillsDescent

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
open Soma.Holonics.Millennium.HolonicYangMillsGlobalEnergy

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- A symmetric ad-invariant pairing. -/
structure SymmetricPairing (𝔤 : Type*) [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]
    extends InvariantPairing 𝔤 where
  symm : ∀ x y, B x y = B y x

/-- The Yang--Mills energy on the unit box. -/
def yangMillsEnergy (P : InvariantPairing 𝔤) (A : Connection (n + 1) 𝔤) : ℝ :=
  (1 / 2) * ∫ x in unitBox (n + 1), ∑ i, ∑ j, P.B (curvature A i j x) (curvature A i j x)

theorem pairing_expand (P : InvariantPairing 𝔤) (x y z : 𝔤) (ε : ℝ) :
    P.B (x + ε • y + (ε * ε) • z) (x + ε • y + (ε * ε) • z) =
      P.B x x + ε * (P.B y x + P.B x y) + ε ^ 2 * (P.B z x + P.B y y + P.B x z) +
        ε ^ 3 * (P.B z y + P.B y z) + ε ^ 4 * P.B z z := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  ring

/-- **The energy along the Yang--Mills direction is a quartic in `ε` whose derivative at `0` is
the first-variation integral.** -/
theorem hasDerivAt_yangMillsEnergy_direction (P : SymmetricPairing 𝔤) (A : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 3 (A i)) (hper : ∀ i, IsOnePeriodicBase (A i)) :
    HasDerivAt (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing
        (fun k y => A k y + ε • yangMillsDirection A k y))
      (-2 * ∑ j, ∫ x in unitBox (n + 1),
        P.B (yangMillsDirection A j x) (yangMillsDirection A j x)) 0 := by
  have hA1 : ∀ i, ContDiff ℝ 1 (A i) := fun i => (hA i).of_le (by norm_num)
  have hA2 : ∀ i, ContDiff ℝ 2 (A i) := fun i => (hA i).of_le (by norm_num)
  have hAd : ∀ i x, DifferentiableAt ℝ (A i) x := fun i x => differentiableAt_of_contDiff (hA2 i) x
  have hF2 : ∀ k l, ContDiff ℝ 2 (curvature A k l) := fun k l => contDiff_curvature A hA k l
  have hG1 : ∀ j, ContDiff ℝ 1 (yangMillsDirection A j) := by
    intro j
    unfold yangMillsDirection
    exact ContDiff.sum fun k _ => contDiff_covariantDerivative A hA2 (hF2 k j) k
  have hGd : ∀ i x, DifferentiableAt ℝ (yangMillsDirection A i) x :=
    fun i x => differentiableAt_of_contDiff_one (hG1 i) x
  set G := yangMillsDirection A with hG
  set V : Fin (n + 1) → Fin (n + 1) → Base (n + 1) → 𝔤 := fun i j => covariantVariation A G i j with hV
  set W : Fin (n + 1) → Fin (n + 1) → Base (n + 1) → 𝔤 := fun i j x => bracket (G i x) (G j x) with hW
  -- the coefficient fields
  set c0 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (curvature A i j x) (curvature A i j x) with hc0
  set c1 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j,
    (P.B (V i j x) (curvature A i j x) + P.B (curvature A i j x) (V i j x)) with hc1
  set c2 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j,
    (P.B (W i j x) (curvature A i j x) + P.B (V i j x) (V i j x) + P.B (curvature A i j x) (W i j x))
    with hc2
  set c3 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, (P.B (W i j x) (V i j x) + P.B (V i j x) (W i j x))
    with hc3
  set c4 : Base (n + 1) → ℝ := fun x => ∑ i, ∑ j, P.B (W i j x) (W i j x) with hc4
  -- pointwise quartic
  have hpt : ∀ (ε : ℝ) (x : Base (n + 1)),
      (∑ i, ∑ j, P.B (curvature (fun k y => A k y + ε • G k y) i j x)
        (curvature (fun k y => A k y + ε • G k y) i j x)) =
      c0 x + ε * c1 x + ε ^ 2 * c2 x + ε ^ 3 * c3 x + ε ^ 4 * c4 x := by
    intro ε x
    have hterm : ∀ i j, P.B (curvature (fun k y => A k y + ε • G k y) i j x)
        (curvature (fun k y => A k y + ε • G k y) i j x) =
        P.B (curvature A i j x) (curvature A i j x) +
          ε * (P.B (V i j x) (curvature A i j x) + P.B (curvature A i j x) (V i j x)) +
          ε ^ 2 * (P.B (W i j x) (curvature A i j x) + P.B (V i j x) (V i j x) +
            P.B (curvature A i j x) (W i j x)) +
          ε ^ 3 * (P.B (W i j x) (V i j x) + P.B (V i j x) (W i j x)) +
          ε ^ 4 * P.B (W i j x) (W i j x) := by
      intro i j
      rw [curvature_add_smul A G hAd hGd ε i j x]
      exact pairing_expand P.toInvariantPairing _ _ _ ε
    simp only [hterm, hc0, hc1, hc2, hc3, hc4, mul_add, Finset.sum_add_distrib, Finset.mul_sum] <;> ring
  -- continuity of the coefficients
  have hFc : ∀ i j, Continuous (curvature A i j) := fun i j => (hF2 i j).continuous
  have hVc : ∀ i j, Continuous (V i j) := by
    intro i j
    simp only [hV]
    exact ((contDiff_zero.mp (contDiff_covariantDerivative A hA1 (hG1 j) i)).sub
      (contDiff_zero.mp (contDiff_covariantDerivative A hA1 (hG1 i) j)))
  have hWc : ∀ i j, Continuous (W i j) := fun i j =>
    (contDiff_zero.mp (contDiff_bracket ((hG1 i).of_le (by norm_num)) ((hG1 j).of_le (by norm_num))))
  have hpair : ∀ {f g : Base (n + 1) → 𝔤}, Continuous f → Continuous g →
      Continuous fun x => P.B (f x) (g x) :=
    fun hf hg => (P.B.continuous.comp hf).clm_apply hg
  have hcompact : IsCompact (unitBox (n + 1)) := isCompact_Icc
  have hint : ∀ {c : Base (n + 1) → ℝ}, Continuous c → IntegrableOn c (unitBox (n + 1)) :=
    fun hc => hc.continuousOn.integrableOn_compact hcompact
  have h0c : Continuous c0 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hFc i j) (hFc i j)
  have h1c : Continuous c1 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (hpair (hVc i j) (hFc i j)).add (hpair (hFc i j) (hVc i j))
  have h2c : Continuous c2 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((hpair (hWc i j) (hFc i j)).add (hpair (hVc i j) (hVc i j))).add (hpair (hFc i j) (hWc i j))
  have h3c : Continuous c3 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (hpair (hWc i j) (hVc i j)).add (hpair (hVc i j) (hWc i j))
  have h4c : Continuous c4 := continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hpair (hWc i j) (hWc i j)
  set I0 := ∫ x in unitBox (n + 1), c0 x with hI0
  set I1 := ∫ x in unitBox (n + 1), c1 x with hI1
  set I2 := ∫ x in unitBox (n + 1), c2 x with hI2
  set I3 := ∫ x in unitBox (n + 1), c3 x with hI3
  set I4 := ∫ x in unitBox (n + 1), c4 x with hI4
  -- the energy is the quartic
  have hE : ∀ ε : ℝ, yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • G k y) =
      (1 / 2) * (I0 + ε * I1 + ε ^ 2 * I2 + ε ^ 3 * I3 + ε ^ 4 * I4) := by
    intro ε
    unfold yangMillsEnergy
    congr 1
    rw [setIntegral_congr_fun hcompact.measurableSet (fun x _ => hpt ε x)]
    rw [integral_add, integral_add, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul]
    · exact hint h0c
    · exact (hint h1c).const_mul _
    · exact (hint h0c).add ((hint h1c).const_mul _)
    · exact (hint h2c).const_mul _
    · exact ((hint h0c).add ((hint h1c).const_mul _)).add ((hint h2c).const_mul _)
    · exact (hint h3c).const_mul _
    · exact (((hint h0c).add ((hint h1c).const_mul _)).add ((hint h2c).const_mul _)).add
        ((hint h3c).const_mul _)
    · exact (hint h4c).const_mul _
  -- the derivative of the quartic at zero
  have hpoly : HasDerivAt (fun ε : ℝ => (1 / 2) * (I0 + ε * I1 + ε ^ 2 * I2 + ε ^ 3 * I3 + ε ^ 4 * I4))
      ((1 / 2) * I1) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => ε * I1) I1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const I1
    have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * I2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const I2
    have h3 : HasDerivAt (fun ε : ℝ => ε ^ 3 * I3) 0 0 := by
      simpa using (hasDerivAt_pow 3 (0 : ℝ)).mul_const I3
    have h4 : HasDerivAt (fun ε : ℝ => ε ^ 4 * I4) 0 0 := by
      simpa using (hasDerivAt_pow 4 (0 : ℝ)).mul_const I4
    have := ((((hasDerivAt_const (0 : ℝ) I0).add h1).add h2).add h3).add h4
    have := this.const_mul (1 / 2)
    simpa using this
  -- identify the first-variation integral
  have hI1' : I1 = 2 * ∫ x in unitBox (n + 1), ∑ i, ∑ j, P.B (V i j x) (curvature A i j x) := by
    rw [hI1, ← integral_const_mul]
    refine setIntegral_congr_fun hcompact.measurableSet fun x _ => ?_
    simp only [hc1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [P.symm (curvature A i j x) (V i j x)]
    ring
  have hglobal := integral_sum_pairing_covariantVariation_yangMillsDirection P.toInvariantPairing A hA hper
  have hderiv : (1 / 2) * I1 = -2 * ∑ j, ∫ x in unitBox (n + 1), P.B (G j x) (G j x) := by
    rw [hI1', hglobal, ← integral_finsetSum _ fun j _ => hint (hpair (hG1 j).continuous (hG1 j).continuous)]
    ring
  rw [← hderiv]
  exact hpoly.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => hE ε)

/-- **The Yang--Mills direction never increases the energy.** -/
theorem deriv_yangMillsEnergy_direction_nonpos (P : SymmetricPairing 𝔤) (hpos : ∀ x, 0 ≤ P.B x x)
    (A : Connection (n + 1) 𝔤) (hA : ∀ i, ContDiff ℝ 3 (A i)) (hper : ∀ i, IsOnePeriodicBase (A i)) :
    deriv (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing
        (fun k y => A k y + ε • yangMillsDirection A k y)) 0 ≤ 0 := by
  rw [(hasDerivAt_yangMillsEnergy_direction P A hA hper).deriv]
  have : 0 ≤ ∑ j, ∫ x in unitBox (n + 1), P.B (yangMillsDirection A j x) (yangMillsDirection A j x) :=
    Finset.sum_nonneg fun j _ => setIntegral_nonneg isCompact_Icc.measurableSet fun x _ => hpos _
  linarith

section Audit

#print axioms hasDerivAt_yangMillsEnergy_direction
#print axioms deriv_yangMillsEnergy_direction_nonpos

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsDescent

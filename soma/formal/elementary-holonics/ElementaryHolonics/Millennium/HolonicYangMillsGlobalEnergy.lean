import ElementaryHolonics.Millennium.HolonicYangMillsEnergy
import ElementaryHolonics.Millennium.HolonicPeriodicBoxDivergence

/-!
# The global Yang--Mills energy identity on the torus

One-periodicity of a connection propagates through the differential, the bracket, the curvature,
the covariant derivative, and the Yang--Mills direction.  The local energy identity is then
integrated over the unit box: the divergence term vanishes by the periodic box law, and

```text
∫_box Σ_{ij} B((D_A G)_ij, F_ij) = −2 Σ_j ∫_box B(G_j, G_j).
```

With the first variation of curvature this is the statement that the Yang--Mills energy of a
periodic connection decreases along the flow exactly by twice the squared flow direction.
-/

noncomputable section

open Set MeasureTheory

namespace Soma.Holonics.Millennium.HolonicYangMillsGlobalEnergy

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-! ## Periodicity propagation -/

theorem differential_periodic {f : Base n → 𝔤} (hf : ContDiff ℝ 1 f) (hper : IsOnePeriodicBase f)
    (i : Fin n) : IsOnePeriodicBase (differential i f) := by
  intro x j
  unfold differential
  have hcomp : (fun y => f (y + Pi.single j 1)) = f := funext fun y => hper y j
  have h0 : HasFDerivAt (fun y : Base n => y + Pi.single j 1) (ContinuousLinearMap.id ℝ (Base n)) x :=
    (hasFDerivAt_id x).add_const _
  have h : HasFDerivAt (fun y => f (y + Pi.single j 1)) (fderiv ℝ f (x + Pi.single j 1)) x := by
    have := ((hf.differentiable (by norm_num) (x + Pi.single j 1)).hasFDerivAt).comp x h0
    exact this
  rw [hcomp] at h
  rw [h.fderiv]

omit [NormedAlgebra ℝ 𝔤] in
theorem bracket_periodic {f g : Base n → 𝔤} (hf : IsOnePeriodicBase f) (hg : IsOnePeriodicBase g) :
    IsOnePeriodicBase (fun x => bracket (f x) (g x)) := by
  intro x i
  simp only [hf x i, hg x i]

theorem curvature_periodic (A : Connection n 𝔤) (hA : ∀ i, ContDiff ℝ 1 (A i))
    (hper : ∀ i, IsOnePeriodicBase (A i)) (i j : Fin n) :
    IsOnePeriodicBase (curvature A i j) := by
  intro x k
  unfold curvature
  rw [differential_periodic (hA j) (hper j) i x k, differential_periodic (hA i) (hper i) j x k,
    hper i x k, hper j x k]

theorem covariantDerivative_periodic (A : Connection n 𝔤) (hper : ∀ i, IsOnePeriodicBase (A i))
    {X : Base n → 𝔤} (hX : ContDiff ℝ 1 X) (hXper : IsOnePeriodicBase X) (i : Fin n) :
    IsOnePeriodicBase (covariantDerivative A i X) := by
  intro x k
  unfold covariantDerivative
  rw [differential_periodic hX hXper i x k, hper i x k, hXper x k]

theorem yangMillsDirection_periodic (A : Connection n 𝔤) (hA : ∀ i, ContDiff ℝ 3 (A i))
    (hper : ∀ i, IsOnePeriodicBase (A i)) (j : Fin n) :
    IsOnePeriodicBase (yangMillsDirection A j) := by
  intro x k
  unfold yangMillsDirection
  refine Finset.sum_congr rfl fun l _ => ?_
  have hA1 : ∀ i, ContDiff ℝ 1 (A i) := fun i => (hA i).of_le (by norm_num)
  have hA2 : ∀ i, ContDiff ℝ 2 (A i) := fun i => (hA i).of_le (by norm_num)
  have hF2 : ContDiff ℝ 2 (curvature A l j) := contDiff_curvature A hA l j
  exact covariantDerivative_periodic A hper (hF2.of_le (by norm_num))
    (curvature_periodic A hA1 hper l j) l x k

/-! ## The integrated identity -/

/-- **The global Yang--Mills energy identity on the torus.** -/
theorem integral_sum_pairing_covariantVariation_yangMillsDirection (P : InvariantPairing 𝔤)
    (A : Connection (n + 1) 𝔤) (hA : ∀ i, ContDiff ℝ 3 (A i))
    (hper : ∀ i, IsOnePeriodicBase (A i)) :
    ∫ x in unitBox (n + 1), ∑ i, ∑ j,
        P.B (covariantVariation A (yangMillsDirection A) i j x) (curvature A i j x) =
      -2 * ∫ x in unitBox (n + 1), ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
  have hA1 : ∀ i, ContDiff ℝ 1 (A i) := fun i => (hA i).of_le (by norm_num)
  have hA2 : ∀ i, ContDiff ℝ 2 (A i) := fun i => (hA i).of_le (by norm_num)
  have hF2 : ∀ k l, ContDiff ℝ 2 (curvature A k l) := fun k l => contDiff_curvature A hA k l
  have hF1 : ∀ k l, ContDiff ℝ 1 (curvature A k l) := fun k l => (hF2 k l).of_le (by norm_num)
  have hG1 : ∀ j, ContDiff ℝ 1 (yangMillsDirection A j) := by
    intro j
    unfold yangMillsDirection
    exact ContDiff.sum fun k _ => contDiff_covariantDerivative A hA2 (hF2 k j) k
  -- the divergence field
  set V : Fin (n + 1) → Base (n + 1) → ℝ :=
    fun i x => ∑ j, P.B (yangMillsDirection A j x) (curvature A i j x) with hV
  have hterm1 : ∀ i j, ContDiff ℝ 1 fun x => P.B (yangMillsDirection A j x) (curvature A i j x) :=
    fun i j => (P.B.contDiff.comp (hG1 j)).clm_apply (hF1 i j)
  have hV1 : ∀ i, ContDiff ℝ 1 (V i) := by
    intro i
    show ContDiff ℝ 1 fun x => ∑ j, P.B (yangMillsDirection A j x) (curvature A i j x)
    exact ContDiff.sum fun j _ => hterm1 i j
  have hVper : ∀ i, IsOnePeriodicBase (V i) := by
    intro i x k
    simp only [hV]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [yangMillsDirection_periodic A hA hper j x k, curvature_periodic A hA1 hper i j x k]
  have hdivV := integral_divergence_unitBox_eq_zero V hV1 hVper
  -- the divergence of V is the double sum of differentials
  have hdivpt : ∀ x, (∑ i, fderiv ℝ (V i) x (Pi.single i 1)) =
      ∑ i, ∑ j, differential i (fun y => P.B (yangMillsDirection A j y) (curvature A i j y)) x := by
    intro x
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfun : V i = fun y => ∑ j, P.B (yangMillsDirection A j y) (curvature A i j y) := rfl
    have hd : HasFDerivAt (fun y => ∑ j, P.B (yangMillsDirection A j y) (curvature A i j y))
        (∑ j, fderiv ℝ (fun y => P.B (yangMillsDirection A j y) (curvature A i j y)) x) x := by
      have hsum := HasFDerivAt.sum (u := Finset.univ) fun j _ =>
        ((hterm1 i j).differentiable (by norm_num) x).hasFDerivAt
      have hfun2 : (fun y => ∑ j, P.B (yangMillsDirection A j y) (curvature A i j y)) =
          ∑ j, fun y => P.B (yangMillsDirection A j y) (curvature A i j y) := by
        funext z
        simp [Finset.sum_apply]
      rw [hfun2]
      exact hsum
    rw [hfun, hd.fderiv, sum_apply]
    rfl
  -- pointwise identity and integrability
  have hpt := sum_pairing_covariantVariation_yangMillsDirection P A hA
  have hcompact : IsCompact (unitBox (n + 1)) := isCompact_Icc
  have hcontS : Continuous fun x => ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
    apply continuous_finsetSum
    intro j _
    exact ((P.B.continuous.comp (hG1 j).continuous).clm_apply (hG1 j).continuous)
  have hcontD : Continuous fun x => ∑ i, fderiv ℝ (V i) x (Pi.single i 1) := by
    apply continuous_finsetSum
    intro i _
    exact ((hV1 i).continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hintS : IntegrableOn (fun x => ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x))
      (unitBox (n + 1)) := hcontS.continuousOn.integrableOn_compact hcompact
  have hintD : IntegrableOn (fun x => ∑ i, fderiv ℝ (V i) x (Pi.single i 1)) (unitBox (n + 1)) :=
    hcontD.continuousOn.integrableOn_compact hcompact
  have hcongr : ∀ x ∈ unitBox (n + 1), ∑ i, ∑ j,
      P.B (covariantVariation A (yangMillsDirection A) i j x) (curvature A i j x) =
      2 * (∑ i, fderiv ℝ (V i) x (Pi.single i 1)) -
        2 * ∑ j, P.B (yangMillsDirection A j x) (yangMillsDirection A j x) := by
    intro x _
    rw [hpt x, hdivpt x]
  rw [setIntegral_congr_fun hcompact.measurableSet hcongr, integral_sub (hintD.const_mul 2)
    (hintS.const_mul 2), integral_const_mul, integral_const_mul, hdivV]
  ring

section Audit

#print axioms integral_sum_pairing_covariantVariation_yangMillsDirection

end Audit

end Soma.Holonics.Millennium.HolonicYangMillsGlobalEnergy

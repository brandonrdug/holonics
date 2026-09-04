import ElementaryHolonics.Millennium.HolonicYangMillsHessian
import ElementaryHolonics.Millennium.HolonicCovariantDerivativeCovariance

/-!
# Gauge invariance of the first and second variations

A gauge acts affinely on connections and linearly on directions: `(A + εB)^g = A^g + ε B^g` with
`B^g = g B g⁻¹`.  Since the energy is gauge invariant, the energy along the transformed line
equals the energy along the original line for every `ε`; matching the Taylor coefficients returns
the invariance of the first variation and of the Hessian.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicYangMillsVariationInvariance

open Set MeasureTheory
open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
open Soma.Holonics.Millennium.HolonicYangMillsDescent
open Soma.Holonics.Millennium.HolonicYangMillsHessian
open Soma.Holonics.Millennium.HolonicGaugeCovariance
open Soma.Holonics.Millennium.HolonicYangMillsGaugeInvariance

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- The gauge action on a direction: conjugation. -/
def gaugeDirection (G : Gauge n 𝔤) (B : Connection n 𝔤) : Connection n 𝔤 :=
  fun i x => G.g x * B i x * G.ginv x

/-- **The gauge acts affinely along a line.** -/
theorem gaugeTransform_add_smul (G : Gauge n 𝔤) (A B : Connection n 𝔤) (ε : ℝ) :
    HolonicGaugeCovariance.gaugeTransform G (fun k y => A k y + ε • B k y) =
      fun k y => HolonicGaugeCovariance.gaugeTransform G A k y + ε • gaugeDirection G B k y := by
  funext k y
  unfold HolonicGaugeCovariance.gaugeTransform gaugeDirection
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  abel

theorem contDiff_gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (i : Fin n) :
    ContDiff ℝ 1 (HolonicGaugeCovariance.gaugeTransform G A i) := by
  have hg : ContDiff ℝ 1 G.g := G.smooth.of_le (by norm_num)
  have hgi : ContDiff ℝ 1 G.ginv := G.smooth_inv.of_le (by norm_num)
  have hAi : ContDiff ℝ 1 (A i) := (hA i).of_le (by norm_num)
  have hd : ContDiff ℝ 1 (differential i G.ginv) := contDiff_differential (m := 1) G.smooth_inv i
  exact ((hg.mul hAi).mul hgi).add (hg.mul hd)

theorem contDiff_gaugeDirection (G : Gauge n 𝔤) (B : Connection n 𝔤)
    (hB : ∀ i, ContDiff ℝ 2 (B i)) (i : Fin n) : ContDiff ℝ 1 (gaugeDirection G B i) := by
  have hg : ContDiff ℝ 1 G.g := G.smooth.of_le (by norm_num)
  have hgi : ContDiff ℝ 1 G.ginv := G.smooth_inv.of_le (by norm_num)
  exact (hg.mul ((hB i).of_le (by norm_num))).mul hgi

/-- **The energy along the transformed line equals the energy along the line.** -/
theorem yangMillsEnergy_gauge_line (P : SymmetricPairing 𝔤) (hP : IsAssociative P)
    (G : Gauge (n + 1) 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (hB : ∀ i, ContDiff ℝ 2 (B i)) (ε : ℝ) :
    yangMillsEnergy P.toInvariantPairing
        (fun k y => HolonicGaugeCovariance.gaugeTransform G A k y + ε • gaugeDirection G B k y) =
      yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y) := by
  rw [← gaugeTransform_add_smul]
  exact yangMillsEnergy_gaugeTransform P hP G _
    (fun i => (hA i).add ((hB i).const_smul ε))

/-- **Invariance of the first variation.** -/
theorem firstVariation_gaugeTransform (P : SymmetricPairing 𝔤) (hP : IsAssociative P)
    (G : Gauge (n + 1) 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (hB : ∀ i, ContDiff ℝ 2 (B i)) :
    firstVariation P (HolonicGaugeCovariance.gaugeTransform G A) (gaugeDirection G B) =
      firstVariation P A B := by
  have hfun : (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing
      (fun k y => HolonicGaugeCovariance.gaugeTransform G A k y + ε • gaugeDirection G B k y)) =
      fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y) :=
    funext (yangMillsEnergy_gauge_line P hP G A B hA hB)
  have h1 := (hasDerivAt_yangMillsEnergy P _ _ (contDiff_gaugeTransform G A hA)
    (contDiff_gaugeDirection G B hB) 0).deriv
  have h2 := (hasDerivAt_yangMillsEnergy P A B (fun i => (hA i).of_le (by norm_num))
    (fun i => (hB i).of_le (by norm_num)) 0).deriv
  rw [hfun] at h1
  simp only [mul_zero, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h1 h2
  linarith

/-- **Invariance of the Hessian.** -/
theorem hessian_gaugeTransform (P : SymmetricPairing 𝔤) (hP : IsAssociative P)
    (G : Gauge (n + 1) 𝔤) (A B : Connection (n + 1) 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (hB : ∀ i, ContDiff ℝ 2 (B i)) :
    hessian P (HolonicGaugeCovariance.gaugeTransform G A) (gaugeDirection G B) =
      hessian P A B := by
  have hfun : (fun ε : ℝ => yangMillsEnergy P.toInvariantPairing
      (fun k y => HolonicGaugeCovariance.gaugeTransform G A k y + ε • gaugeDirection G B k y)) =
      fun ε : ℝ => yangMillsEnergy P.toInvariantPairing (fun k y => A k y + ε • B k y) :=
    funext (yangMillsEnergy_gauge_line P hP G A B hA hB)
  have h1 := deriv_deriv_yangMillsEnergy P _ _ (contDiff_gaugeTransform G A hA)
    (contDiff_gaugeDirection G B hB)
  have h2 := deriv_deriv_yangMillsEnergy P A B (fun i => (hA i).of_le (by norm_num))
    (fun i => (hB i).of_le (by norm_num))
  rw [hfun] at h1
  rw [← h1, ← h2]

end Soma.Holonics.Millennium.HolonicYangMillsVariationInvariance

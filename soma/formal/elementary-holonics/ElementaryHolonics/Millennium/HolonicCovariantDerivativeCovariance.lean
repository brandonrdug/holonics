import ElementaryHolonics.Millennium.HolonicYangMillsGaugeInvariance

/-!
# Gauge covariance of the covariant derivative and of the Yang--Mills direction

Under a gauge `g`, a section conjugates as `X ↦ g X g⁻¹` and the connection as
`A ↦ g A g⁻¹ + g ∂g⁻¹`.  The covariant derivative of the conjugated section by the transformed
connection is the conjugate of the covariant derivative: `D^{A^g}(g X g⁻¹) = g (D^A X) g⁻¹`.
Applied to the curvature, the Yang--Mills direction conjugates as well:
`YM(A^g) = g · YM(A) · g⁻¹`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicCovariantDerivativeCovariance

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsFlow
open Soma.Holonics.Millennium.HolonicGaugeCovariance

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- **Covariance of the covariant derivative.** -/
theorem covariantDerivative_gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤)
    {X : Base n → 𝔤} (hX : ∀ x, DifferentiableAt ℝ X x) (i : Fin n) (x : Base n) :
    covariantDerivative (gaugeTransform G A) i (fun y => G.g y * X y * G.ginv y) x =
      G.g x * covariantDerivative A i X x * G.ginv x := by
  have hg := G.differentiableAt_g x
  have hgi := G.differentiableAt_ginv x
  have hgX : DifferentiableAt ℝ (fun y => G.g y * X y) x := hg.mul (hX x)
  have hd : differential i (fun y => G.g y * X y * G.ginv y) x =
      G.g x * X x * differential i G.ginv x +
        (G.g x * differential i X x + differential i G.g x * X x) * G.ginv x := by
    rw [differential_mul (f := fun y => G.g y * X y) (g := G.ginv) hgX hgi i,
      differential_mul (f := G.g) (g := X) hg (hX x) i]
  unfold covariantDerivative HolonicGaugeCovariance.gaugeTransform bracket
  rw [hd, G.differential_ginv i x]
  have h1 : ∀ t : 𝔤, G.ginv x * (G.g x * t) = t := fun t => by
    rw [← mul_assoc, G.inv_mul, one_mul]
  have h2 : ∀ t : 𝔤, G.g x * (G.ginv x * t) = t := fun t => by
    rw [← mul_assoc, G.mul_inv, one_mul]
  simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, mul_assoc, h1, h2, sub_eq_add_neg,
    neg_add]
  abel

/-- **Covariance of the Yang--Mills direction.** -/
theorem yangMillsDirection_gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (j : Fin n) (x : Base n) :
    yangMillsDirection (gaugeTransform G A) j x =
      G.g x * yangMillsDirection A j x * G.ginv x := by
  unfold yangMillsDirection
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  have hF : curvature (gaugeTransform G A) k j =
      fun y => G.g y * curvature A k j y * G.ginv y :=
    funext (curvature_gaugeTransform G A hA k j)
  rw [hF]
  exact covariantDerivative_gaugeTransform G A
    (fun y => differentiableAt_of_contDiff_one (contDiff_curvature A (m := 1) hA k j) y) k x

end Soma.Holonics.Millennium.HolonicCovariantDerivativeCovariance

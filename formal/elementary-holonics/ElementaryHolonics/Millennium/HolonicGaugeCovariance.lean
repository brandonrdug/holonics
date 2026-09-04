import ElementaryHolonics.Millennium.HolonicConnectionVariation

/-!
# Continuum gauge covariance: `F(A^g) = g F g⁻¹`

A gauge is a `C²` family of units `g` with its inverse `g⁻¹`.  The gauge transform of a
connection is `A^g_i = g A_i g⁻¹ + g ∂_i g⁻¹`, and its curvature is the conjugate of the
curvature: `F(A^g)_ij = g F_ij g⁻¹`.  The proof spends the Leibniz law, the symmetry of second
differentials of `g⁻¹`, and the differentiated unit law `∂ g⁻¹ = −g⁻¹ (∂ g) g⁻¹`.  This is the
continuum twin of the discrete face covariance already on the four-force carrier.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicGaugeCovariance

open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- A gauge: a `C²` family of units carried with its inverse. -/
structure Gauge (n : ℕ) (𝔤 : Type*) [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤] where
  g : Base n → 𝔤
  ginv : Base n → 𝔤
  mul_inv : ∀ x, g x * ginv x = 1
  inv_mul : ∀ x, ginv x * g x = 1
  smooth : ContDiff ℝ 2 g
  smooth_inv : ContDiff ℝ 2 ginv

/-- The gauge transform of a connection: `A^g_i = g A_i g⁻¹ + g ∂_i g⁻¹`. -/
def gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤) : Connection n 𝔤 :=
  fun i x => G.g x * A i x * G.ginv x + G.g x * differential i G.ginv x

namespace Gauge

variable (G : Gauge n 𝔤)

theorem differentiableAt_g (x : Base n) : DifferentiableAt ℝ G.g x :=
  differentiableAt_of_contDiff G.smooth x

theorem differentiableAt_ginv (x : Base n) : DifferentiableAt ℝ G.ginv x :=
  differentiableAt_of_contDiff G.smooth_inv x

/-- **The differentiated unit law**: `∂_i g⁻¹ = −g⁻¹ (∂_i g) g⁻¹`. -/
theorem differential_ginv (i : Fin n) (x : Base n) :
    differential i G.ginv x = -(G.ginv x * differential i G.g x * G.ginv x) := by
  have hone : (fun y => G.g y * G.ginv y) = fun _ => (1 : 𝔤) := funext G.mul_inv
  have hd : differential i (fun y => G.g y * G.ginv y) x = 0 := by
    rw [hone]
    simp [differential]
  rw [differential_mul (G.differentiableAt_g x) (G.differentiableAt_ginv x)] at hd
  -- g ∂ginv + ∂g ginv = 0 ⇒ ∂ginv = −ginv ∂g ginv
  have h1 : G.ginv x * (G.g x * differential i G.ginv x) = differential i G.ginv x := by
    rw [← mul_assoc, G.inv_mul, one_mul]
  have h2 : G.g x * differential i G.ginv x = -(differential i G.g x * G.ginv x) :=
    eq_neg_of_add_eq_zero_left hd
  calc differential i G.ginv x
      = G.ginv x * (G.g x * differential i G.ginv x) := h1.symm
    _ = G.ginv x * (-(differential i G.g x * G.ginv x)) := by rw [h2]
    _ = -(G.ginv x * differential i G.g x * G.ginv x) := by
        rw [mul_neg, mul_assoc]

end Gauge

/-- The differential of a gauge-transformed component, expanded. -/
theorem differential_gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (k l : Fin n) (x : Base n) :
    differential k (gaugeTransform G A l) x =
      differential k G.g x * A l x * G.ginv x + G.g x * differential k (A l) x * G.ginv x +
        G.g x * A l x * differential k G.ginv x +
        (differential k G.g x * differential l G.ginv x +
          G.g x * differential k (differential l G.ginv) x) := by
  have hg := G.differentiableAt_g x
  have hgi := G.differentiableAt_ginv x
  have hAl := differentiableAt_of_contDiff (hA l) x
  have hdgi : DifferentiableAt ℝ (differential l G.ginv) x :=
    differentiableAt_differential G.smooth_inv l x
  have hfun : gaugeTransform G A l = fun y =>
      (G.g y * A l y) * G.ginv y + G.g y * differential l G.ginv y := rfl
  have hd1 : differential k (fun y => (G.g y * A l y) * G.ginv y + G.g y * differential l G.ginv y) x =
      differential k (fun y => (G.g y * A l y) * G.ginv y) x +
        differential k (fun y => G.g y * differential l G.ginv y) x :=
    differential_add (f := fun y => (G.g y * A l y) * G.ginv y)
      (g := fun y => G.g y * differential l G.ginv y) ((hg.mul hAl).mul hgi) (hg.mul hdgi) k
  have hd2 : differential k (fun y => (G.g y * A l y) * G.ginv y) x =
      (G.g x * A l x) * differential k G.ginv x +
        differential k (fun y => G.g y * A l y) x * G.ginv x :=
    differential_mul (f := fun y => G.g y * A l y) (g := G.ginv) (hg.mul hAl) hgi k
  have hd3 : differential k (fun y => G.g y * A l y) x =
      G.g x * differential k (A l) x + differential k G.g x * A l x :=
    differential_mul (f := G.g) (g := A l) hg hAl k
  have hd4 : differential k (fun y => G.g y * differential l G.ginv y) x =
      G.g x * differential k (differential l G.ginv) x +
        differential k G.g x * differential l G.ginv x :=
    differential_mul (f := G.g) (g := differential l G.ginv) hg hdgi k
  rw [hfun, hd1, hd2, hd3, hd4]
  noncomm_ring

/-- **Gauge covariance of the curvature**: `F(A^g)_ij = g F_ij g⁻¹`. -/
theorem curvature_gaugeTransform (G : Gauge n 𝔤) (A : Connection n 𝔤)
    (hA : ∀ i, ContDiff ℝ 2 (A i)) (i j : Fin n) (x : Base n) :
    curvature (gaugeTransform G A) i j x = G.g x * curvature A i j x * G.ginv x := by
  have hsym := differential_differential_comm G.smooth_inv i j x
  have hQi := G.differential_ginv i x
  have hQj := G.differential_ginv j x
  have h1 : ∀ t : 𝔤, G.ginv x * (G.g x * t) = t := fun t => by
    rw [← mul_assoc, G.inv_mul, one_mul]
  have h2 : ∀ t : 𝔤, G.g x * (G.ginv x * t) = t := fun t => by
    rw [← mul_assoc, G.mul_inv, one_mul]
  unfold curvature
  rw [differential_gaugeTransform G A hA i j x, differential_gaugeTransform G A hA j i x, hsym]
  simp only [gaugeTransform, bracket]
  rw [hQi, hQj]
  simp only [mul_add, add_mul, mul_neg, neg_mul, neg_neg, mul_assoc, h1, h2, mul_one,
    one_mul, sub_eq_add_neg, neg_add]
  abel

section Audit

#print axioms Gauge.differential_ginv
#print axioms curvature_gaugeTransform

end Audit

end Soma.Holonics.Millennium.HolonicGaugeCovariance

import ElementaryHolonics.Millennium.HolonicConnectionCurvature
import ElementaryHolonics.Objects.Ratio.GaugeCalculus

/-!
# Curvature covariance under the core gauge action: `F(A^g) = g F g⁻¹`

A gauge is a `C²` family of units `g` with its inverse `g⁻¹`.  The gauge transform of a
connection is `A^g_i = g A_i g⁻¹ + g ∂_i g⁻¹`, and its curvature is the conjugate of the
curvature: `F(A^g)_ij = g F_ij g⁻¹`.  The proof spends the Leibniz law, the symmetry of second
differentials of `g⁻¹`, and the differentiated unit law `∂ g⁻¹ = −g⁻¹ (∂ g) g⁻¹`.  This is the
continuum twin of the discrete face covariance already on the four-force carrier.
The gauge and its action are owned by `Objects/Ratio/GaugeCalculus`; this research module retains
the continuum curvature covariance theorem.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicGaugeCovariance

open Soma.Holonics.Millennium.HolonicConnectionCurvature

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

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

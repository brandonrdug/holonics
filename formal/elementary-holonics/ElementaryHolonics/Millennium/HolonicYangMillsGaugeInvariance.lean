import ElementaryHolonics.Millennium.HolonicYangMillsDescent
import ElementaryHolonics.Millennium.HolonicGaugeCovariance

/-!
# Gauge invariance of the Yang--Mills energy

An associative symmetric pairing (`B (x * y) z = B x (y * z)`, the trace form) is invariant under
conjugation by any unit: `B (g x g⁻¹) (g y g⁻¹) = B x y`.  Since the curvature of a gauge
transform is the conjugated curvature, the Yang--Mills energy of a gauge transform equals the
energy of the original connection.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicYangMillsGaugeInvariance

open Set MeasureTheory
open Soma.Holonics.Millennium.HolonicConnectionCurvature
open Soma.Holonics.Millennium.HolonicConnectionVariation
open Soma.Holonics.Millennium.HolonicYangMillsEnergy
open Soma.Holonics.Millennium.HolonicPeriodicBoxDivergence
open Soma.Holonics.Millennium.HolonicYangMillsDescent
open Soma.Holonics.Millennium.HolonicGaugeCovariance

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- **Associativity of a pairing**: the trace law `B (x * y) z = B x (y * z)`. -/
def IsAssociative (P : SymmetricPairing 𝔤) : Prop :=
  ∀ x y z, P.B (x * y) z = P.B x (y * z)

/-- **Conjugation invariance.** An associative symmetric pairing is invariant under conjugation
by a unit. -/
theorem pairing_conj (P : SymmetricPairing 𝔤) (hP : IsAssociative P) {g ginv : 𝔤}
    (hig : ginv * g = 1) (x y : 𝔤) :
    P.B (g * x * ginv) (g * y * ginv) = P.B x y := by
  have h1 : P.B (g * x * ginv) (g * y * ginv) = P.B (g * x) (ginv * (g * y * ginv)) := hP _ _ _
  have h2 : ginv * (g * y * ginv) = y * ginv := by
    calc ginv * (g * y * ginv) = (ginv * g) * y * ginv := by simp only [mul_assoc]
      _ = y * ginv := by rw [hig, one_mul]
  have h3 : P.B (g * x) (y * ginv) = P.B g (x * (y * ginv)) := hP _ _ _
  have h4 : P.B g (x * (y * ginv)) = P.B (x * (y * ginv)) g := P.symm _ _
  have h5 : P.B (x * (y * ginv)) g = P.B x ((y * ginv) * g) := hP _ _ _
  have h6 : (y * ginv) * g = y := by rw [mul_assoc, hig, mul_one]
  rw [h1, h2, h3, h4, h5, h6]

/-- **Gauge invariance of the Yang--Mills energy.** -/
theorem yangMillsEnergy_gaugeTransform (P : SymmetricPairing 𝔤) (hP : IsAssociative P)
    (G : Gauge (n + 1) 𝔤) (A : Connection (n + 1) 𝔤) (hA : ∀ i, ContDiff ℝ 2 (A i)) :
    yangMillsEnergy P.toInvariantPairing (gaugeTransform G A) =
      yangMillsEnergy P.toInvariantPairing A := by
  unfold yangMillsEnergy
  have hfun : (fun x => ∑ i, ∑ j, P.B (curvature (gaugeTransform G A) i j x)
      (curvature (gaugeTransform G A) i j x)) =
      fun x => ∑ i, ∑ j, P.B (curvature A i j x) (curvature A i j x) := by
    funext x
    simp only [curvature_gaugeTransform G A hA, pairing_conj P hP (G.inv_mul x)]
  rw [hfun]

end Soma.Holonics.Millennium.HolonicYangMillsGaugeInvariance

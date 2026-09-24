import ElementaryHolonics.Millennium.NavierStokes
import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart

/-!
# Cartesian axial lift

This owner fixes the affine-radial Cartesian field used by the MFR source calculation.  It keeps
the Euclidean `Space` carrier and exposes the Cartesian formulas through its coordinate
equivalence. The actual derivative, divergence, normalized momentum and curl give the pressure
compatibility conditions on its scalar coefficients. Periodicity and finite energy are not
asserted for this local profile construction.
-/

noncomputable section

open ContDiff Set

namespace Soma.Holonics.Millennium.NavierStokesAxialLift

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

local notation "χ" => EuclideanSpace.equiv (Fin 3) ℝ

def axialLift (F W : ℝ → ℝ) (x : Space) : Space :=
  (χ).symm ![
    -(χ x 0) * deriv W (χ x 2) / 2 - (χ x 1) * F (χ x 2),
    -(χ x 1) * deriv W (χ x 2) / 2 + (χ x 0) * F (χ x 2),
    W (χ x 2)]

def axialA (F W : ℝ → ℝ) (alpha beta z : ℝ) : ℝ :=
  (deriv W z) ^ 2 / 4 - (F z) ^ 2 -
    (W z + beta * z) * deriv (deriv W) z / 2 -
    (alpha + beta) * deriv W z / 2

def axialC (F W : ℝ → ℝ) (alpha beta z : ℝ) : ℝ :=
  (W z + beta * z) * deriv F z +
    (alpha + beta - deriv W z) * F z

def axialB (F W : ℝ → ℝ) (alpha beta z : ℝ) : ℝ :=
  (W z + beta * z) * deriv W z + alpha * W z

theorem axialA_deriv (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (alpha beta : ℝ) :
    deriv (axialA F W alpha beta) = fun z ↦ -2 * F z * deriv F z -
      ((W z + beta * z) * deriv (deriv (deriv W)) z +
        (alpha + 2 * beta) * deriv (deriv W) z) / 2 := by
  have hW1 : ContDiff ℝ ∞ (deriv W) := by fun_prop
  have hW2 : ContDiff ℝ ∞ (deriv (deriv W)) := by fun_prop
  funext z
  have hf := (hF.differentiable (by simp) z).hasDerivAt
  have hw := (hW.differentiable (by simp) z).hasDerivAt
  have hw1 := (hW1.differentiable (by simp) z).hasDerivAt
  have hw2 := (hW2.differentiable (by simp) z).hasDerivAt
  have hgamma := hw.add ((hasDerivAt_id z).const_mul beta)
  have h := ((((hw1.pow 2).div_const 4).sub (hf.pow 2)).sub
    ((hgamma.mul hw2).div_const 2)).sub ((hw1.const_mul (alpha + beta)).div_const 2)
  convert h.deriv using 1 <;>
    first | rfl | (simp only [Pi.add_apply, Pi.mul_apply, id_eq] <;> ring)

theorem axialLift_coordinate (F W : ℝ → ℝ) (x : Space) (i : Fin 3) :
    axialLift F W x i =
      ![
        -(χ x 0) * deriv W (χ x 2) / 2 - (χ x 1) * F (χ x 2),
        -(χ x 1) * deriv W (χ x 2) / 2 + (χ x 0) * F (χ x 2),
        W (χ x 2)] i := by
  simp [axialLift]

theorem contDiff_infty_axialLift
    (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (axialLift F W) := by
  unfold axialLift
  let V : Space → (Fin 3 → ℝ) := fun x ↦ ![
    -(χ x 0) * deriv W (χ x 2) / 2 - (χ x 1) * F (χ x 2),
    -(χ x 1) * deriv W (χ x 2) / 2 + (χ x 0) * F (χ x 2),
    W (χ x 2)]
  have hV : ContDiff ℝ ∞ V := by
    rw [contDiff_pi]
    intro i
    fin_cases i
    · change ContDiff ℝ ∞ (fun x ↦
        -(χ x 0) * deriv W (χ x 2) / 2 - (χ x 1) * F (χ x 2))
      fun_prop
    · change ContDiff ℝ ∞ (fun x ↦
        -(χ x 1) * deriv W (χ x 2) / 2 + (χ x 0) * F (χ x 2))
      fun_prop
    · change ContDiff ℝ ∞ (fun x ↦ W (χ x 2))
      fun_prop
  change ContDiff ℝ ∞ ((χ).symm ∘ V)
  exact ((EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp hV)

theorem axialLift_third_coordinate
    (F W : ℝ → ℝ) (x : Space) :
    axialLift F W x 2 = W (χ x 2) := by
  rw [axialLift_coordinate]
  simp

theorem axialLift_horizontal_coordinates
    (F W : ℝ → ℝ) (x : Space) :
    axialLift F W x 0 =
        -(χ x 0) * deriv W (χ x 2) / 2 - (χ x 1) * F (χ x 2) ∧
      axialLift F W x 1 =
        -(χ x 1) * deriv W (χ x 2) / 2 + (χ x 0) * F (χ x 2) := by
  rw [axialLift_coordinate, axialLift_coordinate]
  simp

/-! These named scalar combinations are the exact coefficients in the normalized Euler residual;
their use does not assume that any pressure solves the resulting compatibility equation. -/

theorem axialA_coordinate (F W : ℝ → ℝ) (alpha beta z : ℝ) :
    axialA F W alpha beta z =
      (deriv W z) ^ 2 / 4 - (F z) ^ 2 -
        (W z + beta * z) * deriv (deriv W) z / 2 -
        (alpha + beta) * deriv W z / 2 := rfl

theorem axialC_coordinate (F W : ℝ → ℝ) (alpha beta z : ℝ) :
    axialC F W alpha beta z =
      (W z + beta * z) * deriv F z +
        (alpha + beta - deriv W z) * F z := rfl

theorem axialB_coordinate (F W : ℝ → ℝ) (alpha beta z : ℝ) :
    axialB F W alpha beta z = (W z + beta * z) * deriv W z + alpha * W z := rfl

def axialMeridionalV (W : ℝ → ℝ) : MeridionalProfile := fun p ↦ -deriv W p.2 / 2

def axialMeridionalOmega (F : ℝ → ℝ) : MeridionalProfile := fun p ↦ F p.2

def axialMeridionalW (W : ℝ → ℝ) : MeridionalProfile := fun p ↦ W p.2

theorem axialLift_eq_axisymmetricVelocity (F W : ℝ → ℝ) :
    axialLift F W = axisymmetricVelocity
      (axialMeridionalV W) (axialMeridionalOmega F) (axialMeridionalW W) := by
  funext x
  ext i
  fin_cases i <;>
    simp [axialLift, axisymmetricVelocity, assemble, axialMeridionalV,
      axialMeridionalOmega, axialMeridionalW, meridionalChart] <;> ring

theorem axialOnly_jet (f : ℝ → ℝ) (p : ℝ × ℝ) (f' : ℝ)
    (hf : HasDerivAt f f' p.2) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ f q.2) p ∧
      radialDerivative (fun q : ℝ × ℝ ↦ f q.2) p = 0 ∧
      axialDerivative (fun q : ℝ × ℝ ↦ f q.2) p = f' := by
  let projection : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hc := hf.hasFDerivAt.comp p projection.hasFDerivAt
  change HasFDerivAt (fun q : ℝ × ℝ ↦ f q.2) _ p at hc
  refine ⟨hc.differentiableAt, ?_, ?_⟩ <;>
    simp [radialDerivative, axialDerivative, hc.fderiv, projection]

theorem axialProfiles_jets (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (p : ℝ × ℝ) :
    (DifferentiableAt ℝ (axialMeridionalV W) p ∧
      radialDerivative (axialMeridionalV W) p = 0 ∧
      axialDerivative (axialMeridionalV W) p = -deriv (deriv W) p.2 / 2) ∧
    (DifferentiableAt ℝ (axialMeridionalOmega F) p ∧
      radialDerivative (axialMeridionalOmega F) p = 0 ∧
      axialDerivative (axialMeridionalOmega F) p = deriv F p.2) ∧
    (DifferentiableAt ℝ (axialMeridionalW W) p ∧
      radialDerivative (axialMeridionalW W) p = 0 ∧
      axialDerivative (axialMeridionalW W) p = deriv W p.2) := by
  have hdW : ContDiff ℝ ∞ (deriv W) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · exact axialOnly_jet (fun z ↦ -deriv W z / 2) p _
      (((hdW.differentiable (by simp) p.2).hasDerivAt.neg).div_const 2)
  · exact axialOnly_jet F p _ ((hF.differentiable (by simp) p.2).hasDerivAt)
  · exact axialOnly_jet W p _ ((hW.differentiable (by simp) p.2).hasDerivAt)

theorem divergence_axialLift (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (x : Space) : divergence (axialLift F W) x = 0 := by
  obtain ⟨hV, hO, hZ⟩ := axialProfiles_jets F W hF hW (meridionalChart x)
  rw [axialLift_eq_axisymmetricVelocity,
    divergence_axisymmetricVelocity _ _ _ x hV.1 hO.1 hZ.1, hV.2.1, hZ.2.2]
  simp [axialMeridionalV]
  ring

/-- The previously named scalar residuals are derived from the actual Cartesian field. -/
theorem normalizedMomentum_axialLift (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hW : ContDiff ℝ ∞ W) (alpha beta : ℝ) (x : Space) :
    fderiv ℝ (axialLift F W) x (axialLift F W x) + beta • fderiv ℝ (axialLift F W) x x
      + alpha • axialLift F W x =
      assemble (x 0 * axialA F W alpha beta (x 2) - x 1 * axialC F W alpha beta (x 2))
        (x 1 * axialA F W alpha beta (x 2) + x 0 * axialC F W alpha beta (x 2))
        (axialB F W alpha beta (x 2)) := by
  obtain ⟨hV, hO, hZ⟩ := axialProfiles_jets F W hF hW (meridionalChart x)
  rw [axialLift_eq_axisymmetricVelocity,
    normalizedMomentum_axisymmetricVelocity alpha beta _ _ _ x hV.1 hO.1 hZ.1]
  simp only [radialMomentum, swirlMomentum, axialMomentum, hV.2.1, hV.2.2,
    hO.2.1, hO.2.2, hZ.2.1, hZ.2.2]
  ext i
  fin_cases i <;>
    simp [assemble, axialMeridionalV, axialMeridionalOmega, axialMeridionalW,
      meridionalChart, axialA, axialC, axialB] <;> ring

def axialResidual (F W : ℝ → ℝ) (alpha beta : ℝ) : InitialVelocity := fun x ↦
  fderiv ℝ (axialLift F W) x (axialLift F W x) + beta • fderiv ℝ (axialLift F W) x x
    + alpha • axialLift F W x

theorem axialResidual_eq_axisymmetricVelocity (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hW : ContDiff ℝ ∞ W) (alpha beta : ℝ) :
    axialResidual F W alpha beta = axisymmetricVelocity
      (fun p ↦ axialA F W alpha beta p.2) (fun p ↦ axialC F W alpha beta p.2)
      (fun p ↦ axialB F W alpha beta p.2) := by
  funext x
  exact normalizedMomentum_axialLift F W hF hW alpha beta x

theorem vorticityAt_axialResidual (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hW : ContDiff ℝ ∞ W) (alpha beta : ℝ) (x : Space) :
    vorticityAt (axialResidual F W alpha beta) x =
      assemble
        (-x 1 * deriv (axialA F W alpha beta) (x 2) - x 0 * deriv (axialC F W alpha beta) (x 2))
        (x 0 * deriv (axialA F W alpha beta) (x 2) - x 1 * deriv (axialC F W alpha beta) (x 2))
        (2 * axialC F W alpha beta (x 2)) := by
  have hA : ContDiff ℝ ∞ (axialA F W alpha beta) := by unfold axialA; fun_prop
  have hC : ContDiff ℝ ∞ (axialC F W alpha beta) := by unfold axialC; fun_prop
  have hB : ContDiff ℝ ∞ (axialB F W alpha beta) := by unfold axialB; fun_prop
  have jA := axialOnly_jet (axialA F W alpha beta) (meridionalChart x) _
    ((hA.differentiable (by simp) _).hasDerivAt)
  have jC := axialOnly_jet (axialC F W alpha beta) (meridionalChart x) _
    ((hC.differentiable (by simp) _).hasDerivAt)
  have jB := axialOnly_jet (axialB F W alpha beta) (meridionalChart x) _
    ((hB.differentiable (by simp) _).hasDerivAt)
  rw [axialResidual_eq_axisymmetricVelocity F W hF hW alpha beta,
    vorticityAt_axisymmetricVelocity _ _ _ x jA.1 jC.1 jB.1,
    jB.2.1, jA.2.2, jC.2.2, jC.2.1]
  simp [meridionalChart, mul_sub, neg_mul]

theorem vorticityAt_eq_zero_of_pressure_balance (R : InitialVelocity) (pressure : Space → ℝ)
    (hp : ContDiff ℝ 2 pressure) (hbalance : ∀ x, R x + gradient pressure x = 0) (x : Space) :
    vorticityAt R x = 0 := by
  have hfield : R = fun x ↦ -gradient pressure x :=
    funext fun x ↦ eq_neg_of_add_eq_zero_left (hbalance x)
  rw [hfield]
  change derivativeCurlLinearMap (fderiv ℝ (fun x ↦ -gradient pressure x) x) = 0
  rw [fderiv_fun_neg, map_neg]
  change -vorticityAt (gradient pressure) x = 0
  rw [curl_gradient_eq_zero pressure x hp.contDiffAt, neg_zero]

/-- Smooth pressure forces both the swirl equation and the radial/axial compatibility current.
The swirl condition is recovered by curl at the axis; the radial derivative is read off-axis. -/
theorem pressure_balance_implies_compatibility (F W : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hW : ContDiff ℝ ∞ W) (alpha beta : ℝ) (pressure : Space → ℝ)
    (hp : ContDiff ℝ 2 pressure)
    (hbalance : ∀ x, axialResidual F W alpha beta x + gradient pressure x = 0) :
    ∀ z, axialC F W alpha beta z = 0 ∧ deriv (axialA F W alpha beta) z = 0 := by
  intro z
  have haxis := vorticityAt_eq_zero_of_pressure_balance _ pressure hp hbalance (assemble 0 0 z)
  have hoff := vorticityAt_eq_zero_of_pressure_balance _ pressure hp hbalance (assemble 1 0 z)
  rw [vorticityAt_axialResidual F W hF hW alpha beta] at haxis hoff
  have hc := congrArg (fun v : Space ↦ v 2) haxis
  have ha := congrArg (fun v : Space ↦ v 1) hoff
  simp at hc ha
  exact ⟨by linarith, ha⟩

#print axioms contDiff_infty_axialLift
#print axioms axialLift_third_coordinate
#print axioms axialLift_horizontal_coordinates
#print axioms divergence_axialLift
#print axioms normalizedMomentum_axialLift
#print axioms vorticityAt_axialResidual
#print axioms pressure_balance_implies_compatibility

end Soma.Holonics.Millennium.NavierStokesAxialLift

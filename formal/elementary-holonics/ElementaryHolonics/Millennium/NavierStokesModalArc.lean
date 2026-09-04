import ElementaryHolonics.Millennium.NavierStokesModalRiccati

/-!
# The mode's arc is turned only by the nonlinear source: dissipation draws no area

Each vorticity mode `ω̂_k(τ) ∈ ℂ³` draws a parametric arc.  Its energy `E_k = Σ_c |ω̂_{k,c}|²`
changes by the real part of `⟨ω̂_k, ω̂_k'⟩`, the grip; the area it sweeps changes by the imaginary
part, the slip (`TABLET_THE_TURN`: aim and cross are the two faces of one contact, and neither is a
scalar summary of the other).  Along Sol's per-mode equation the Stokes term is a real multiple of
the mode, so it contributes nothing to the areal velocity: dissipation shrinks the arc but does
not turn it.  The areal velocity is exactly `Σ_c Im(conj ω̂_{k,c} · N_{k,c})`, the slip of the
nonlinear source, and it is paid by the same shell-step cost as the grip.

This is the first degree of arc calculus on the modes.  Nothing here integrates the area.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesModalArc

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesModalRiccati

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The areal velocity of the mode arc at a derivative value `d`: `Σ_c Im(conj ω̂_c · d_c)`. -/
def arealVelocity (w d : ComplexVector) : ℝ :=
  ∑ component : Fin 3, (conj (w component) * d component).im

/-- The grip of the mode arc at a derivative value `d`: `Σ_c Re(conj ω̂_c · d_c)`. -/
def gripVelocity (w d : ComplexVector) : ℝ :=
  ∑ component : Fin 3, (conj (w component) * d component).re

/-- A real multiple of the mode draws no area. -/
theorem arealVelocity_real_smul (w : ComplexVector) (r : ℝ) :
    arealVelocity w (fun component ↦ (r : ℂ) * w component) = 0 := by
  unfold arealVelocity
  apply Finset.sum_eq_zero
  intro component _
  rw [← mul_assoc, mul_comm (conj (w component)) (r : ℂ), mul_assoc,
    Complex.conj_mul' (w component), ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

theorem arealVelocity_add (w d e : ComplexVector) :
    arealVelocity w (fun component ↦ d component + e component) =
      arealVelocity w d + arealVelocity w e := by
  unfold arealVelocity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro component _
  rw [mul_add, Complex.add_im]

/-- **Dissipation draws no area.**  Along the per-mode equation the areal velocity of the mode arc
is the slip of the nonlinear source alone. -/
theorem arealVelocity_eq_nonlinear (t : Ioo 0 T) (k : SpatialFrequency) :
    arealVelocity (vorticityModeCurve (velocity := velocity) k t.1)
        (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
            frequencyCurlMultiplier k (velocityMode velocity k t.1) +
          vorticityNonlinearMode solution t k) =
      arealVelocity (vorticityModeCurve (velocity := velocity) k t.1)
        (vorticityNonlinearMode solution t k) := by
  have hsplit : (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
        frequencyCurlMultiplier k (velocityMode velocity k t.1) +
      vorticityNonlinearMode solution t k) =
      fun component ↦ ((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) *
          vorticityModeCurve (velocity := velocity) k t.1 component +
        vorticityNonlinearMode solution t k component := by
    funext component
    simp [vorticityModeCurve, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsplit, arealVelocity_add, arealVelocity_real_smul, zero_add]

/-- The slip is paid by the same shell-step cost as the grip. -/
theorem abs_arealVelocity_le (hnu : 0 ≤ nu) (t : Ioo 0 T) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) :
    |arealVelocity (vorticityModeCurve (velocity := velocity) k t.1)
        (vorticityNonlinearMode solution t k)| ≤
      complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
        (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * feedBound solution t radius) := by
  set w := vorticityModeCurve (velocity := velocity) k t.1 with hw
  set N := vorticityNonlinearMode solution t k with hN
  have hterm : ∀ component : Fin 3,
      |(conj (w component) * N component).im| ≤ ‖w component‖ * complexVectorL1 N := by
    intro component
    refine (Complex.abs_im_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold complexVectorL1
    fin_cases component <;> simp <;> linarith [norm_nonneg (N 0), norm_nonneg (N 1), norm_nonneg (N 2)]
  unfold arealVelocity
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun component _ ↦ hterm component).trans ?_
  rw [← Finset.sum_mul, ← complexVectorL1_eq_sum w]
  exact mul_le_mul_of_nonneg_left (complexVectorL1_vorticityNonlinearMode_le solution hnu t hk)
    (complexVectorL1_nonneg w)

section Audit

#print axioms arealVelocity_real_smul
#print axioms arealVelocity_eq_nonlinear
#print axioms abs_arealVelocity_le

end Audit

end Soma.Holonics.Millennium.NavierStokesModalArc

import ElementaryHolonics.Millennium.NavierStokesCoordinateH3FullEstimate
import ElementaryHolonics.Millennium.NavierStokesTorusVorticity

/-!
# The coordinate continuation law reads the actual torus Jacobian receiver

**[proved-derived]** The source owner is an admitted smooth periodic solution.  At one strict
interior time its spatial Fréchet derivative is continuous and one-periodic, hence descends to a
continuous field on the genuine spatial torus.  Its continuous-map norm is the actual Jacobian
receiver used here; it is not an arbitrary scalar envelope and it retains the complete derivative
field as its reconstruction population.

The returned consequence is the pointwise Euclidean Jacobian bound and its direct insertion into
the checked forty-face coordinate `H³` production inequality.  A later annular Hodge theorem may
bound this receiver with its honest kernel constant.  No low/middle/high scalar testimony or
continuation conclusion is assumed in this owner.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FullEstimate
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-- The complete spatial velocity derivative on one strict interior face, descended through the
actual periodic quotient. -/
def openPeriodicTorusJacobianSlice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, Space →L[ℝ] Space) :=
  periodicTorusLift
    (fderiv ℝ (fun x ↦ velocity x t.1))
    ((openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).fderiv_right
      (m := 0) (by simp)).continuous
    (fderiv_isOnePeriodic (fun x ↦ velocity x t.1)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩))

/-- Pulling the torus Jacobian receiver back along the quotient returns the literal Euclidean
Fréchet derivative. -/
@[simp]
theorem openPeriodicTorusJacobianSlice_projection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (x : Space) :
    openPeriodicTorusJacobianSlice solution t (euclideanToSpatialTorus x) =
      fderiv ℝ (fun y ↦ velocity y t.1) x := by
  unfold openPeriodicTorusJacobianSlice
  exact periodicTorusLift_projection _ _ _ x

/-- The actual time-indexed Jacobian receiver.  Outside the strict interior it is totalized to
zero; all continuation consequences below open it only with the addressed interior receipt. -/
def coordinateJacobianReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) T then
    ‖openPeriodicTorusJacobianSlice solution ⟨t, ht⟩‖
  else 0

/-- On a strict interior face the totalized receiver is exactly the genuine-torus supremum norm. -/
theorem coordinateJacobianReceiver_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateJacobianReceiver solution t =
      ‖openPeriodicTorusJacobianSlice solution ⟨t, ht⟩‖ := by
  simp [coordinateJacobianReceiver, ht]

/-- The actual receiver is nonnegative at every time, including its exterior totalization. -/
theorem coordinateJacobianReceiver_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) :
    0 ≤ coordinateJacobianReceiver solution t := by
  unfold coordinateJacobianReceiver
  split_ifs
  · positivity
  · exact le_rfl

/-- Every Euclidean spatial receiver is bounded by the norm of the complete descended Jacobian
field. -/
theorem norm_fderiv_le_coordinateJacobianReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    ‖fderiv ℝ (fun y ↦ velocity y t) x‖ ≤
      coordinateJacobianReceiver solution t := by
  rw [coordinateJacobianReceiver_eq solution ht]
  rw [← openPeriodicTorusJacobianSlice_projection solution ⟨t, ht⟩ x]
  exact (openPeriodicTorusJacobianSlice solution ⟨t, ht⟩).norm_coe_le_norm
    (euclideanToSpatialTorus x)

/-- The checked forty-face unforced production law now consumes the actual Jacobian receiver,
with no arbitrary envelope function left in this passage. -/
theorem openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_actualJacobian
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (hnu : 0 ≤ nu) :
    coordinateH3TimeWork velocity t ≤
      10986 * coordinateJacobianReceiver solution t *
        coordinateLogH3Receiver velocity t := by
  exact openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_envelope
    solution ht hnu (fun x _hx ↦
      norm_fderiv_le_coordinateJacobianReceiver solution ht x)

section Audit

#print axioms openPeriodicTorusJacobianSlice_projection
#print axioms coordinateJacobianReceiver_nonneg
#print axioms norm_fderiv_le_coordinateJacobianReceiver
#print axioms openPeriodicSolutionOn_unforced_coordinateH3TimeWork_le_actualJacobian

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver

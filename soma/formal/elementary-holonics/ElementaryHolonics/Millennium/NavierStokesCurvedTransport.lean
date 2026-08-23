import Mathlib.Tactic
import ElementaryHolonics.Millennium.NavierStokesMaterialPolygon

/-!
# Kelvin, Gauss--Bonnet, and receiver-indexed Einstein coupling on the fluid polygon

This module turns three adjacent subjects into explicit interfaces over the material-polygon owner.

* `MaterialCirculationBalance` retains pressure, viscous, and forcing returns separately.  Pressure
  cancels around the closed boundary, and zero viscous/forcing return gives the Kelvin conclusion.
* `PolygonGaussBonnet` retains a bulk curvature population and every boundary turn.  The
  bulk-plus-boundary law makes total angle excess equal total curvature.
* `EinsteinFluidDynamics` couples a curvature occurrence to a stress-energy occurrence only after
  a receiver selects comparable scalar faces.  The source is constituted from the actual velocity
  and pressure, and its divergence return is required to vanish.

The interfaces make the named laws available for subsequent analytic and geometric construction:
later modules can derive the circulation balance from the PDE, realize the curvature ledger from a
metric connection, and instantiate the receiver equation on a Lorentzian tensor carrier.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCurvedTransport

open Set
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesMaterialPolygon

/-! ## 1. Kelvin as the zero-return fibre of the material circulation balance -/

/-- The complete finite circulation balance between two material snapshots.  Pressure is retained
as an edge population; viscosity and forcing are separate returned faces. -/
structure MaterialCirculationBalance {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) where
  pressure : PressureField
  viscousReturn : ℝ → ℝ → ℝ
  forcingReturn : ℝ → ℝ → ℝ
  balance : ∀ s t, 0 ≤ s → 0 ≤ t →
    polygon.velocityCirculation t - polygon.velocityCirculation s =
      (∑ i, polygon.pressureIncrementAt pressure t i) +
        viscousReturn s t + forcingReturn s t

/-- The pressure population disappears from the circulation balance by exact cyclic cancellation;
the viscous and forcing ports remain visible. -/
theorem MaterialCirculationBalance.change_eq_viscous_add_forcing
    {extra : ℕ} {velocity : VelocityField} {polygon : MaterialPolygon extra velocity}
    (law : MaterialCirculationBalance polygon) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    polygon.velocityCirculation t - polygon.velocityCirculation s =
      law.viscousReturn s t + law.forcingReturn s t := by
  rw [law.balance s t hs ht, polygon.sum_pressureIncrementAt_eq_zero]
  simp

/-- **Finite material Kelvin theorem.**  On the zero-viscous-return and zero-forcing-return fibre,
the polygonal circulation is conserved between every two nonnegative receiver times. -/
theorem MaterialCirculationBalance.kelvin
    {extra : ℕ} {velocity : VelocityField} {polygon : MaterialPolygon extra velocity}
    (law : MaterialCirculationBalance polygon)
    (hviscous : ∀ s t, 0 ≤ s → 0 ≤ t → law.viscousReturn s t = 0)
    (hforcing : ∀ s t, 0 ≤ s → 0 ≤ t → law.forcingReturn s t = 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    polygon.velocityCirculation t = polygon.velocityCirculation s := by
  have hchange := law.change_eq_viscous_add_forcing hs ht
  rw [hviscous s t hs ht, hforcing s t hs ht] at hchange
  have hzero : polygon.velocityCirculation t - polygon.velocityCirculation s = 0 := by
    simpa using hchange
  exact sub_eq_zero.mp hzero

/-! ## 2. Gauss--Bonnet as conservation between bulk curvature and boundary turn -/

/-- A finite Gauss--Bonnet presentation for a polygonal disk.  The curvature carrier `Cell` keeps
the bulk population addressed instead of pre-summing it. -/
structure PolygonGaussBonnet (extra : ℕ) (Cell : Type*) [Fintype Cell] where
  interior : PolygonIndex extra → ℝ
  exterior : PolygonIndex extra → ℝ
  halfTurn : ℝ
  curvature : Cell → ℝ
  supplementary : ∀ i, interior i + exterior i = halfTurn
  bulk_add_boundary : (∑ c, curvature c) + ∑ i, exterior i = 2 * halfTurn

/-- The sum of interior angles is the flat polygon budget plus total bulk curvature. -/
theorem PolygonGaussBonnet.sum_interior_eq_flat_add_curvature
    {extra : ℕ} {Cell : Type*} [Fintype Cell]
    (ledger : PolygonGaussBonnet extra Cell) :
    ∑ i, ledger.interior i =
      (extra + 1 : ℕ) * ledger.halfTurn + ∑ c, ledger.curvature c := by
  have hsupp : ∑ i, (ledger.interior i + ledger.exterior i) =
      ∑ _i : PolygonIndex extra, ledger.halfTurn := by
    apply Finset.sum_congr rfl
    intro i _
    exact ledger.supplementary i
  have hcard : ∑ _i : PolygonIndex extra, ledger.halfTurn =
      (extra + 3 : ℕ) * ledger.halfTurn := by
    simp
  rw [Finset.sum_add_distrib] at hsupp
  rw [hcard] at hsupp
  norm_num at hsupp ⊢
  linarith [ledger.bulk_add_boundary]

/-- The receiver-visible angle excess above the flat `(n - 2)` budget. -/
def PolygonGaussBonnet.angleExcess
    {extra : ℕ} {Cell : Type*} [Fintype Cell]
    (ledger : PolygonGaussBonnet extra Cell) : ℝ :=
  (∑ i, ledger.interior i) - (extra + 1 : ℕ) * ledger.halfTurn

/-- **Finite Gauss--Bonnet return.**  Total angle excess is exactly the sum of the retained bulk
curvature population. -/
theorem PolygonGaussBonnet.angleExcess_eq_sum_curvature
    {extra : ℕ} {Cell : Type*} [Fintype Cell]
    (ledger : PolygonGaussBonnet extra Cell) :
    ledger.angleExcess = ∑ c, ledger.curvature c := by
  rw [PolygonGaussBonnet.angleExcess,
    ledger.sum_interior_eq_flat_add_curvature]
  ring

/-- The flat turn ledger is the zero-bulk-curvature fibre of the Gauss--Bonnet presentation. -/
def gaussBonnetZeroOfTurnLedger
    (ledger : PolygonTurnLedger extra) : PolygonGaussBonnet extra (Fin 0) where
  interior := ledger.interior
  exterior := ledger.exterior
  halfTurn := ledger.halfTurn
  curvature := Fin.elim0
  supplementary := ledger.supplementary
  bulk_add_boundary := by simpa using ledger.windingOne

/-- The zero-curvature fibre has zero angle excess. -/
theorem PolygonTurnLedger.toGaussBonnetZero_angleExcess
    (ledger : PolygonTurnLedger extra) :
    (gaussBonnetZeroOfTurnLedger ledger).angleExcess = 0 := by
  rw [PolygonGaussBonnet.angleExcess_eq_sum_curvature]
  simp

/-! ## 3. Einstein dynamics as a fluid-constituted, receiver-indexed field equation -/

/-- A receiver-indexed Einstein/fluid dynamics interface.  `stressLaw` constructs the source from
the actual local velocity and pressure.  Curvature and stress-energy may have different internal
carriers; a receiver supplies the two comparable faces. -/
structure EinsteinFluidDynamics
    (velocity : VelocityField) (pressure : PressureField)
    (Curvature Stress Receiver Flux : Type*) [Zero Flux] where
  curvatureAt : Space → ℝ → Curvature
  stressLaw : Space → ℝ → Space → ℝ → Stress
  curvatureFace : Receiver → Curvature → ℝ
  stressFace : Receiver → Stress → ℝ
  stressDivergence : (Space → ℝ → Stress) → Space → ℝ → Flux
  coupling : ℝ
  fieldEquation : ∀ receiver x t,
    curvatureFace receiver (curvatureAt x t) =
      coupling * stressFace receiver (stressLaw x t (velocity x t) (pressure x t))
  sourceConserved : ∀ x t,
    stressDivergence (fun y τ ↦ stressLaw y τ (velocity y τ) (pressure y τ)) x t = 0

/-- The stress-energy occurrence constituted by the fluid fields. -/
def EinsteinFluidDynamics.stressAt
    {velocity : VelocityField} {pressure : PressureField}
    {Curvature Stress Receiver Flux : Type*} [Zero Flux]
    (dynamics : EinsteinFluidDynamics velocity pressure Curvature Stress Receiver Flux)
    (x : Space) (t : ℝ) : Stress :=
  dynamics.stressLaw x t (velocity x t) (pressure x t)

/-- The fluid-constituted stress-energy occurrence satisfies the declared conservation return. -/
theorem EinsteinFluidDynamics.stressAt_conserved
    {velocity : VelocityField} {pressure : PressureField}
    {Curvature Stress Receiver Flux : Type*} [Zero Flux]
    (dynamics : EinsteinFluidDynamics velocity pressure Curvature Stress Receiver Flux)
    (x : Space) (t : ℝ) :
    dynamics.stressDivergence dynamics.stressAt x t = 0 := by
  exact dynamics.sourceConserved x t

/-- Select the project's depth-two arc/differential coupling for the field equation. -/
def EinsteinFluidDynamics.UsesRefineForkCoupling
    {velocity : VelocityField} {pressure : PressureField}
    {Curvature Stress Receiver Flux : Type*} [Zero Flux]
    (dynamics : EinsteinFluidDynamics velocity pressure Curvature Stress Receiver Flux)
    (arc differential : ℝ) : Prop :=
  dynamics.coupling = refineForkCoupling 2 0 arc differential

/-- **Receiver equation at the holonic depth-two coupling.**  Every receiver reads curvature as
`4 * (C / r)` times its fluid stress-energy face. -/
theorem EinsteinFluidDynamics.receiverEquation_fourArcOverDifferential
    {velocity : VelocityField} {pressure : PressureField}
    {Curvature Stress Receiver Flux : Type*} [Zero Flux]
    (dynamics : EinsteinFluidDynamics velocity pressure Curvature Stress Receiver Flux)
    {arc differential : ℝ} (hcoupling : dynamics.UsesRefineForkCoupling arc differential)
    (receiver : Receiver) (x : Space) (t : ℝ) :
    dynamics.curvatureFace receiver (dynamics.curvatureAt x t) =
      (4 * (arc / differential)) * dynamics.stressFace receiver (dynamics.stressAt x t) := by
  rw [dynamics.fieldEquation receiver x t, hcoupling,
    refineForkCoupling_two_zero]
  rfl

section Audit

#print axioms MaterialCirculationBalance.change_eq_viscous_add_forcing
#print axioms MaterialCirculationBalance.kelvin
#print axioms PolygonGaussBonnet.angleExcess_eq_sum_curvature
#print axioms PolygonTurnLedger.toGaussBonnetZero_angleExcess
#print axioms EinsteinFluidDynamics.stressAt_conserved
#print axioms EinsteinFluidDynamics.receiverEquation_fourArcOverDifferential

end Audit

end Soma.Holonics.Millennium.NavierStokesCurvedTransport

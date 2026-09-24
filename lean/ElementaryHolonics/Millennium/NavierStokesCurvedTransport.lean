import Mathlib.Tactic
import Mathlib.LinearAlgebra.BilinearMap
import ElementaryHolonics.Millennium.NavierStokesMaterialPolygon

/-!
# Kelvin, Gauss--Bonnet, and receiver-indexed Einstein coupling on the fluid polygon

This module turns three adjacent subjects into explicit interfaces over the material-polygon owner.

* `MaterialCirculationBalance` is a finite balance certificate retaining pressure, viscous, and
  forcing returns separately.  Pressure cancels around the closed boundary, and zero
  viscous/forcing return gives conditional polygonal Kelvin constancy.
* `PolygonGaussBonnet` retains a bulk curvature population and every boundary turn;
  `TriangulatedGaussBonnetLedger` derives the bulk-plus-boundary theorem from local triangle budgets
  and an Euler incidence return.
* `EinsteinFluidDynamics` is the coupling interface through which the actual velocity and pressure
  constitute a covariant bilinear source field.  Its supplied Einstein tensor, covariant
  divergence, field equation, Bianchi return, and metric compatibility derive source conservation;
  declared receivers read both the field equation and conservation.

The interfaces make the named laws available for subsequent analytic and geometric construction.
The next construction derives the circulation balance from the PDE, realizes the curvature ledger
from a metric connection, and instantiates the Einstein coupling on a Lorentzian tensor carrier.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCurvedTransport

open Set
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesMaterialPolygon

/-! ## 1. Kelvin as the zero-return fibre of the material circulation balance -/

/-- A finite circulation-balance certificate between two material snapshots of one admitted smooth
Navier--Stokes solution.  Its pressure is retained as an edge population; viscosity and forcing
are separate returned faces.  The analytic PDE-to-balance construction is the next owner. -/
structure MaterialCirculationBalance
    {extra : ℕ} {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra nu initial force velocity pressure) where
  viscousReturn : ℝ → ℝ → ℝ
  forcingReturn : ℝ → ℝ → ℝ
  balance : ∀ s t, 0 ≤ s → 0 ≤ t →
    body.polygon.symmetricVelocityCirculation t - body.polygon.symmetricVelocityCirculation s =
      (∑ i, body.polygon.pressureIncrementAt pressure t i) +
        viscousReturn s t + forcingReturn s t

/-- The pressure population disappears from the circulation balance by exact cyclic cancellation;
the viscous and forcing ports remain visible. -/
theorem MaterialCirculationBalance.change_eq_viscous_add_forcing
    {extra : ℕ} {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {body : SolutionMaterialPolygon extra nu initial force velocity pressure}
    (law : MaterialCirculationBalance body) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    body.polygon.symmetricVelocityCirculation t - body.polygon.symmetricVelocityCirculation s =
      law.viscousReturn s t + law.forcingReturn s t := by
  rw [law.balance s t hs ht, body.polygon.sum_pressureIncrementAt_eq_zero]
  simp

/-- **Conditional polygonal Kelvin constancy.**  On the zero-viscous-return and
zero-forcing-return fibre of the certified balance, polygonal circulation is conserved between
every two nonnegative receiver times. -/
theorem MaterialCirculationBalance.kelvin
    {extra : ℕ} {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {body : SolutionMaterialPolygon extra nu initial force velocity pressure}
    (law : MaterialCirculationBalance body)
    (hviscous : ∀ s t, 0 ≤ s → 0 ≤ t → law.viscousReturn s t = 0)
    (hforcing : ∀ s t, 0 ≤ s → 0 ≤ t → law.forcingReturn s t = 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    body.polygon.symmetricVelocityCirculation t = body.polygon.symmetricVelocityCirculation s := by
  have hchange := law.change_eq_viscous_add_forcing hs ht
  rw [hviscous s t hs ht, hforcing s t hs ht] at hchange
  have hzero : body.polygon.symmetricVelocityCirculation t -
      body.polygon.symmetricVelocityCirculation s = 0 := by
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

/-- A triangulated bulk/boundary ledger from which Gauss--Bonnet is derived.  Each triangular face
supplies its angle budget, while `combinatorialCount` is the Euler incidence return of the chosen
triangulation. -/
structure TriangulatedGaussBonnetLedger
    (Interior Boundary Face : Type*) [Fintype Interior] [Fintype Boundary] [Fintype Face] where
  cornerAngle : Sum Interior Boundary → Face → ℝ
  eulerCharacteristic : ℤ
  faceAngleBudget : ∀ face, ∑ vertex, cornerAngle vertex face = Real.pi
  combinatorialCount :
    (2 : ℝ) * (eulerCharacteristic : ℝ) =
      2 * (Fintype.card Interior : ℝ) + (Fintype.card Boundary : ℝ) -
        (Fintype.card Face : ℝ)

/-- Curvature retained at one interior vertex. -/
def TriangulatedGaussBonnetLedger.bulkCurvature
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) (i : Interior) : ℝ :=
  2 * Real.pi - ∑ face, ledger.cornerAngle (.inl i) face

/-- Turning retained at one boundary vertex. -/
def TriangulatedGaussBonnetLedger.boundaryTurn
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) (b : Boundary) : ℝ :=
  Real.pi - ∑ face, ledger.cornerAngle (.inr b) face

/-- **Discrete Gauss--Bonnet from local face budgets and Euler incidence.** -/
theorem TriangulatedGaussBonnetLedger.gaussBonnet
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) :
    (∑ i, ledger.bulkCurvature i) + ∑ b, ledger.boundaryTurn b =
      2 * Real.pi * (ledger.eulerCharacteristic : ℝ) := by
  have hcorner :
      (∑ vertex : Sum Interior Boundary, ∑ face, ledger.cornerAngle vertex face) =
        (Fintype.card Face : ℝ) * Real.pi := by
    rw [Finset.sum_comm]
    calc
      (∑ face, ∑ vertex, ledger.cornerAngle vertex face) =
          ∑ _face : Face, Real.pi := by
        apply Finset.sum_congr rfl
        intro face _
        exact ledger.faceAngleBudget face
      _ = (Fintype.card Face : ℝ) * Real.pi := by simp
  simp only [TriangulatedGaussBonnetLedger.bulkCurvature,
    TriangulatedGaussBonnetLedger.boundaryTurn, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.sum_sum_type] at hcorner
  linear_combination - hcorner - Real.pi * ledger.combinatorialCount

/-! ## 3. Einstein dynamics as curvature-to-fluid conservation transport -/

/-- A space-time event on the current fluid chart. -/
abbrev FluidEvent := Space × ℝ

/-- A bilinear tensor field over fluid events, with an abstract space-time tangent fibre `V`. -/
abbrev TensorField (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  FluidEvent → LinearMap.BilinForm ℝ V

/-- A covector field over the same events, the natural target of divergence for covariant
bilinear tensor fields before any metric musical isomorphism raises the remaining index. -/
abbrev CovectorField (V : Type*) [AddCommGroup V] [Module ℝ V] :=
  FluidEvent → Module.Dual ℝ V

/-- A receiver-indexed Einstein/fluid dynamics interface.  `stressLaw` constitutes a covariant
bilinear source field from the actual local velocity and pressure.  The metric, Einstein tensor,
covariant divergence, field equation, contracted Bianchi return, and metric compatibility are
supplied ports; conservation of the fluid source is derived from their interaction below.  A
Lorentzian metric/connection/curvature realization can instantiate those ports without changing
the conservation transport. -/
structure EinsteinFluidDynamics
    (velocity : VelocityField) (pressure : PressureField)
    (V Receiver : Type*) [AddCommGroup V] [Module ℝ V] where
  metric : TensorField V
  einstein : TensorField V
  stressLaw : Space → ℝ → Space → ℝ → LinearMap.BilinForm ℝ V
  covDiv : TensorField V →ₗ[ℝ] CovectorField V
  tensorReceiver : Receiver → TensorField V →ₗ[ℝ] ℝ
  conservationReceiver : Receiver → CovectorField V →ₗ[ℝ] ℝ
  cosmologicalConstant : ℝ
  coupling : ℝ
  coupling_ne_zero : coupling ≠ 0
  fieldEquation :
    einstein + cosmologicalConstant • metric =
      coupling • (fun event ↦
        stressLaw event.1 event.2 (velocity event.1 event.2) (pressure event.1 event.2))
  contractedBianchi : covDiv einstein = 0
  metricCompatible : covDiv metric = 0

/-- The tensor-field source occurrence constituted by the fluid fields.  In a Lorentzian fluid
realization this is the stress-energy field. -/
def EinsteinFluidDynamics.stressEnergy
    {velocity : VelocityField} {pressure : PressureField}
    {V Receiver : Type*} [AddCommGroup V] [Module ℝ V]
    (dynamics : EinsteinFluidDynamics velocity pressure V Receiver) : TensorField V :=
  fun event ↦ dynamics.stressLaw event.1 event.2
    (velocity event.1 event.2) (pressure event.1 event.2)

/-- **Einstein-to-fluid conservation transport.**  The field equation, contracted Bianchi return,
metric compatibility, and nonzero coupling force covariant conservation of the constituted source
field. -/
theorem EinsteinFluidDynamics.stressEnergy_conserved
    {velocity : VelocityField} {pressure : PressureField}
    {V Receiver : Type*} [AddCommGroup V] [Module ℝ V]
    (dynamics : EinsteinFluidDynamics velocity pressure V Receiver) :
    dynamics.covDiv dynamics.stressEnergy = 0 := by
  have h := congrArg (fun tensor ↦ dynamics.covDiv tensor) dynamics.fieldEquation
  change dynamics.covDiv
      (dynamics.einstein + dynamics.cosmologicalConstant • dynamics.metric) =
    dynamics.covDiv (dynamics.coupling • dynamics.stressEnergy) at h
  simp only [map_add, LinearMap.map_smul_of_tower, dynamics.contractedBianchi,
    dynamics.metricCompatible, smul_zero, add_zero] at h
  rw [← inv_smul_smul₀ dynamics.coupling_ne_zero
    (dynamics.covDiv dynamics.stressEnergy)]
  rw [← h, smul_zero]

/-- Every declared current receiver reads the derived conservation return as zero. -/
theorem EinsteinFluidDynamics.everyReceiver_reads_conservation
    {velocity : VelocityField} {pressure : PressureField}
    {V Receiver : Type*} [AddCommGroup V] [Module ℝ V]
    (dynamics : EinsteinFluidDynamics velocity pressure V Receiver) (receiver : Receiver) :
    dynamics.conservationReceiver receiver (dynamics.covDiv dynamics.stressEnergy) = 0 := by
  rw [dynamics.stressEnergy_conserved]
  exact map_zero (dynamics.conservationReceiver receiver)

/-- Select the project's depth-two arc/differential coupling for the tensor field equation. -/
def EinsteinFluidDynamics.UsesRefineForkCoupling
    {velocity : VelocityField} {pressure : PressureField}
    {V Receiver : Type*} [AddCommGroup V] [Module ℝ V]
    (dynamics : EinsteinFluidDynamics velocity pressure V Receiver)
    (arc differential : ℝ) : Prop :=
  dynamics.coupling = refineForkCoupling 2 0 arc differential

/-- **Conditional receiver equation at the holonic depth-two coupling.**  Once `hcoupling`
identifies the coupling with `refineForkCoupling 2 0 C r`, every linear tensor receiver reads the
Einstein side as `4 * (C / r)` times its fluid source face. -/
theorem EinsteinFluidDynamics.receiverEquation_fourArcOverDifferential
    {velocity : VelocityField} {pressure : PressureField}
    {V Receiver : Type*} [AddCommGroup V] [Module ℝ V]
    (dynamics : EinsteinFluidDynamics velocity pressure V Receiver)
    {arc differential : ℝ} (hdifferential : differential ≠ 0)
    (hcoupling : dynamics.UsesRefineForkCoupling arc differential)
    (receiver : Receiver) :
    dynamics.tensorReceiver receiver
        (dynamics.einstein + dynamics.cosmologicalConstant • dynamics.metric) =
      (4 * (arc / differential)) *
        dynamics.tensorReceiver receiver dynamics.stressEnergy := by
  rw [dynamics.fieldEquation, map_smul, hcoupling,
    refineForkCoupling_two_zero arc differential hdifferential]
  rfl

section Audit

#print axioms MaterialCirculationBalance.change_eq_viscous_add_forcing
#print axioms MaterialCirculationBalance.kelvin
#print axioms PolygonGaussBonnet.angleExcess_eq_sum_curvature
#print axioms PolygonTurnLedger.toGaussBonnetZero_angleExcess
#print axioms TriangulatedGaussBonnetLedger.gaussBonnet
#print axioms EinsteinFluidDynamics.stressEnergy_conserved
#print axioms EinsteinFluidDynamics.everyReceiver_reads_conservation
#print axioms EinsteinFluidDynamics.receiverEquation_fourArcOverDifferential

end Audit

end Soma.Holonics.Millennium.NavierStokesCurvedTransport

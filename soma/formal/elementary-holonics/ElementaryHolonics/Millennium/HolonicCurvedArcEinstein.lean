import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Millennium.NavierStokesCurvedTransport

/-!
# Curved arc transport, gyro-return, Gauss--Bonnet holonomy, and an Einstein falsifier

Position radius, curvature radius, arc length, phase, differential, and refinement index are kept
as different types.  An oriented arc is an addressed occurrence carrying an invertible connection
transport.  The relative return of two transports is trivial exactly when they agree.  A gyrogroup
gyration is then a literal curvature-return instance, with the additive group proved flat.

The existing triangulated Gauss--Bonnet ledger is converted into a connection word on the phase
line: its holonomy is translation by `2πχ`.  On the Einstein side the depth-two arc/differential
formula remains valid at a selected receiver calibration, while a new falsifier proves that no
nonzero coupling can equal that ratio for every arc.  A concrete nondegenerate Minkowski plane and
flat vacuum instantiate the existing Bianchi/metric-compatible conservation interface.

Truth status: `[proved-derived] [formal-checked]` for every theorem.  The universal identification
of a physical Einstein coupling with `4 arc / differential` is refuted; only the already stated
local calibrated equation survives.
-/

namespace Soma.Holonics.Millennium.HolonicCurvedArcEinstein

open Soma.Holonics
open Soma.Holonics.Millennium.HolonicComposition
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesMaterialPolygon
open Soma.Holonics.Millennium.NavierStokesCurvedTransport
open scoped BigOperators

noncomputable section

/-! ## Separately typed geometric ports -/

structure PositionRadius where value : ℝ
structure CurvatureRadius where value : ℝ
structure ArcLength where value : ℝ
structure ArcPhase where value : ℝ
structure ArcDifferential where value : ℝ
structure RefinementIndex where value : ℕ

/-- One receiver-addressed bundle of the six typed arc ports. -/
structure ArcReceiverDatum where
  positionRadius : PositionRadius
  curvatureRadius : CurvatureRadius
  arcLength : ArcLength
  phase : ArcPhase
  differential : ArcDifferential
  refinement : RefinementIndex

/-! ## Addressed arcs and connection return -/

/-- An oriented geometric occurrence with its connection transport. -/
structure OrientedArc (Position Fibre : Type*) where
  source : Position
  target : Position
  length : ArcLength
  phase : ArcPhase
  transport : Equiv.Perm Fibre

def orientedArcPassage (Position Fibre : Type*) : AddressedPassage Position Position where
  Occurrence := OrientedArc Position Fibre
  source := OrientedArc.source
  target := OrientedArc.target

def orientedArcConnection (Position Fibre : Type*) :
    AddressedConnection Fibre (orientedArcPassage Position Fibre) :=
  OrientedArc.transport

theorem orientedArc_connectionTransport {Position Fibre : Type*}
    (arc : OrientedArc Position Fibre) :
    connectionTransport (orientedArcConnection Position Fibre) arc = arc.transport := rfl

/-- The return obtained by following the right route and reversing the left route. -/
def routeCurvatureReturn {Fibre : Type*} (left right : Equiv.Perm Fibre) : Equiv.Perm Fibre :=
  routeComparisonReturn left right

theorem routeCurvatureReturn_eq_one_iff {Fibre : Type*} (left right : Equiv.Perm Fibre) :
    routeCurvatureReturn left right = 1 ↔ right = left :=
  routeComparisonReturn_eq_one_iff left right

/-! ## Gyrotransport is a connection-return instance -/

def gyrationCurvatureReturn {G : Type*} [Gyrogroup G] (a b : G) : Equiv.Perm G :=
  Gyrogroup.gyr a b

theorem additive_gyrationCurvatureReturn_is_flat
    (G : Type*) [AddCommGroup G] (a b : G) :
    gyrationCurvatureReturn a b = 1 := by
  ext x
  simp [gyrationCurvatureReturn]

theorem gyrationCurvatureReturn_nontrivial_of_moves
    {G : Type*} [Gyrogroup G] {a b x : G} (hmove : Gyrogroup.gyr a b x ≠ x) :
    gyrationCurvatureReturn a b ≠ 1 := by
  intro h
  apply hmove
  have hx := DFunLike.congr_fun h x
  simpa [gyrationCurvatureReturn] using hx

/-! ## Discrete Gauss--Bonnet as phase holonomy -/

/-- Translation of the receiver's oriented phase line. -/
def phaseShift (angle : ℝ) : Equiv.Perm ℝ :=
  additiveTranslation angle

@[simp] theorem phaseShift_apply (angle x : ℝ) : phaseShift angle x = x + angle := rfl

theorem phaseShift_mul (a b : ℝ) : phaseShift a * phaseShift b = phaseShift (a + b) :=
  additiveTranslation_mul a b

theorem parallelTransport_phaseShift (angles : List ℝ) :
    parallelTransport (angles.map phaseShift) = phaseShift angles.sum :=
  parallelTransport_additiveTranslation angles

/-- The ordered phase word retains every bulk-curvature and boundary-turn occurrence. -/
def gaussBonnetAngleWord
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) : List ℝ :=
  (Finset.univ.toList.map ledger.bulkCurvature) ++
    (Finset.univ.toList.map ledger.boundaryTurn)

theorem gaussBonnetAngleWord_sum
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) :
    (gaussBonnetAngleWord ledger).sum =
      (∑ i, ledger.bulkCurvature i) + ∑ b, ledger.boundaryTurn b := by
  simp [gaussBonnetAngleWord]

/-- Polygonal Gauss--Bonnet is exactly the holonomy of the retained phase-transport word. -/
theorem gaussBonnet_is_phaseHolonomy
    {Interior Boundary Face : Type*} [Fintype Interior] [Fintype Boundary] [Fintype Face]
    (ledger : TriangulatedGaussBonnetLedger Interior Boundary Face) :
    parallelTransport ((gaussBonnetAngleWord ledger).map phaseShift) =
      phaseShift (2 * Real.pi * (ledger.eulerCharacteristic : ℝ)) := by
  rw [parallelTransport_phaseShift, gaussBonnetAngleWord_sum, ledger.gaussBonnet]

/-! ## The typed arc/differential equation and its falsifier -/

def typedRefineForkCoupling (forks : ℕ) (scale : RefinementIndex)
    (arc : ArcLength) (differential : ArcDifferential) : ℝ :=
  refineForkCoupling forks scale.value arc.value differential.value

theorem typedRefineForkCoupling_two_zero (arc : ArcLength) (differential : ArcDifferential)
    (hdiff : differential.value ≠ 0) :
    typedRefineForkCoupling 2 ⟨0⟩ arc differential =
      4 * (arc.value / differential.value) :=
  refineForkCoupling_two_zero arc.value differential.value hdiff

/-- A nonzero Einstein coupling cannot be the depth-two ratio at every arc.  Thus the ratio can be
a selected local receiver calibration, but it is not a universal field constant. -/
theorem nonzeroCoupling_is_not_universalArcRatio (coupling : ℝ) (hcoupling : coupling ≠ 0) :
    ¬ ∀ arc : ArcLength,
      coupling = typedRefineForkCoupling 2 ⟨0⟩ arc ⟨1⟩ := by
  intro h
  have hzero := h ⟨0⟩
  norm_num [typedRefineForkCoupling, refineForkCoupling] at hzero
  exact hcoupling hzero

/-! ## An explicit Lorentzian control realizing the conservation interface -/

abbrev LorentzPlane := ℝ × ℝ

/-- The nondegenerate signature `(-,+)` Minkowski form. -/
def minkowskiMetric : LinearMap.BilinForm ℝ LorentzPlane :=
  LinearMap.mk₂ ℝ (fun u v ↦ -(u.1 * v.1) + u.2 * v.2)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)
    (by intros; simp; ring)

theorem minkowskiMetric_time : minkowskiMetric (1, 0) (1, 0) = -1 := by
  norm_num [minkowskiMetric]

theorem minkowskiMetric_space : minkowskiMetric (0, 1) (0, 1) = 1 := by
  norm_num [minkowskiMetric]

theorem minkowskiMetric_isSymm : minkowskiMetric.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff, LinearMap.isSymm_def]
  intro x y
  simp [minkowskiMetric]
  ring

theorem minkowskiMetric_nondegenerate (x : LorentzPlane)
    (hzero : ∀ y, minkowskiMetric x y = 0) : x = 0 := by
  have ht := hzero (1, 0)
  have hs := hzero (0, 1)
  apply Prod.ext
  · simpa [minkowskiMetric] using neg_eq_zero.mp (by simpa [minkowskiMetric] using ht)
  · simpa [minkowskiMetric] using hs

/-- A concrete flat vacuum: the metric is Minkowski, the connection divergence is zero, and the
Einstein and stress-energy fields vanish.  All compatibility laws are constructed, not postulated
at the theorem which derives conservation. -/
def flatLorentzVacuumDynamics (velocity : VelocityField) (pressure : PressureField) :
    EinsteinFluidDynamics velocity pressure LorentzPlane Unit where
  metric := fun _ ↦ minkowskiMetric
  einstein := 0
  stressLaw := fun _ _ _ _ ↦ 0
  covDiv := 0
  tensorReceiver := fun _ ↦ 0
  conservationReceiver := fun _ ↦ 0
  cosmologicalConstant := 0
  coupling := 1
  coupling_ne_zero := one_ne_zero
  fieldEquation := by
    simp
    rfl
  contractedBianchi := rfl
  metricCompatible := rfl

theorem flatLorentzVacuumDynamics_conserves
    (velocity : VelocityField) (pressure : PressureField) :
    (flatLorentzVacuumDynamics velocity pressure).covDiv
      (flatLorentzVacuumDynamics velocity pressure).stressEnergy = 0 :=
  (flatLorentzVacuumDynamics velocity pressure).stressEnergy_conserved

end

end Soma.Holonics.Millennium.HolonicCurvedArcEinstein

section Audit
open Soma.Holonics.Millennium.HolonicCurvedArcEinstein
#print axioms orientedArc_connectionTransport
#print axioms routeCurvatureReturn_eq_one_iff
#print axioms additive_gyrationCurvatureReturn_is_flat
#print axioms gyrationCurvatureReturn_nontrivial_of_moves
#print axioms gaussBonnet_is_phaseHolonomy
#print axioms typedRefineForkCoupling_two_zero
#print axioms nonzeroCoupling_is_not_universalArcRatio
#print axioms minkowskiMetric_isSymm
#print axioms minkowskiMetric_nondegenerate
#print axioms flatLorentzVacuumDynamics_conserves
end Audit

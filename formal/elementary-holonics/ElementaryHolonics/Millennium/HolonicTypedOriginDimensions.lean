import ElementaryHolonics.Foundation.TransportLift
import ElementaryHolonics.Millennium.Ellipse

/-!
# Typed-origin dimensional transport

**[proved-derived]** Conventional dimensional analysis records one time exponent.  This file
refines that receiver shadow by retaining two addressed causal occurrences: the source-time factor
and the receiver-time factor.  The conventional `(length, mass, time)` dimension is then an exact
additive receiver which sums the two time exponents.

Thus the typed source of `length / time^2` is

`length ⊗ sourceTime⁻¹ ⊗ receiverTime⁻¹`,

and the ordinary exponent `-2` is its returned conventional coordinate.  The receiver is not
injective: the nonzero difference `sourceTime - receiverTime` lies in its kernel, and every
inhabited dimensional preimage fibre is therefore a translate of that retained kernel.

The same calculus returns `[cosmological constant] = length⁻²` and checks the complete typed
Einstein equation:

`[G/c⁴] + [stress--energy] = [curvature] = [cosmological constant · metric]`.

The last section distinguishes tensor multiplication from exterior area.  A repeated covector has
a nonzero tensor square but zero self-wedge; an oriented event-area requires two independent causal
directions.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTypedOriginDimensions

open Soma.Holonics.Foundation
open Soma.Holonics.Millennium

/-! ## Addressed source and receiver dimensions -/

inductive TimeOrigin where
  | source
  | receiver
  deriving DecidableEq, Repr

instance : Fintype TimeOrigin :=
  Fintype.ofList [.source, .receiver] (by
    intro origin
    cases origin <;> simp)

inductive OriginAxis where
  | length
  | mass
  | time : TimeOrigin → OriginAxis
  deriving DecidableEq, Repr

instance : Fintype OriginAxis :=
  Fintype.ofList [.length, .mass, .time .source, .time .receiver] (by
    intro axis
    cases axis with
    | length => simp
    | mass => simp
    | time origin => cases origin <;> simp)

/-- An exact physical dimension before the conventional receiver identifies causal origins. -/
abbrev OriginDim := OriginAxis → ℤ

def axisDim (axis : OriginAxis) : OriginDim :=
  fun candidate ↦ if candidate = axis then 1 else 0

def lengthDim : OriginDim := axisDim .length
def massDim : OriginDim := axisDim .mass
def sourceTimeDim : OriginDim := axisDim (.time .source)
def receiverTimeDim : OriginDim := axisDim (.time .receiver)

/-- The conventional `(length, mass, time)` receiver.  It sums the two addressed time exponents;
it does not identify the source and receiver occurrences. -/
def symmetrizeDimension : OriginDim →+ Ellipse.Dim where
  toFun dimension :=
    (dimension .length, dimension .mass,
      dimension (.time .source) + dimension (.time .receiver))
  map_zero' := by
    rfl
  map_add' left right := by
    ext <;> simp
    ring

def sourceSpeedDim : OriginDim := lengthDim - sourceTimeDim
def receiverSpeedDim : OriginDim := lengthDim - receiverTimeDim

/-- The two factors of `c²` keep their distinct causal provenance until a receiver folds them. -/
def speedSquaredDim : OriginDim := sourceSpeedDim + receiverSpeedDim

def forceDim : OriginDim :=
  massDim + lengthDim - sourceTimeDim - receiverTimeDim

def gravitationalConstantDim : OriginDim :=
  3 • lengthDim - massDim - sourceTimeDim - receiverTimeDim

def speedFourthDim : OriginDim := 2 • speedSquaredDim

/-- The dimension of the Einstein coupling `G/c⁴`; dimensionless factors such as `8π` do not
change it. -/
def einsteinCouplingDim : OriginDim :=
  gravitationalConstantDim - speedFourthDim

/-- Stress--energy as force per oriented area. -/
def stressEnergyDim : OriginDim :=
  massDim - lengthDim - sourceTimeDim - receiverTimeDim

def curvatureDim : OriginDim := (-2 : ℤ) • lengthDim

/-- In the convention where the metric components are dimensionless, the cosmological constant is
an inverse-area curvature coefficient. -/
def cosmologicalConstantDim : OriginDim := curvatureDim

def metricDim : OriginDim := 0

/-! ## Spatial primal/dual cell-measure dimensions -/

/-- Oriented spatial area as two independent length factors. -/
def areaDim : OriginDim := 2 • lengthDim

/-- Oriented spatial three-volume as three independent length factors. -/
def spatialVolumeDim : OriginDim := 3 • lengthDim

def primalEdgeMeasureDim : OriginDim := lengthDim
def dualEdgeMeasureDim : OriginDim := spatialVolumeDim
def primalFaceMeasureDim : OriginDim := areaDim
def dualFaceMeasureDim : OriginDim := areaDim

/-- The coordinate dimension of the four-dimensional geometric Hodge weight on one-cells. -/
def edgeHodgeWeightDim : OriginDim := dualEdgeMeasureDim - primalEdgeMeasureDim

/-- The coordinate dimension of the four-dimensional geometric Hodge weight on two-cells. -/
def faceHodgeWeightDim : OriginDim := dualFaceMeasureDim - primalFaceMeasureDim

theorem edgeHodgeWeightDim_eq_areaDim : edgeHodgeWeightDim = areaDim := by
  funext axis
  simp [edgeHodgeWeightDim, dualEdgeMeasureDim, primalEdgeMeasureDim,
    spatialVolumeDim, areaDim]
  ring

theorem faceHodgeWeightDim_eq_zero : faceHodgeWeightDim = 0 := by
  simp [faceHodgeWeightDim, dualFaceMeasureDim, primalFaceMeasureDim]

theorem sourceSpeedDim_ne_receiverSpeedDim :
    sourceSpeedDim ≠ receiverSpeedDim := by
  intro equal
  have coordinate := congrFun equal (.time .source)
  simp [sourceSpeedDim, receiverSpeedDim, sourceTimeDim, receiverTimeDim,
    lengthDim, axisDim] at coordinate

theorem symmetrize_sourceSpeedDim :
    symmetrizeDimension sourceSpeedDim = Ellipse.dimC := by
  simp [symmetrizeDimension, sourceSpeedDim, sourceTimeDim, lengthDim,
    axisDim, Ellipse.dimC]

theorem symmetrize_receiverSpeedDim :
    symmetrizeDimension receiverSpeedDim = Ellipse.dimC := by
  simp [symmetrizeDimension, receiverSpeedDim, receiverTimeDim, lengthDim,
    axisDim, Ellipse.dimC]

theorem speedSquared_eq_source_add_receiver :
    speedSquaredDim = sourceSpeedDim + receiverSpeedDim := rfl

theorem symmetrize_speedSquaredDim :
    symmetrizeDimension speedSquaredDim = Ellipse.dsmul 2 Ellipse.dimC := by
  simp [symmetrizeDimension, speedSquaredDim, sourceSpeedDim, receiverSpeedDim,
    sourceTimeDim, receiverTimeDim, lengthDim, axisDim, Ellipse.dsmul, Ellipse.dimC]

/-! ## The conventional receiver has a retained causal-origin fibre -/

def timeOriginDifference : OriginDim := sourceTimeDim - receiverTimeDim

theorem timeOriginDifference_ne_zero : timeOriginDifference ≠ 0 := by
  intro equal
  have coordinate := congrFun equal (.time .source)
  simp [timeOriginDifference, sourceTimeDim, receiverTimeDim, axisDim] at coordinate

theorem symmetrize_timeOriginDifference :
    symmetrizeDimension timeOriginDifference = 0 := by
  simp [symmetrizeDimension, timeOriginDifference, sourceTimeDim, receiverTimeDim,
    axisDim]

theorem timeOriginDifference_mem_kernel :
    timeOriginDifference ∈ symmetrizeDimension.ker := by
  rw [AddMonoidHom.mem_ker]
  exact symmetrize_timeOriginDifference

theorem symmetrizeDimension_not_injective :
    ¬ Function.Injective symmetrizeDimension := by
  intro injective
  apply timeOriginDifference_ne_zero
  apply injective
  simpa using symmetrize_timeOriginDifference

abbrev DimensionFibre (reading : Ellipse.Dim) :=
  Lift.PreimageFibre symmetrizeDimension reading

def dimensionFibreEquivKernel {reading : Ellipse.Dim}
    (base : DimensionFibre reading) :
    DimensionFibre reading ≃ symmetrizeDimension.ker :=
  Lift.fibreEquivKernel symmetrizeDimension base

/-! ## Exact Einstein and cosmological-constant dimensions -/

theorem symmetrize_gravitationalConstantDim :
    symmetrizeDimension gravitationalConstantDim = Ellipse.dimG := by
  simp [symmetrizeDimension, gravitationalConstantDim, lengthDim, massDim,
    sourceTimeDim, receiverTimeDim, axisDim, Ellipse.dimG]

theorem symmetrize_forceDim :
    symmetrizeDimension forceDim = Ellipse.dimForce := by
  simp [symmetrizeDimension, forceDim, lengthDim, massDim, sourceTimeDim,
    receiverTimeDim, axisDim, Ellipse.dimForce]

theorem einsteinCouplingDim_eq_neg_forceDim :
    einsteinCouplingDim = -forceDim := by
  funext axis
  cases axis with
  | length => simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
      speedSquaredDim, sourceSpeedDim, receiverSpeedDim, forceDim, lengthDim, massDim,
      sourceTimeDim, receiverTimeDim, axisDim]
  | mass => simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
      speedSquaredDim, sourceSpeedDim, receiverSpeedDim, forceDim, lengthDim, massDim,
      sourceTimeDim, receiverTimeDim, axisDim]
  | time origin =>
      cases origin <;>
        simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
          speedSquaredDim, sourceSpeedDim, receiverSpeedDim, forceDim, lengthDim,
          massDim, sourceTimeDim, receiverTimeDim, axisDim]

theorem einsteinSourceDim_eq_curvatureDim :
    einsteinCouplingDim + stressEnergyDim = curvatureDim := by
  funext axis
  cases axis with
  | length => simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
      speedSquaredDim, sourceSpeedDim, receiverSpeedDim, stressEnergyDim, curvatureDim,
      lengthDim, massDim, sourceTimeDim, receiverTimeDim, axisDim]
  | mass => simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
      speedSquaredDim, sourceSpeedDim, receiverSpeedDim, stressEnergyDim, curvatureDim,
      lengthDim, massDim, sourceTimeDim, receiverTimeDim, axisDim]
  | time origin =>
      cases origin <;>
        simp [einsteinCouplingDim, gravitationalConstantDim, speedFourthDim,
          speedSquaredDim, sourceSpeedDim, receiverSpeedDim, stressEnergyDim,
          curvatureDim, lengthDim, massDim, sourceTimeDim, receiverTimeDim, axisDim]

theorem cosmologicalMetricDim_eq_curvatureDim :
    cosmologicalConstantDim + metricDim = curvatureDim := by
  simp [cosmologicalConstantDim, metricDim]

theorem symmetrize_cosmologicalConstantDim :
    symmetrizeDimension cosmologicalConstantDim = ((-2, 0, 0) : Ellipse.Dim) := by
  simp [symmetrizeDimension, cosmologicalConstantDim, curvatureDim, lengthDim,
    axisDim]

/-! ## Quantities have typed origins; their returned differences survive a common rebase -/

structure QuantityOccurrence (Origin : Type*) (dimension : OriginDim) where
  origin : Origin
  coordinate : ℚ

def returnedDifference {Origin : Type*} {dimension : OriginDim}
    (source receiver : QuantityOccurrence Origin dimension) : ℚ :=
  receiver.coordinate - source.coordinate

def rebase {Origin : Type*} {dimension : OriginDim} (shift : ℚ)
    (quantity : QuantityOccurrence Origin dimension) : QuantityOccurrence Origin dimension where
  origin := quantity.origin
  coordinate := quantity.coordinate - shift

theorem returnedDifference_rebase {Origin : Type*} {dimension : OriginDim}
    (shift : ℚ) (source receiver : QuantityOccurrence Origin dimension) :
    returnedDifference (rebase shift source) (rebase shift receiver) =
      returnedDifference source receiver := by
  simp [returnedDifference, rebase]

/-! ## Tensor squares and exterior event-area are different receivers -/

abbrev EventCovector := Fin 2 → ℤ

def eventCovector (axis : Fin 2) : EventCovector := Pi.single axis 1

def tensorProduct (left right : EventCovector) : Fin 2 → Fin 2 → ℤ :=
  fun i j ↦ left i * right j

/-- The coefficient of the oriented two-event exterior blade. -/
def wedgeArea (left right : EventCovector) : ℤ :=
  left 0 * right 1 - left 1 * right 0

theorem tensor_self_survives :
    tensorProduct (eventCovector 0) (eventCovector 0) 0 0 = 1 := by
  norm_num [tensorProduct, eventCovector]

theorem wedge_self_zero (event : EventCovector) :
    wedgeArea event event = 0 := by
  unfold wedgeArea
  ring

theorem independent_event_wedge :
    wedgeArea (eventCovector 0) (eventCovector 1) = 1 := by
  norm_num [wedgeArea, eventCovector]

end Soma.Holonics.Millennium.HolonicTypedOriginDimensions

section Audit
open Soma.Holonics.Millennium.HolonicTypedOriginDimensions
#print axioms sourceSpeedDim_ne_receiverSpeedDim
#print axioms symmetrize_sourceSpeedDim
#print axioms symmetrize_receiverSpeedDim
#print axioms symmetrize_speedSquaredDim
#print axioms timeOriginDifference_ne_zero
#print axioms symmetrize_timeOriginDifference
#print axioms timeOriginDifference_mem_kernel
#print axioms symmetrizeDimension_not_injective
#print axioms einsteinCouplingDim_eq_neg_forceDim
#print axioms einsteinSourceDim_eq_curvatureDim
#print axioms cosmologicalMetricDim_eq_curvatureDim
#print axioms symmetrize_cosmologicalConstantDim
#print axioms edgeHodgeWeightDim_eq_areaDim
#print axioms faceHodgeWeightDim_eq_zero
#print axioms returnedDifference_rebase
#print axioms tensor_self_survives
#print axioms wedge_self_zero
#print axioms independent_event_wedge
end Audit

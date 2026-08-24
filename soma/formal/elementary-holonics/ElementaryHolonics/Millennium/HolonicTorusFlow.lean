import ElementaryHolonics.Millennium.HolonicPolygonGyroWinding
import ElementaryHolonics.Millennium.NavierStokesDyadicFlowCommutator

/-!
# The genuine torus fluid and its addressed frequency polygons

The primary source of the first passage is a field on the genuine quotient `T^3`; one Fourier
coefficient is a receiver face.  Closed frequency triads and equal-output parallelograms are then
installed as addressed boundary and comparison passages.  The dyadic interact/filter square is
finally expressed by the generic comparison-cell owner: its route difference is exactly the
already proved finite multiplier-flow commutator, and a nonzero commutator returns a receiver
defect without identifying Fourier data with the fluid body.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTorusFlow

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain

/-! ## The field is primary and the Fourier coefficient is a receiver -/

/-- One integer-character receiver on fields already living on the genuine spatial torus. -/
def torusFourierReceiverPassage (k : SpatialFrequency) :
    AddressedPassage (SpatialTorus → ℂ) ℂ :=
  AddressedPassage.graph fun field => torusSpatialFourierCoeff field k

/-- The complete receiver fibre retains the source field occurrence. -/
theorem torusFourierReceiver_retains_field (field : SpatialTorus → ℂ) (k : SpatialFrequency) :
    Nonempty ((torusFourierReceiverPassage k).Fibre field
      (torusSpatialFourierCoeff field k)) :=
  ⟨AddressedPassage.graphFibre _ field⟩

/-! ## Addressed closed triads and frequency parallelograms -/

/-- Boundary order of the three addressed pins in a closed Fourier triad. -/
def triadBoundaryEdges (triad : AddressedClosedFourierTriad) : List SpatialFrequency :=
  [triad.advecting, triad.transported, triad.receiver]

theorem triadBoundaryEdges_close (triad : AddressedClosedFourierTriad) :
    frequencyPolygonBoundary (triadBoundaryEdges triad) = 0 := by
  simpa [frequencyPolygonBoundary, triadBoundaryEdges, add_assoc] using triad.closed

/-- A triad is carried as an occurrence before its additive frequency boundary is read. -/
def triadBoundaryPassage :
    AddressedPassage AddressedClosedFourierTriad SpatialFrequency :=
  AddressedPassage.graph fun triad => frequencyPolygonBoundary (triadBoundaryEdges triad)

theorem triadBoundaryPassage_target_eq_zero (triad : AddressedClosedFourierTriad) :
    triadBoundaryPassage.target triad = 0 :=
  triadBoundaryEdges_close triad

/-- The same closed polygon remains closed in the complex derivative-frequency chart. -/
theorem triadComplexBoundary_eq_zero (triad : AddressedClosedFourierTriad) :
    complexFrequencyPolygonBoundary (triadBoundaryEdges triad) = 0 :=
  complexFrequencyPolygonBoundary_eq_zero_of_closed _ (triadBoundaryEdges_close triad)

def firstFrequencyDecompositionPassage :
    AddressedPassage FrequencyParallelogramComparison SpatialFrequency :=
  AddressedPassage.graph fun comparison => comparison.firstLeft + comparison.firstRight

def secondFrequencyDecompositionPassage :
    AddressedPassage FrequencyParallelogramComparison SpatialFrequency :=
  AddressedPassage.graph fun comparison => comparison.secondLeft + comparison.secondRight

/-- Both decompositions remain separately addressed at one comparison occurrence. -/
def frequencyParallelogramCell (comparison : FrequencyParallelogramComparison) :
    AddressedPassage.ComparisonCell
      firstFrequencyDecompositionPassage secondFrequencyDecompositionPassage where
  left := comparison
  right := comparison
  source_exact := rfl

theorem frequencyParallelogramCell_commutes
    (comparison : FrequencyParallelogramComparison) :
    (frequencyParallelogramCell comparison).Commutes :=
  comparison.sameOutput

/-- The complex frequency receiver preserves the commuting parallelogram. -/
theorem frequencyParallelogramCell_commutesAt_complex
    (comparison : FrequencyParallelogramComparison) :
    (frequencyParallelogramCell comparison).CommutesAt complexFrequencyVector :=
  (frequencyParallelogramCell comparison).commutesAt_of_commutes
    (frequencyParallelogramCell_commutes comparison) complexFrequencyVector

/-! ## The finite multiplier-flow square as a comparison cell -/

abbrev FourierVectorField := SpatialFrequency → ComplexVector

def interactThenFilterCoefficient
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (k : SpatialFrequency) (fields : FourierVectorField × FourierVectorField) : ComplexVector :=
  multiplierFilter multiplier
    (finiteAdvectiveCoefficient aperture fields.1 fields.2) k

def filterThenInteractCoefficient
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (k : SpatialFrequency) (fields : FourierVectorField × FourierVectorField) : ComplexVector :=
  finiteAdvectiveCoefficient aperture fields.1
    (multiplierFilter multiplier fields.2) k

def interactThenFilterPassage
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (k : SpatialFrequency) :
    AddressedPassage (FourierVectorField × FourierVectorField) ComplexVector :=
  AddressedPassage.graph (interactThenFilterCoefficient aperture multiplier k)

def filterThenInteractPassage
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (k : SpatialFrequency) :
    AddressedPassage (FourierVectorField × FourierVectorField) ComplexVector :=
  AddressedPassage.graph (filterThenInteractCoefficient aperture multiplier k)

def multiplierFlowSquareCell
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (advecting transported : FourierVectorField) (k : SpatialFrequency) :
    AddressedPassage.ComparisonCell
      (interactThenFilterPassage aperture multiplier k)
      (filterThenInteractPassage aperture multiplier k) where
  left := (advecting, transported)
  right := (advecting, transported)
  source_exact := rfl

/-- The comparison-cell route difference is the existing finite flow commutator definitionally. -/
theorem multiplierFlowSquare_routeDifference
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (advecting transported : FourierVectorField) (k : SpatialFrequency) :
    (interactThenFilterPassage aperture multiplier k).target
        (multiplierFlowSquareCell aperture multiplier advecting transported k).left -
      (filterThenInteractPassage aperture multiplier k).target
        (multiplierFlowSquareCell aperture multiplier advecting transported k).right =
      finiteMultiplierFlowCommutatorCoefficient aperture multiplier
        advecting transported k := rfl

/-- The square commutes exactly when its complete finite commutator vanishes. -/
theorem multiplierFlowSquare_commutes_iff
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (advecting transported : FourierVectorField) (k : SpatialFrequency) :
    (multiplierFlowSquareCell aperture multiplier advecting transported k).Commutes ↔
      finiteMultiplierFlowCommutatorCoefficient aperture multiplier
        advecting transported k = 0 := by
  change interactThenFilterCoefficient aperture multiplier k (advecting, transported) =
      filterThenInteractCoefficient aperture multiplier k (advecting, transported) ↔ _
  exact sub_eq_zero.symm

/-- A nonzero commutator becomes a route-separating receiver defect, not an erased failure. -/
theorem multiplierFlowSquare_receiverDefect
    (aperture : Finset SpatialFrequency) (multiplier : SpatialFrequency → ℂ)
    (advecting transported : FourierVectorField) (k : SpatialFrequency)
    (hdefect : finiteMultiplierFlowCommutatorCoefficient aperture multiplier
      advecting transported k ≠ 0) :
    (multiplierFlowSquareCell aperture multiplier advecting transported k).ReceiverDefect
      ComplexVector _root_.id := by
  refine ⟨?_⟩
  intro hcommutes
  exact hdefect ((multiplierFlowSquare_commutes_iff aperture multiplier
    advecting transported k).mp hcommutes)

/-- For the direct dyadic Hodge multiplier, the generic route difference is the deposited exact
sum of addressed multiplier differences. -/
theorem dyadicFlowSquare_routeDifference_eq_sum
    (scale : ℕ) (aperture : Finset SpatialFrequency)
    (advecting transported : FourierVectorField) (k : SpatialFrequency) :
    (interactThenFilterPassage aperture (dyadicHodgeBandMultiplier scale) k).target
        (multiplierFlowSquareCell aperture (dyadicHodgeBandMultiplier scale)
          advecting transported k).left -
      (filterThenInteractPassage aperture (dyadicHodgeBandMultiplier scale) k).target
        (multiplierFlowSquareCell aperture (dyadicHodgeBandMultiplier scale)
          advecting transported k).right =
      ∑ p ∈ aperture,
        ((dyadicHodgeBandWeight scale k : ℂ) -
            (dyadicHodgeBandWeight scale (transportedFrequencyAt k p) : ℂ)) •
          complexAdvectiveInteraction p (transportedFrequencyAt k p)
            (advecting p) (transported (transportedFrequencyAt k p)) := by
  rw [multiplierFlowSquare_routeDifference]
  exact finiteDyadicFlowCommutatorCoefficient_eq_sum_difference
    scale aperture advecting transported k

end Soma.Holonics.Millennium.HolonicTorusFlow

section Audit
open Soma.Holonics.Millennium.HolonicTorusFlow
#print axioms torusFourierReceiver_retains_field
#print axioms triadBoundaryPassage_target_eq_zero
#print axioms triadComplexBoundary_eq_zero
#print axioms frequencyParallelogramCell_commutes
#print axioms frequencyParallelogramCell_commutesAt_complex
#print axioms multiplierFlowSquare_routeDifference
#print axioms multiplierFlowSquare_commutes_iff
#print axioms multiplierFlowSquare_receiverDefect
#print axioms dyadicFlowSquare_routeDifference_eq_sum
end Audit

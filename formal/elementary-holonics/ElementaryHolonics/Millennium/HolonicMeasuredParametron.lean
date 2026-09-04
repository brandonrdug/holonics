import ElementaryHolonics.Foundation.MeasuredDifferenceReceiver
import ElementaryHolonics.Millennium.HolonicComplexParametron

/-!
# The coupled parametron coefficients are returned comparisons

**[proved-derived]** `HolonicComplexParametron` proves transport laws for an oriented coupled-LC
lattice while accepting its real coefficient fields as inputs.  This file closes the scalar-
provenance gap: capacitance, inductance, inverse inductance, impedance, and angular frequency are
ratios of returned differences between addressed occurrences.  Their zero points are chart
choices, not physical coefficients.

The measured fields then enter the existing generalized mode relation.  Reorienting branch charts
still preserves the mode because the coefficient measurements and the incidence transport remain
separate typed passages.  The binary phase-selection face is also proved to be a normalized
exponential quotient of one action difference.  No theorem here derives a hardware constitutive
law, passivity, damping, a Floquet spectrum, or a Millennium conclusion.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicMeasuredParametron

open Soma.Holonics.Foundation.MeasuredDifferenceReceiver
open Soma.Holonics.Millennium.HolonicComplexParametron

/-! ## Measured constitutive coefficients -/

/-- `C = ΔQ / ΔV` between two addressed occurrences. -/
def measuredCapacitance {Occurrence : Type*}
    (charge voltage : Occurrence → ℝ) (source target : Occurrence) : ℝ :=
  differenceRatio charge voltage source target

/-- `L = ΔΦ / ΔI` between two addressed occurrences. -/
def measuredInductance {Occurrence : Type*}
    (flux current : Occurrence → ℝ) (source target : Occurrence) : ℝ :=
  differenceRatio flux current source target

/-- `L⁻¹ = ΔI / ΔΦ`, the coefficient consumed by the stiffness response. -/
def measuredInverseInductance {Occurrence : Type*}
    (current flux : Occurrence → ℝ) (source target : Occurrence) : ℝ :=
  differenceRatio current flux source target

/-- `Z = ΔV / ΔI` between two addressed occurrences. -/
def measuredImpedance {Occurrence : Type*}
    (voltage current : Occurrence → ℝ) (source target : Occurrence) : ℝ :=
  differenceRatio voltage current source target

/-- `ω = Δθ / Δt` between two addressed occurrences. -/
def measuredAngularFrequency {Occurrence : Type*}
    (phase time : Occurrence → ℝ) (source target : Occurrence) : ℝ :=
  differenceRatio phase time source target

/-- Away from a zero voltage difference, measured capacitance returns the exact constitutive
comparison `C ΔV = ΔQ`. -/
theorem measuredCapacitance_mul_voltageDifference {Occurrence : Type*}
    (charge voltage : Occurrence → ℝ) (source target : Occurrence)
    (hvoltage : sectionDifference voltage source target ≠ 0) :
    measuredCapacitance charge voltage source target *
        sectionDifference voltage source target =
      sectionDifference charge source target := by
  exact differenceRatio_mul_denominator charge voltage source target hvoltage

/-- Away from a zero flux difference, inverse inductance returns `L⁻¹ ΔΦ = ΔI`. -/
theorem measuredInverseInductance_mul_fluxDifference {Occurrence : Type*}
    (current flux : Occurrence → ℝ) (source target : Occurrence)
    (hflux : sectionDifference flux source target ≠ 0) :
    measuredInverseInductance current flux source target *
        sectionDifference flux source target =
      sectionDifference current source target := by
  exact differenceRatio_mul_denominator current flux source target hflux

/-- Independently shifting the zero points of charge and voltage does not alter capacitance. -/
theorem measuredCapacitance_add_chartZeros {Occurrence : Type*}
    (charge voltage : Occurrence → ℝ) (chargeZero voltageZero : ℝ)
    (source target : Occurrence) :
    measuredCapacitance
        (fun occurrence ↦ charge occurrence + chargeZero)
        (fun occurrence ↦ voltage occurrence + voltageZero)
        source target =
      measuredCapacitance charge voltage source target := by
  exact differenceRatio_add_common charge voltage chargeZero voltageZero source target

/-- Independently shifting the zero points of phase and time does not alter angular frequency. -/
theorem measuredAngularFrequency_add_chartZeros {Occurrence : Type*}
    (phase time : Occurrence → ℝ) (phaseZero timeZero : ℝ)
    (source target : Occurrence) :
    measuredAngularFrequency
        (fun occurrence ↦ phase occurrence + phaseZero)
        (fun occurrence ↦ time occurrence + timeZero)
        source target =
      measuredAngularFrequency phase time source target := by
  exact differenceRatio_add_common phase time phaseZero timeZero source target

/-! ## Branch differences are the branch drop of a state difference -/

/-- The additive branch-drop chart, read without any additional quotient. -/
def branchDifferenceReceiver {Node Branch : Type*} [Fintype Node]
    (incidence : Branch → Node → ℝ) (branch : Branch) :
    DifferenceReceiver (Node → ℝ) ℝ ℝ where
  chart := fun state ↦ branchDrop incidence state branch
  read := id

/-- Linear incidence transports the complete state difference into the branch difference. -/
theorem branchDrop_stateDifference {Node Branch : Type*} [Fintype Node]
    (incidence : Branch → Node → ℝ) (source target : Node → ℝ) (branch : Branch) :
    branchDrop incidence (target - source) branch =
      branchDrop incidence target branch - branchDrop incidence source branch := by
  unfold branchDrop
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro node hnode
  simp only [Pi.sub_apply]
  ring

/-- The difference receiver and the incidence image of the state difference are the same returned
branch occurrence. -/
theorem branchDifferenceReceiver_returnedDifference {Node Branch : Type*} [Fintype Node]
    (incidence : Branch → Node → ℝ) (source target : Node → ℝ) (branch : Branch) :
    (branchDifferenceReceiver incidence branch).returnedDifference source target =
      branchDrop incidence (target - source) branch := by
  rw [DifferenceReceiver.returnedDifference, branchDifferenceReceiver,
    branchDrop_stateDifference]

/-! ## Measured coefficient fields enter the coupled lattice -/

/-- Branchwise capacitance measured from charge and voltage sections. -/
def measuredCapacityField {Occurrence Branch : Type*}
    (charge voltage : Occurrence → Branch → ℝ) (source target : Occurrence) : Branch → ℝ :=
  fun branch ↦ measuredCapacitance
    (fun occurrence ↦ charge occurrence branch)
    (fun occurrence ↦ voltage occurrence branch)
    source target

/-- Branchwise inverse inductance measured from current and flux sections. -/
def measuredStiffnessField {Occurrence Branch : Type*}
    (current flux : Occurrence → Branch → ℝ) (source target : Occurrence) : Branch → ℝ :=
  fun branch ↦ measuredInverseInductance
    (fun occurrence ↦ current occurrence branch)
    (fun occurrence ↦ flux occurrence branch)
    source target

/-- The generalized LC mode after every scalar coefficient and its frequency have been returned
from addressed differences. -/
def IsMeasuredGeneralizedMode
    {Occurrence Node Branch : Type*} [Fintype Node] [Fintype Branch]
    (charge voltage current flux : Occurrence → Branch → ℝ)
    (phase time : Occurrence → ℝ) (source target : Occurrence)
    (incidence : Branch → Node → ℝ) (mode : Node → ℝ) : Prop :=
  IsGeneralizedMode
    (measuredStiffnessField current flux source target)
    (measuredCapacityField charge voltage source target)
    incidence
    ((measuredAngularFrequency phase time source target) ^ 2)
    mode

/-- Pure branch-coordinate reversal preserves the fully measured generalized mode. -/
theorem isMeasuredGeneralizedMode_reorient_iff
    {Occurrence Node Branch : Type*} [Fintype Node] [Fintype Branch]
    (selected : Branch → Bool)
    (charge voltage current flux : Occurrence → Branch → ℝ)
    (phase time : Occurrence → ℝ) (source target : Occurrence)
    (incidence : Branch → Node → ℝ) (mode : Node → ℝ) :
    IsMeasuredGeneralizedMode charge voltage current flux phase time source target
        (reorientIncidence selected incidence) mode ↔
      IsMeasuredGeneralizedMode charge voltage current flux phase time source target
        incidence mode := by
  unfold IsMeasuredGeneralizedMode
  exact isGeneralizedMode_reorient_iff
    (selected := selected)
    (stiffnessWeight := measuredStiffnessField current flux source target)
    (capacityWeight := measuredCapacityField charge voltage source target)
    (incidence := incidence)
    (omegaSq := (measuredAngularFrequency phase time source target) ^ 2)
    (mode := mode)

/-! ## Binary collapse retains an action-difference fibre -/

/-- A two-basin receiver face from two action potentials.  This is a scalar quotient of the
complex pre-locking body, not a replacement for it. -/
def binaryActionFace {Occurrence : Type*} (action : Occurrence → ℝ)
    (source target : Occurrence) : ℝ :=
  binaryExponentialFace (action source) (action target)

/-- Binary action selection depends only on the oriented action difference. -/
theorem binaryActionFace_eq_logisticDifference {Occurrence : Type*}
    (action : Occurrence → ℝ) (source target : Occurrence) :
    binaryActionFace action source target =
      logisticDifference (sectionDifference action source target) := by
  exact binaryExponentialFace_eq_logisticDifference _ _

/-- Adding a common action potential is invisible to the binary receiver. -/
theorem binaryActionFace_add_common {Occurrence : Type*}
    (action : Occurrence → ℝ) (common : ℝ) (source target : Occurrence) :
    binaryActionFace (fun occurrence ↦ action occurrence + common) source target =
      binaryActionFace action source target := by
  exact binaryExponentialFace_add_common _ _ _

section Audit

#print axioms measuredCapacitance_mul_voltageDifference
#print axioms measuredInverseInductance_mul_fluxDifference
#print axioms measuredCapacitance_add_chartZeros
#print axioms branchDrop_stateDifference
#print axioms branchDifferenceReceiver_returnedDifference
#print axioms isMeasuredGeneralizedMode_reorient_iff
#print axioms binaryActionFace_eq_logisticDifference

end Audit

end Soma.Holonics.Millennium.HolonicMeasuredParametron

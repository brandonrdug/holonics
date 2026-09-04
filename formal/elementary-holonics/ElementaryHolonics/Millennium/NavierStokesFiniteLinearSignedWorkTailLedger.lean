import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
import ElementaryHolonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin

/-!
# Finite linear signed-work tail ledger

**[proved-derived; formal-checked]**  The compact-time one-copy linear boundary work is compared
with one pair-compatible finite interaction radius before any scale-by-scale magnitude is taken.
The finite work is then split into its physical direction reading, the literal output-frequency
tail, and the three multiplier-crossing boundary faces.  The remaining difference between the
actual source and the finite interaction radius is retained as an explicit radius tail.

The resulting time ledger applies one extended norm only after the finite scale word has been
formed and integrated in time.  It does not assert that the output tail, interaction-radius tail,
or multiplier-crossing population vanishes or is summable.  In particular, the kinetic base used
below is the ordinary-energy base from `NavierStokesVorticityDirectionBaseEnergy`, never the older
critical-vorticity-rate base.
-/

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped BigOperators Interval ENNReal

namespace Soma.Holonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Compact actual work and its finite-radius difference -/

/-- One pair-compatible finite-radius presentation of the compactly clamped one-copy boundary
work.  The finite scale word has already been condensed to its common low-pass boundary. -/
def compactFinitePairCompatibleBoundaryNonlinearWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) : ℝ :=
  (finitePairCompatibleBoundaryNonlinearWork solution
    (compactInteriorTime ha hab hbT time) depth radius).re

/-- The actual-minus-finite interaction-radius tail.  It is a literal difference of work rates,
not a summability premise or a generated receipt. -/
def compactFiniteLinearInteractionRadiusTailRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) : ℝ :=
  compactOpenSmoothDyadicLinearBoundarySignedWorkRate
      solution ha hab hbT depth time -
    compactFinitePairCompatibleBoundaryNonlinearWorkRate
      solution ha hab hbT depth radius time

theorem compactLinearBoundaryWork_eq_finiteRadius_add_tail
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) :
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time =
      compactFinitePairCompatibleBoundaryNonlinearWorkRate
          solution ha hab hbT depth radius time +
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time := by
  unfold compactFiniteLinearInteractionRadiusTailRate
  ring

/-- At each compactly clamped time, the explicit interaction-radius tail converges to zero.  This
is pointwise in time; no uniform or time-integrated radius passage is asserted. -/
theorem tendsto_compactFiniteLinearInteractionRadiusTailRate_zero
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    Tendsto
      (fun radius : ℕ ↦
        compactFiniteLinearInteractionRadiusTailRate
          solution ha hab hbT depth radius time)
      atTop (nhds 0) := by
  let t := compactInteriorTime ha hab hbT time
  have hlimit :=
    tendsto_finitePairCompatibleBoundaryNonlinearWork_re_to_actualScaleSum
      solution t depth
  have hboundary :
      (∑ scale ∈ Finset.range depth,
          openSmoothDyadicLinearBandActualSignedWorkRate solution t scale) =
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time := by
    simpa [t, compactOpenSmoothDyadicLinearBandActualSignedWorkRate] using
      sum_compactOpenSmoothDyadicLinearBandActualSignedWorkRate_eq_boundary
        solution ha hab hbT depth time
  rw [hboundary] at hlimit
  have hconst : Tendsto
      (fun _radius : ℕ ↦
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time)
      atTop
      (nhds (compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time)) := tendsto_const_nhds
  have htail := hconst.sub hlimit
  simpa [compactFiniteLinearInteractionRadiusTailRate,
    compactFinitePairCompatibleBoundaryNonlinearWorkRate] using htail

/-! ## Physical direction, output, and multiplier-crossing populations -/

/-- The exact finite-depth physical direction mass together with its scale-zero kinetic base.
The second summand is controlled by
`norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy`; no critical vorticity rate enters.
Keeping the actual base norm here avoids duplicating its calibrated Fourier constant. -/
def finiteDepthKineticDirectionReceiverMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  (∫ q : SpatialTorus,
      ‖finiteDepthDyadicHodgeStrainReading solution t q depth‖) +
    ∫ q : SpatialTorus,
      ‖openPeriodicDyadicBaseStrainReading solution t q‖

theorem finiteDepthKineticDirectionReceiverMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    0 ≤ finiteDepthKineticDirectionReceiverMass solution t depth := by
  unfold finiteDepthKineticDirectionReceiverMass
  have hdirection : 0 ≤ ∫ q : SpatialTorus,
      ‖finiteDepthDyadicHodgeStrainReading solution t q depth‖ :=
    integral_nonneg fun q ↦ norm_nonneg
      (finiteDepthDyadicHodgeStrainReading solution t q depth)
  have hbase : 0 ≤ ∫ q : SpatialTorus,
      ‖openPeriodicDyadicBaseStrainReading solution t q‖ :=
    integral_nonneg fun q ↦ norm_nonneg
      (openPeriodicDyadicBaseStrainReading solution t q)
  exact add_nonneg hdirection hbase

/-- The literal receiver-frequency output tail exposed by the common-aperture Parseval join. -/
def finitePairCompatiblePhysicalOutputTailMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℝ :=
  ∫ q : SpatialTorus,
    ‖finitePairCompatibleStrainOutputTail solution t depth radius q‖

/-- The complete finite multiplier-crossing population still requiring a scale/radius
summability law: stretching commutator, transported-filter cross-boundary, and transport
commutator.  Same-weight transport faces cancel before this receiver; these are precisely the
surviving crossing faces. -/
def finitePairCompatibleMultiplierCrossingBoundaryMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) : ℝ :=
  |(finitePairCompatibleStretchingMultiplierBoundaryWork
      solution t depth radius).re| +
    |(finitePairCompatibleTransportCrossBoundaryWork
      solution t depth radius).re| +
    |(finitePairCompatibleTransportMultiplierBoundaryWork
      solution t depth radius).re|

/-- The finite-radius pointwise tail majorant.  It names every population and retains the actual
interaction-radius difference rather than replacing it by an unproved convergence rate. -/
def compactFiniteLinearSignedWorkTailMajorant
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) : ℝ :=
  let t := compactInteriorTime ha hab hbT time
  finiteDepthKineticDirectionReceiverMass solution t depth +
    finitePairCompatiblePhysicalOutputTailMass solution t depth radius +
    finitePairCompatibleMultiplierCrossingBoundaryMass solution t depth radius +
    |compactFiniteLinearInteractionRadiusTailRate
      solution ha hab hbT depth radius time|

private theorem four_terms_le_paid_head
    (head first second third payment output : ℝ)
    (hhead : head ≤ payment + output) :
    head + first + second + third ≤
      payment + output + (first + second + third) := by
  linarith

private theorem abs_finiteBoundaryWork_le_physicalTailMajorant
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth radius : ℕ) :
    |(finitePairCompatibleBoundaryNonlinearWork solution t depth radius).re| ≤
      finiteDepthKineticDirectionReceiverMass solution t depth +
        finitePairCompatiblePhysicalOutputTailMass solution t depth radius +
        finitePairCompatibleMultiplierCrossingBoundaryMass solution t depth radius := by
  have hstrain :
      |(finitePairCompatibleStrainFilteredStretchingWork
          solution t depth radius).re| ≤
        finiteDepthKineticDirectionReceiverMass solution t depth +
          finitePairCompatiblePhysicalOutputTailMass solution t depth radius := by
    have hdecomposition :=
      finitePairCompatibleStrainFilteredStretchingWork_eq_directionIntegral_add_defect
        solution t depth radius
    have hcomplex :
        ‖finitePairCompatibleStrainFilteredStretchingWork
            solution t depth radius‖ ≤
          ‖∫ q : SpatialTorus,
              finiteDepthDyadicHodgeStrainReading solution t q depth‖ +
            ‖finitePairCompatibleStrainDirectionIdentificationDefect
              solution t depth radius‖ := by
      rw [hdecomposition]
      exact norm_add_le _ _
    calc
      |(finitePairCompatibleStrainFilteredStretchingWork
          solution t depth radius).re| ≤
          ‖finitePairCompatibleStrainFilteredStretchingWork
            solution t depth radius‖ := Complex.abs_re_le_norm _
      _ ≤
          ‖∫ q : SpatialTorus,
              finiteDepthDyadicHodgeStrainReading solution t q depth‖ +
            ‖finitePairCompatibleStrainDirectionIdentificationDefect
              solution t depth radius‖ := hcomplex
      _ ≤
          (∫ q : SpatialTorus,
              ‖finiteDepthDyadicHodgeStrainReading solution t q depth‖) +
            finitePairCompatiblePhysicalOutputTailMass
              solution t depth radius :=
        add_le_add
          (norm_integral_le_integral_norm _)
          (norm_finitePairCompatibleStrainDirectionIdentificationDefect_le_outputTail
            solution t depth radius)
      _ ≤ finiteDepthKineticDirectionReceiverMass solution t depth +
            finitePairCompatiblePhysicalOutputTailMass
              solution t depth radius := by
        gcongr
        unfold finiteDepthKineticDirectionReceiverMass
        have hbase : 0 ≤ ∫ q : SpatialTorus,
            ‖openPeriodicDyadicBaseStrainReading solution t q‖ :=
          integral_nonneg fun q ↦ norm_nonneg
            (openPeriodicDyadicBaseStrainReading solution t q)
        exact le_add_of_nonneg_right
          hbase
  have hboundary :=
    finitePairCompatibleBoundaryNonlinearWork_re_eq_direction_plus_boundaries
      solution t depth radius
  rw [hboundary]
  calc
    |(finitePairCompatibleStrainFilteredStretchingWork
          solution t depth radius).re +
        (finitePairCompatibleStretchingMultiplierBoundaryWork
          solution t depth radius).re -
        (finitePairCompatibleTransportCrossBoundaryWork
          solution t depth radius).re -
        (finitePairCompatibleTransportMultiplierBoundaryWork
          solution t depth radius).re| ≤
      |(finitePairCompatibleStrainFilteredStretchingWork
          solution t depth radius).re| +
        |(finitePairCompatibleStretchingMultiplierBoundaryWork
          solution t depth radius).re| +
        |(finitePairCompatibleTransportCrossBoundaryWork
          solution t depth radius).re| +
        |(finitePairCompatibleTransportMultiplierBoundaryWork
          solution t depth radius).re| := by
      calc
        |(finitePairCompatibleStrainFilteredStretchingWork
              solution t depth radius).re +
            (finitePairCompatibleStretchingMultiplierBoundaryWork
              solution t depth radius).re -
            (finitePairCompatibleTransportCrossBoundaryWork
              solution t depth radius).re -
            (finitePairCompatibleTransportMultiplierBoundaryWork
              solution t depth radius).re| ≤
          |(finitePairCompatibleStrainFilteredStretchingWork
                solution t depth radius).re +
              (finitePairCompatibleStretchingMultiplierBoundaryWork
                solution t depth radius).re -
              (finitePairCompatibleTransportCrossBoundaryWork
                solution t depth radius).re| +
            |(finitePairCompatibleTransportMultiplierBoundaryWork
              solution t depth radius).re| := abs_sub _ _
        _ ≤
          (|(finitePairCompatibleStrainFilteredStretchingWork
                solution t depth radius).re +
              (finitePairCompatibleStretchingMultiplierBoundaryWork
                solution t depth radius).re| +
            |(finitePairCompatibleTransportCrossBoundaryWork
              solution t depth radius).re|) +
            |(finitePairCompatibleTransportMultiplierBoundaryWork
              solution t depth radius).re| := by
          gcongr
          exact abs_sub _ _
        _ ≤
          ((|(finitePairCompatibleStrainFilteredStretchingWork
                solution t depth radius).re| +
              |(finitePairCompatibleStretchingMultiplierBoundaryWork
                solution t depth radius).re|) +
            |(finitePairCompatibleTransportCrossBoundaryWork
              solution t depth radius).re|) +
            |(finitePairCompatibleTransportMultiplierBoundaryWork
              solution t depth radius).re| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by ring
    _ ≤ finiteDepthKineticDirectionReceiverMass solution t depth +
        finitePairCompatiblePhysicalOutputTailMass solution t depth radius +
        finitePairCompatibleMultiplierCrossingBoundaryMass
          solution t depth radius := by
      unfold finitePairCompatibleMultiplierCrossingBoundaryMass
      exact four_terms_le_paid_head
        |(finitePairCompatibleStrainFilteredStretchingWork
          solution t depth radius).re|
        |(finitePairCompatibleStretchingMultiplierBoundaryWork
          solution t depth radius).re|
        |(finitePairCompatibleTransportCrossBoundaryWork
          solution t depth radius).re|
        |(finitePairCompatibleTransportMultiplierBoundaryWork
          solution t depth radius).re|
        (finiteDepthKineticDirectionReceiverMass solution t depth)
        (finitePairCompatiblePhysicalOutputTailMass solution t depth radius)
        hstrain

/-- **Actual finite-depth, finite-radius signed-work estimate.**  The magnitude is taken after
the complete finite scale prefix has reached one common boundary.  The four named right-hand
populations are the non-circular direction receiver, physical output tail, multiplier crossings,
and actual interaction-radius tail. -/
theorem abs_compactLinearBoundaryWork_le_signedWorkTailMajorant
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) (time : ℝ) :
    |compactOpenSmoothDyadicLinearBoundarySignedWorkRate
        solution ha hab hbT depth time| ≤
      compactFiniteLinearSignedWorkTailMajorant
        solution ha hab hbT depth radius time := by
  rw [compactLinearBoundaryWork_eq_finiteRadius_add_tail
    solution ha hab hbT depth radius time]
  refine (abs_add_le _ _).trans ?_
  unfold compactFiniteLinearSignedWorkTailMajorant
    compactFinitePairCompatibleBoundaryNonlinearWorkRate
  have hfinite := abs_finiteBoundaryWork_le_physicalTailMajorant solution
    (compactInteriorTime ha hab hbT time) depth radius
  exact add_le_add hfinite le_rfl

/-! ## One phase-first time receiver -/

/-- **Combined prefix signed-work time ledger.**  The left extended norm is applied only after
the actual finite scale prefix has been integrated in time.  The right side is the unconditional
extended integral of the four explicit finite-radius populations.  Extended nonnegative values
are used deliberately: no hidden time-integrability or terminal summability premise is inserted.
-/
theorem enorm_integral_compactLinearBoundaryWork_le_signedWorkTailLedger
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth radius : ℕ) :
    ‖∫ time in a..b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ₑ ≤
      ∫⁻ time in Ioc a b,
        ENNReal.ofReal
          (compactFiniteLinearSignedWorkTailMajorant
            solution ha hab hbT depth radius time) := by
  rw [intervalIntegral.integral_of_le hab]
  calc
    ‖∫ time in Ioc a b,
        compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ₑ ≤
      ∫⁻ time in Ioc a b,
        ‖compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ time in Ioc a b,
        ENNReal.ofReal
          (compactFiniteLinearSignedWorkTailMajorant
            solution ha hab hbT depth radius time) := by
      apply lintegral_mono
      intro time
      change
        ‖compactOpenSmoothDyadicLinearBoundarySignedWorkRate
          solution ha hab hbT depth time‖ₑ ≤
        ENNReal.ofReal
          (compactFiniteLinearSignedWorkTailMajorant
            solution ha hab hbT depth radius time)
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_ofReal
        (abs_compactLinearBoundaryWork_le_signedWorkTailMajorant
          solution ha hab hbT depth radius time)

/-- **Clock-payment consequence.**  The positive part of the parabolically clocked finite-prefix
payment above the depth-independent initial storage is controlled by the same physical tail
ledger.  This composes the one-copy spectral service bridge from the scale--time owner with the
finite-radius work decomposition; it does not identify the one-copy and two-copy signed works. -/
theorem ofReal_clockedPrefixExcess_le_signedWorkTailLedger
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth radius : ℕ) :
    ENNReal.ofReal
        (nu * (∫ time in a..b,
            compactOpenSmoothDyadicPrefixClockedCoefficientMass
              solution ha hab hbT depth time) -
          (1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2) ≤
      ∫⁻ time in Ioc a b,
        ENNReal.ofReal
          (compactFiniteLinearSignedWorkTailMajorant
            solution ha hab hbT depth radius time) := by
  let work : ℝ := ∫ time in a..b,
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
      solution ha hab hbT depth time
  have hclock :=
    openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  have hexcess :
      nu * (∫ time in a..b,
          compactOpenSmoothDyadicPrefixClockedCoefficientMass
            solution ha hab hbT depth time) -
        (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 ≤ |work| := by
    exact sub_le_iff_le_add.mpr (by
      simpa only [work, add_comm] using hclock)
  calc
    ENNReal.ofReal
        (nu * (∫ time in a..b,
            compactOpenSmoothDyadicPrefixClockedCoefficientMass
              solution ha hab hbT depth time) -
          (1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2) ≤
      ENNReal.ofReal |work| := ENNReal.ofReal_le_ofReal hexcess
    _ = ‖work‖ₑ := (Real.enorm_eq_ofReal_abs work).symm
    _ ≤ ∫⁻ time in Ioc a b,
        ENNReal.ofReal
          (compactFiniteLinearSignedWorkTailMajorant
            solution ha hab hbT depth radius time) := by
      dsimp [work]
      exact enorm_integral_compactLinearBoundaryWork_le_signedWorkTailLedger
        solution ha hab hbT depth radius

section Audit

#print axioms compactLinearBoundaryWork_eq_finiteRadius_add_tail
#print axioms tendsto_compactFiniteLinearInteractionRadiusTailRate_zero
#print axioms finiteDepthKineticDirectionReceiverMass_nonneg
#print axioms abs_compactLinearBoundaryWork_le_signedWorkTailMajorant
#print axioms enorm_integral_compactLinearBoundaryWork_le_signedWorkTailLedger
#print axioms ofReal_clockedPrefixExcess_le_signedWorkTailLedger
#print axioms norm_openPeriodicDyadicBaseStrainReading_le_kineticEnergy
#print axioms finiteDepthWeightedTransportExchange_eq_zero_of_weight_eq
#print axioms norm_finiteDepthWeightedTransportExchange_le_triadicEnergyFace

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteLinearSignedWorkTailLedger

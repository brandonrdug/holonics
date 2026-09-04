import ElementaryHolonics.Millennium.NavierStokesAdaptiveMatchedPhysicalService
import ElementaryHolonics.Millennium.NavierStokesH2StorageDissipationPayment

/-!
# Coordinate payment of the matched cofinal physical endpoint

**[proved-derived; formal-checked]**  The exact cofinal-work receiver is paid without returning
to a compact-time `H3` supremum.  The two endpoint enstrophy faces descend to coordinate `H2`
storage, while the accumulated vorticity dissipation and the retained scale-zero reconstruction
fibre remain explicitly addressed.  Thus the only nonlinear endpoint debt is the literal
scale-zero fibre already present in the cofinal cancellation theorem; it is not replaced by an
assumed adapter or an unsigned per-scale work sum.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesMatchedPhysicalEndpointPayment

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveClockMatchedPacking
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedPhysicalService
open Soma.Holonics.Millennium.NavierStokesCofinalWorkEnstrophyJoin
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesEnstrophyTerminalCurrent
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-! ## Endpoint enstrophy is coordinate storage -/

/-- The physical enstrophy at an admitted time is paid by twice the full coordinate `H2`
storage.  This uses the coarse curl inequality and the exact identity between first-coordinate
storage and order-zero dissipation.  No zero-mean frame is selected. -/
theorem openPeriodicSolutionOn_periodicEnstrophy_le_two_mul_coordinateH2Energy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    periodicEnstrophy velocity t ≤ 2 * coordinateH2Energy velocity t := by
  have hcurl :=
    openPeriodicSolutionOn_integral_norm_vorticityField_sq_le_two_mul_dissipation
      solution ht
  rw [integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy] at hcurl
  have hfirst :=
    openPeriodicSolutionOn_two_mul_coordinateH1Storage_eq_coordinateH0Dissipation
      solution ht
  have hkinetic : 0 ≤ periodicKineticEnergy velocity t :=
    periodicKineticEnergy_nonneg velocity t
  have hsecondStorage : 0 ≤ coordinateH2Storage velocity t := by
    unfold coordinateH2Storage
    exact Finset.sum_nonneg fun word _hword ↦
      periodicKineticEnergy_nonneg (coordinateJetField velocity 2 word) t
  rw [coordinateH2Energy_eq_kinetic_add_H1Storage_add_H2Storage]
  linarith

/-! ## Exact physical current and paid square service -/

/-- The endpoint-current population which pays the exact cofinal work.  The first term is the
actual left-face complete vorticity coefficient mass.  The next two are coordinate-storage
payments for the endpoint enstrophies.  The final two retain the viscous occupation and the
scale-zero reconstruction fibre separately. -/
def compactMatchedPhysicalEndpointCurrent
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  (1 / 2 : ℝ) *
      openPeriodicFullVorticityCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
    2 * coordinateH2Energy velocity a +
    2 * coordinateH2Energy velocity b +
    nu * (∫ time in a..b, periodicVorticityDissipation velocity time) +
    abs (compactScaleZeroLinearWorkBoundaryRealIntegral solution ha hab hbT)

/-- The coordinate-paid cofinal square service. -/
def compactAdaptiveMatchedCoordinateEndpointSquareService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  nu⁻¹ * (1024 * (b - a) *
    compactMatchedPhysicalEndpointCurrent solution ha hab hbT)

/-- The same payment after the coordinate `H2` storage faces have descended through their exact
storage/dissipation owner.  The undifferentiated Galilean face is the initial kinetic storage;
the two endpoint `H3` viscous populations remain individually addressed. -/
def compactMatchedH3EndpointCurrent
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  (1 / 2 : ℝ) *
      openPeriodicFullVorticityCoefficientMass solution
        ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
    4 * periodicKineticEnergy velocity 0 +
    coordinateH3ViscousDissipation velocity a +
    coordinateH3ViscousDissipation velocity b +
    nu * (∫ time in a..b, periodicVorticityDissipation velocity time) +
    abs (compactScaleZeroLinearWorkBoundaryRealIntegral solution ha hab hbT)

/-- The endpoint-`H3` presentation of the cofinal square service. -/
def compactAdaptiveMatchedH3EndpointSquareService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) : ℝ :=
  nu⁻¹ * (1024 * (b - a) *
    compactMatchedH3EndpointCurrent solution ha hab hbT)

/-- The accumulated vorticity dissipation is nonnegative on an ordered interval. -/
theorem integral_periodicVorticityDissipation_nonneg
    {a b : ℝ} {velocity : VelocityField} (hab : a ≤ b) :
    0 ≤ ∫ time in a..b, periodicVorticityDissipation velocity time := by
  apply intervalIntegral.integral_nonneg hab
  intro time _htime
  unfold periodicVorticityDissipation
  apply integral_nonneg_of_ae
  filter_upwards with x
  exact Finset.sum_nonneg fun component _hcomponent ↦ sq_nonneg _

/-- The exact cofinal signed-work integral is bounded by the two endpoint enstrophies, the
nonnegative viscous occupation, and the absolute retained scale-zero fibre. -/
theorem abs_compactCofinalLinearMultiplierWorkRealIntegral_le_physicalEndpointCurrent
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b) :
    abs (compactCofinalLinearMultiplierWorkRealIntegral solution ha hab hbT) ≤
      2 * coordinateH2Energy velocity a +
      2 * coordinateH2Energy velocity b +
      nu * (∫ time in a..b, periodicVorticityDissipation velocity time) +
      abs (compactScaleZeroLinearWorkBoundaryRealIntegral solution ha hab hbT) := by
  rw [compactCofinalLinearMultiplierWorkRealIntegral_eq_endpointEnstrophy
    solution ha hab hbT receipt]
  let enstrophyA := periodicEnstrophy velocity a
  let enstrophyB := periodicEnstrophy velocity b
  let dissipation := ∫ time in a..b, periodicVorticityDissipation velocity time
  let scaleZero := compactScaleZeroLinearWorkBoundaryRealIntegral solution ha hab hbT
  have haT : a < T := hab.trans_lt hbT
  have henstrophyA : enstrophyA ≤ 2 * coordinateH2Energy velocity a :=
    openPeriodicSolutionOn_periodicEnstrophy_le_two_mul_coordinateH2Energy
      solution ⟨ha, haT⟩
  have henstrophyB : enstrophyB ≤ 2 * coordinateH2Energy velocity b :=
    openPeriodicSolutionOn_periodicEnstrophy_le_two_mul_coordinateH2Energy
      solution ⟨ha.trans_le hab, hbT⟩
  have henstrophyANonneg : 0 ≤ enstrophyA :=
    periodicKineticEnergy_nonneg (vorticityField velocity) a
  have henstrophyBNonneg : 0 ≤ enstrophyB :=
    periodicKineticEnergy_nonneg (vorticityField velocity) b
  have hdissipation : 0 ≤ dissipation :=
    integral_periodicVorticityDissipation_nonneg hab
  have hviscous : 0 ≤ nu * dissipation := mul_nonneg hnu.le hdissipation
  calc
    |enstrophyB - enstrophyA + nu * dissipation - scaleZero| ≤
        |enstrophyB - enstrophyA + nu * dissipation| + |scaleZero| :=
      abs_sub _ _
    _ ≤ (|enstrophyB - enstrophyA| + |nu * dissipation|) + |scaleZero| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ ((|enstrophyB| + |enstrophyA|) + |nu * dissipation|) + |scaleZero| := by
      gcongr
      exact abs_sub _ _
    _ = (enstrophyB + enstrophyA) + nu * dissipation + |scaleZero| := by
      rw [abs_of_nonneg henstrophyBNonneg, abs_of_nonneg henstrophyANonneg,
        abs_of_nonneg hviscous]
    _ ≤ (2 * coordinateH2Energy velocity b +
          2 * coordinateH2Energy velocity a) +
        nu * dissipation + |scaleZero| := by gcongr
    _ = 2 * coordinateH2Energy velocity a +
        2 * coordinateH2Energy velocity b +
        nu * dissipation + |scaleZero| := by ring

/-- **Public endpoint-uniform matched-service inequality.**  The cancellation-preserving service
is paid by the left coefficient mass and the exact physical endpoint current.  There is no
compact `H3` supremum, no zero-mean assumption, and no hidden scale-wise absolute-value sum. -/
theorem compactAdaptiveMatchedCofinalSquareService_le_coordinateEndpointService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b) :
    compactAdaptiveMatchedCofinalSquareService solution ha hab hbT ≤
      compactAdaptiveMatchedCoordinateEndpointSquareService
        solution ha hab hbT := by
  unfold compactAdaptiveMatchedCofinalSquareService
    compactAdaptiveMatchedCoordinateEndpointSquareService
    compactMatchedPhysicalEndpointCurrent
  have hwork :=
    abs_compactCofinalLinearMultiplierWorkRealIntegral_le_physicalEndpointCurrent
      solution hnu ha hab hbT receipt
  have hfactor : 0 ≤ nu⁻¹ * (1024 * (b - a)) := by positivity
  calc
    nu⁻¹ * (1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT))) =
      (nu⁻¹ * (1024 * (b - a))) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          abs (compactCofinalLinearMultiplierWorkRealIntegral
            solution ha hab hbT)) := by ring
    _ ≤ (nu⁻¹ * (1024 * (b - a))) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          (2 * coordinateH2Energy velocity a +
            2 * coordinateH2Energy velocity b +
            nu * (∫ time in a..b, periodicVorticityDissipation velocity time) +
            abs (compactScaleZeroLinearWorkBoundaryRealIntegral
              solution ha hab hbT))) := by
      gcongr
    _ = nu⁻¹ * (1024 * (b - a) *
        ((1 / 2 : ℝ) *
            openPeriodicFullVorticityCoefficientMass solution
              ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
          2 * coordinateH2Energy velocity a +
          2 * coordinateH2Energy velocity b +
          nu * (∫ time in a..b, periodicVorticityDissipation velocity time) +
          abs (compactScaleZeroLinearWorkBoundaryRealIntegral
            solution ha hab hbT))) := by ring

/-- The coordinate endpoint current is paid by initial kinetic storage and the two literal
endpoint `H3` viscous populations.  This is pointwise endpoint dissipation, not a compact-time
supremum and not a cubic quantity. -/
theorem compactMatchedPhysicalEndpointCurrent_le_H3EndpointCurrent
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    compactMatchedPhysicalEndpointCurrent solution ha hab hbT ≤
      compactMatchedH3EndpointCurrent solution ha hab hbT := by
  have haT : a < T := hab.trans_lt hbT
  have hstorageA :=
    openPeriodicSolutionOn_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
      solution hnu ⟨ha, haT⟩
  have hstorageB :=
    openPeriodicSolutionOn_coordinateH2Energy_le_initialKinetic_add_half_H3Dissipation
      solution hnu ⟨ha.trans_le hab, hbT⟩
  unfold compactMatchedPhysicalEndpointCurrent compactMatchedH3EndpointCurrent
  nlinarith

/-- The original cancellation-preserving service therefore also has a public initial-storage /
endpoint-dissipation payment. -/
theorem compactAdaptiveMatchedCofinalSquareService_le_H3EndpointService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b) :
    compactAdaptiveMatchedCofinalSquareService solution ha hab hbT ≤
      compactAdaptiveMatchedH3EndpointSquareService solution ha hab hbT := by
  have hcoordinate :=
    compactAdaptiveMatchedCofinalSquareService_le_coordinateEndpointService
      solution hnu ha hab hbT receipt
  have hcurrent := compactMatchedPhysicalEndpointCurrent_le_H3EndpointCurrent
    solution hnu.le ha hab hbT
  have hservice :
      compactAdaptiveMatchedCoordinateEndpointSquareService
          solution ha hab hbT ≤
        compactAdaptiveMatchedH3EndpointSquareService
          solution ha hab hbT := by
    unfold compactAdaptiveMatchedCoordinateEndpointSquareService
      compactAdaptiveMatchedH3EndpointSquareService
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hcurrent
        (mul_nonneg (by norm_num) (sub_nonneg.mpr hab)))
      (inv_nonneg.mpr hnu.le)
  exact hcoordinate.trans hservice

/-- Every finite matched diagonal inherits the coordinate endpoint service. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_coordinateEndpointService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      compactAdaptiveMatchedCoordinateEndpointSquareService
        solution ha hab hbT := by
  exact (compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_cofinalService
    solution hnu ha hab hbT depth).trans
      (compactAdaptiveMatchedCofinalSquareService_le_coordinateEndpointService
        solution hnu ha hab hbT receipt)

/-- Every finite matched diagonal also inherits the initial-kinetic / endpoint-`H3`
presentation directly. -/
theorem compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_H3EndpointService
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (receipt : EnstrophyStrandIntervalReceipt (0 : VelocityField) velocity a b)
    (depth : ℕ) :
    compactOpenSmoothDyadicAdaptiveMatchedL1Prefix
        solution ha hab hbT depth ^ 2 ≤
      compactAdaptiveMatchedH3EndpointSquareService
        solution ha hab hbT := by
  exact (compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_cofinalService
    solution hnu ha hab hbT depth).trans
      (compactAdaptiveMatchedCofinalSquareService_le_H3EndpointService
        solution hnu ha hab hbT receipt)

section Audit

#print axioms openPeriodicSolutionOn_periodicEnstrophy_le_two_mul_coordinateH2Energy
#print axioms abs_compactCofinalLinearMultiplierWorkRealIntegral_le_physicalEndpointCurrent
#print axioms compactAdaptiveMatchedCofinalSquareService_le_coordinateEndpointService
#print axioms compactMatchedPhysicalEndpointCurrent_le_H3EndpointCurrent
#print axioms compactAdaptiveMatchedCofinalSquareService_le_H3EndpointService
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_coordinateEndpointService
#print axioms compactOpenSmoothDyadicAdaptiveMatchedL1Prefix_sq_le_H3EndpointService

end Audit

end Soma.Holonics.Millennium.NavierStokesMatchedPhysicalEndpointPayment

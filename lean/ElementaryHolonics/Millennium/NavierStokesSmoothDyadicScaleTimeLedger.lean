import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary

/-!
# Signed smooth-dyadic scale--time ledger

**[proved-derived; formal-checked]** The exact smooth-band energy laws are added over a finite
scale word before any nonlinear work is replaced by an absolute value.  This retains the signed
interaction among bands while exposing one storage face at each time and one viscous clock
payment over the whole word.

The initial storage is then condensed through the actual depth-independent boundary theorem.
Consequently the clocked coefficient population is bounded uniformly in the word depth by the
initial full vorticity coefficient mass and the absolute value of one *combined* signed-work
integral.  No sum of per-band absolute work occurs here.

This is a compact-interior scale--time estimate.  The remaining PDE obligation is to control the
combined signed work uniformly as the right endpoint approaches the terminal face; no terminal
regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger

set_option maxHeartbeats 2400000

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearUniformBoundary
open Soma.Holonics.Millennium.NavierStokesSmoothSharpDyadicShellComparison
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-! ## Finite scale-word receivers -/

/-- The retained real storage in the first `depth` smooth dyadic bands. -/
def openSmoothDyadicPrefixRealEnergy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    openSmoothDyadicBandRealEnergy solution t scale

/-- The compactly charted spectral dissipation in a finite scale word. -/
def compactOpenSmoothDyadicPrefixSpectralDissipationMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) (time : ℝ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicBandSpectralDissipationMass
      solution ha hab hbT scale time

/-- The compactly charted signed nonlinear work after every band occurrence has reached one
finite scale receiver. -/
def compactOpenSmoothDyadicPrefixActualSignedWorkRate
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) (time : ℝ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    compactOpenSmoothDyadicBandActualSignedWorkRate
      solution ha hab hbT scale time

/-- The parabolically clocked smooth-band coefficient population in a finite scale word. -/
def compactOpenSmoothDyadicPrefixClockedCoefficientMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) (time : ℝ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    (4 : ℝ) ^ scale *
      compactOpenSmoothDyadicBandCoefficientMass
        solution ha hab hbT scale time

theorem openSmoothDyadicPrefixRealEnergy_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    0 ≤ openSmoothDyadicPrefixRealEnergy solution t depth := by
  unfold openSmoothDyadicPrefixRealEnergy
  exact Finset.sum_nonneg fun scale _hscale ↦
    openSmoothDyadicBandRealEnergy_nonneg solution t scale

theorem compactOpenSmoothDyadicPrefixSpectralDissipationMass_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicPrefixSpectralDissipationMass
        solution ha hab hbT depth) volume a b := by
  unfold compactOpenSmoothDyadicPrefixSpectralDissipationMass
  have hsum := IntervalIntegrable.sum (Finset.range depth) (fun scale _hscale ↦
    compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
      solution ha hab hbT scale)
  have hfun :
      (∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicBandSpectralDissipationMass
          solution ha hab hbT scale) =
      fun time ↦ ∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicBandSpectralDissipationMass
          solution ha hab hbT scale time := by
    funext time
    rw [Finset.sum_apply]
  rw [← hfun]
  exact hsum

theorem compactOpenSmoothDyadicPrefixActualSignedWorkRate_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicPrefixActualSignedWorkRate
        solution ha hab hbT depth) volume a b := by
  unfold compactOpenSmoothDyadicPrefixActualSignedWorkRate
  have hsum := IntervalIntegrable.sum (Finset.range depth) (fun scale _hscale ↦
    compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
      solution ha hab hbT scale)
  have hfun :
      (∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicBandActualSignedWorkRate
          solution ha hab hbT scale) =
      fun time ↦ ∑ scale ∈ Finset.range depth,
        compactOpenSmoothDyadicBandActualSignedWorkRate
          solution ha hab hbT scale time := by
    funext time
    rw [Finset.sum_apply]
  rw [← hfun]
  exact hsum

theorem compactOpenSmoothDyadicPrefixClockedCoefficientMass_intervalIntegrable
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    IntervalIntegrable
      (compactOpenSmoothDyadicPrefixClockedCoefficientMass
        solution ha hab hbT depth) volume a b := by
  unfold compactOpenSmoothDyadicPrefixClockedCoefficientMass
  have hsum := IntervalIntegrable.sum (Finset.range depth) (fun scale _hscale ↦
    (compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
      solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))
  have hfun :
      (∑ scale ∈ Finset.range depth, fun time ↦
        (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time) =
      fun time ↦ ∑ scale ∈ Finset.range depth,
        (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time := by
    funext time
    rw [Finset.sum_apply]
  rw [← hfun]
  exact hsum

/-! ## The exact signed ledger -/

/-- The finite scale word satisfies one exact balance.  The nonlinear terms are integrated only
after their signed scale sum has been formed. -/
theorem openPeriodicSolutionOn_openSmoothDyadicPrefix_integrated_balance
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    openSmoothDyadicPrefixRealEnergy solution
        ⟨b, ha.trans_le hab, hbT⟩ depth +
        nu * ∫ time in a..b,
          compactOpenSmoothDyadicPrefixSpectralDissipationMass
            solution ha hab hbT depth time =
      openSmoothDyadicPrefixRealEnergy solution
          ⟨a, ha, hab.trans_lt hbT⟩ depth +
        ∫ time in a..b,
          compactOpenSmoothDyadicPrefixActualSignedWorkRate
            solution ha hab hbT depth time := by
  have hsum :
      (∑ scale ∈ Finset.range depth,
        (openSmoothDyadicBandRealEnergy solution
            ⟨b, ha.trans_le hab, hbT⟩ scale +
          nu * ∫ time in a..b,
            compactOpenSmoothDyadicBandSpectralDissipationMass
              solution ha hab hbT scale time)) =
      ∑ scale ∈ Finset.range depth,
        (openSmoothDyadicBandRealEnergy solution
            ⟨a, ha, hab.trans_lt hbT⟩ scale +
          ∫ time in a..b,
            compactOpenSmoothDyadicBandActualSignedWorkRate
              solution ha hab hbT scale time) := by
    apply Finset.sum_congr rfl
    intro scale _hscale
    exact openPeriodicSolutionOn_openSmoothDyadicBand_integrated_balance
      solution ha hab hbT scale
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp only [openSmoothDyadicPrefixRealEnergy,
    compactOpenSmoothDyadicPrefixSpectralDissipationMass,
    compactOpenSmoothDyadicPrefixActualSignedWorkRate]
  rw [intervalIntegral.integral_finsetSum (fun scale _hscale ↦
      compactOpenSmoothDyadicBandSpectralDissipationMass_intervalIntegrable
        solution ha hab hbT scale),
    intervalIntegral.integral_finsetSum (fun scale _hscale ↦
      compactOpenSmoothDyadicBandActualSignedWorkRate_intervalIntegrable
        solution ha hab hbT scale)]
  exact hsum

/-! ## Depth-uniform storage and parabolic clock payment -/

/-- Initial storage is paid by one depth-independent actual-slice receiver. -/
theorem openSmoothDyadicPrefixRealEnergy_le_fullCoefficientMass_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openSmoothDyadicPrefixRealEnergy solution t depth ≤
      (1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution t ^ 2 := by
  exact sum_openSmoothDyadicBandRealEnergy_le_fullCoefficientMass_sq
    solution t depth

/-- Pointwise, the parabolic clocked coefficient population is no larger than the spectral
dissipation of the same finite word. -/
theorem compactOpenSmoothDyadicPrefixClockedCoefficientMass_le_dissipation
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (depth : ℕ) (time : ℝ) :
    compactOpenSmoothDyadicPrefixClockedCoefficientMass
        solution ha hab hbT depth time ≤
      compactOpenSmoothDyadicPrefixSpectralDissipationMass
        solution ha hab hbT depth time := by
  unfold compactOpenSmoothDyadicPrefixClockedCoefficientMass
    compactOpenSmoothDyadicPrefixSpectralDissipationMass
  apply Finset.sum_le_sum
  intro scale _hscale
  exact four_pow_mul_openSmoothDyadicBandCoefficientMass_le_dissipation
    solution (compactInteriorTime ha hab hbT time) scale

/-- The one-copy linear spectral service dominates the parabolically clocked two-copy band
population.  One copy of a multiplier in `[0,1]` pays two copies, and the lower adjacent shell
clock pays every nonzero supported mode. -/
theorem four_pow_mul_openSmoothDyadicBandCoefficientMass_le_linearDissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    (4 : ℝ) ^ scale *
        openSmoothDyadicBandCoefficientMass solution t scale ≤
      openSmoothDyadicLinearBandSpectralDissipationMass solution t scale := by
  unfold openSmoothDyadicBandCoefficientMass
    openSmoothDyadicLinearBandSpectralDissipationMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro frequency _hfrequency
  by_cases hweight : dyadicHodgeBandWeight scale frequency = 0
  · simp [openFilteredVorticityCoefficient, hweight,
      complexVectorEuclideanSquare]
  · have hsupport :=
      mem_two_sharp_shells_of_dyadicHodgeBandWeight_ne_zero scale hweight
    have hmode : (4 : ℝ) ^ scale ≤ torusStokesEigenvalue frequency := by
      rw [Finset.mem_union] at hsupport
      rcases hsupport with hcurrent | hnext
      · exact (four_pow_le_dyadicShellClockCost scale).trans
          (dyadicShellClockCost_le_mode hcurrent)
      · have hpow : (4 : ℝ) ^ scale ≤ (4 : ℝ) ^ (scale + 1) := by
          exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ scale)
        exact hpow.trans <|
          (four_pow_le_dyadicShellClockCost (scale + 1)).trans
            (dyadicShellClockCost_le_mode hnext)
    have hweightBounds := dyadicHodgeBandWeight_mem_unitInterval scale frequency
    let square := complexVectorEuclideanSquare
      (openPeriodicVorticityFourierMode solution t frequency)
    have hsquare : 0 ≤ square := by
      dsimp [square, complexVectorEuclideanSquare]
      exact Finset.sum_nonneg fun component _hcomponent ↦
        Complex.normSq_nonneg _
    have hweightedMode :
        (4 : ℝ) ^ scale * dyadicHodgeBandWeight scale frequency ≤
          torusStokesEigenvalue frequency :=
      (mul_le_of_le_one_right (by positivity) hweightBounds.2).trans hmode
    unfold openFilteredVorticityCoefficient
    rw [complexVectorEuclideanSquare_real_smul]
    calc
      (4 : ℝ) ^ scale *
          (dyadicHodgeBandWeight scale frequency ^ 2 * square) =
        ((4 : ℝ) ^ scale * dyadicHodgeBandWeight scale frequency) *
          (dyadicHodgeBandWeight scale frequency * square) := by ring
      _ ≤ torusStokesEigenvalue frequency *
          (dyadicHodgeBandWeight scale frequency * square) :=
        mul_le_mul_of_nonneg_right hweightedMode
          (mul_nonneg hweightBounds.1 hsquare)
      _ = torusStokesEigenvalue frequency *
          dyadicHodgeBandWeight scale frequency * square := by ring

/-- **Depth-uniform compact scale--time payment.**  The initial storage no longer depends on the
number of crossed scales, and the nonlinear return is kept as one signed integral until the last
receiver.  Thus cancellation among bands is retained exactly. -/
theorem openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth : ℕ) :
    nu * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time ≤
      (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicPrefixActualSignedWorkRate
            solution ha hab hbT depth time| := by
  have hclockIntegral :
      (∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time) ≤
      ∫ time in a..b,
        compactOpenSmoothDyadicPrefixSpectralDissipationMass
          solution ha hab hbT depth time := by
    exact intervalIntegral.integral_mono_on hab
      (compactOpenSmoothDyadicPrefixClockedCoefficientMass_intervalIntegrable
        solution ha hab hbT depth)
      (compactOpenSmoothDyadicPrefixSpectralDissipationMass_intervalIntegrable
        solution ha hab hbT depth)
      (fun time _htime ↦
        compactOpenSmoothDyadicPrefixClockedCoefficientMass_le_dissipation
          solution ha hab hbT depth time)
  have hclockViscous := mul_le_mul_of_nonneg_left hclockIntegral hnu.le
  have hbalance := openPeriodicSolutionOn_openSmoothDyadicPrefix_integrated_balance
    solution ha hab hbT depth
  have hterminal := openSmoothDyadicPrefixRealEnergy_nonneg solution
    ⟨b, ha.trans_le hab, hbT⟩ depth
  have hinitial := openSmoothDyadicPrefixRealEnergy_le_fullCoefficientMass_sq
    solution ⟨a, ha, hab.trans_lt hbT⟩ depth
  have hwork := le_abs_self (∫ time in a..b,
    compactOpenSmoothDyadicPrefixActualSignedWorkRate
      solution ha hab hbT depth time)
  linarith

/-- **Phase-preserving depth-uniform clock payment.**  The stronger one-copy balance makes the
nonlinear term exactly the single cumulative boundary work to which the finite physical/transport
decomposition applies.  Absolute value is taken only after scale summation and time integration.
-/
theorem openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu)
    (depth : ℕ) :
    nu * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time ≤
      (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time| := by
  have hscale : ∀ scale ∈ Finset.range depth,
      (∫ time in a..b,
        (4 : ℝ) ^ scale *
          compactOpenSmoothDyadicBandCoefficientMass
            solution ha hab hbT scale time) ≤
      ∫ time in a..b,
        compactOpenSmoothDyadicLinearBandSpectralDissipationMass
          solution ha hab hbT scale time := by
    intro scale _hscale
    exact intervalIntegral.integral_mono_on hab
      ((compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
        solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))
      (compactOpenSmoothDyadicLinearBandSpectralDissipationMass_intervalIntegrable
        solution ha hab hbT scale)
      (fun time _htime ↦
        four_pow_mul_openSmoothDyadicBandCoefficientMass_le_linearDissipation
          solution (compactInteriorTime ha hab hbT time) scale)
  have hsum := Finset.sum_le_sum hscale
  have hclockIntegral :
      (∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time) ≤
      ∑ scale ∈ Finset.range depth,
        ∫ time in a..b,
          compactOpenSmoothDyadicLinearBandSpectralDissipationMass
            solution ha hab hbT scale time := by
    unfold compactOpenSmoothDyadicPrefixClockedCoefficientMass
    rw [intervalIntegral.integral_finsetSum (fun scale _hscale ↦
      (compactOpenSmoothDyadicBandCoefficientMass_intervalIntegrable
        solution ha hab hbT scale).const_mul ((4 : ℝ) ^ scale))]
    exact hsum
  have hclockViscous := mul_le_mul_of_nonneg_left hclockIntegral hnu.le
  have hboundary :=
    sum_openSmoothDyadicBandRealEnergy_add_linearDissipation_le_boundary
      solution ha hab hbT depth
  have hterminal : 0 ≤ ∑ scale ∈ Finset.range depth,
      openSmoothDyadicBandRealEnergy solution
        ⟨b, ha.trans_le hab, hbT⟩ scale :=
    Finset.sum_nonneg fun scale _hscale ↦
      openSmoothDyadicBandRealEnergy_nonneg solution
        ⟨b, ha.trans_le hab, hbT⟩ scale
  have hstorage :
      (linearMultiplierCoefficientStorage
        (smoothDyadicCumulativeBoundaryMultiplier depth)
        (smoothDyadicBandNativeAperture depth)
        (openPeriodicVorticityFourierMode solution
          ⟨a, ha, hab.trans_lt hbT⟩)).re ≤
      (1 / 2 : ℝ) *
        openPeriodicFullVorticityCoefficientMass solution
          ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 := by
    calc
      _ ≤ (1 / 2 : ℝ) *
          ∑ frequency ∈ smoothDyadicBandNativeAperture depth,
            complexVectorEuclideanSquare
              (openPeriodicVorticityFourierMode solution
                ⟨a, ha, hab.trans_lt hbT⟩ frequency) :=
        linearBoundaryStorage_le_finiteVorticityEnergy
          solution ⟨a, ha, hab.trans_lt hbT⟩ depth
      _ ≤ (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 :=
        mul_le_mul_of_nonneg_left
          (finiteVorticityEnergy_le_fullCoefficientMass_sq
            solution ⟨a, ha, hab.trans_lt hbT⟩
              (smoothDyadicBandNativeAperture depth)) (by norm_num)
  have hwork := le_abs_self (∫ time in a..b,
    compactOpenSmoothDyadicLinearBoundarySignedWorkRate
      solution ha hab hbT depth time)
  linarith

section Audit

#print axioms openPeriodicSolutionOn_openSmoothDyadicPrefix_integrated_balance
#print axioms openSmoothDyadicPrefixRealEnergy_le_fullCoefficientMass_sq
#print axioms compactOpenSmoothDyadicPrefixClockedCoefficientMass_le_dissipation
#print axioms four_pow_mul_openSmoothDyadicBandCoefficientMass_le_linearDissipation
#print axioms openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le
#print axioms openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork

end Audit

end Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger

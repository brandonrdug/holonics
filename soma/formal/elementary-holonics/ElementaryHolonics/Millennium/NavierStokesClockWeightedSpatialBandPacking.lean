import ElementaryHolonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
import ElementaryHolonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking

/-!
# Clock-weighted spatial packing of smooth dyadic vorticity bands

**[proved-derived; formal-checked]** The phase-bearing spatial supremum of one smooth vorticity
band is bounded by the square root of its *actual filtered aperture population* times the square
root of its actual coefficient-square mass.  This is a localized Bernstein estimate: the full
enstrophy population does not replace the filtered coefficients.

Multiplying the spatial band at scale `j` by `2⁻ʲ` pairs it with the parabolic coefficient clock
`4ʲ M_j`.  The conjugate density is `card_j / 16ʲ`.  Its three-dimensional aperture population is
bounded by `512 * 8ʲ`, so the density is summable and every finite prefix is at most `1024`.
Consequently the square of the clock-weighted spatial prefix is controlled uniformly in depth by
the clocked coefficient mass, and the signed scale--time ledger transports that control to one
cumulative linear boundary-work receiver.

**[open]** This is a negative-one-scale, clock-weighted `L²`-in-time packing.  It is not the
unweighted terminal `L¹` packing required by the literal continuation receiver.  The exact weight
defect and the cofinal frequency complement are retained below as one explicit reconstruction
fibre; no terminal regularity conclusion is asserted.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicScaleTimeLedger
open Soma.Holonics.Millennium.NavierStokesTerminalSmoothDyadicVorticityPacking
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesProjectedDyadicShellEvolution
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandIntegratedBalance
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearScaleBoundary
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

set_option maxHeartbeats 2400000

/-- The ambient product norm of a complex three-vector is paid by its coordinate Euclidean
square.  This bridges the synthesis norm to the quadratic band-energy receiver without changing
either norm convention. -/
theorem complexVectorNorm_sq_le_euclideanSquare (coefficient : ComplexVector) :
    ‖coefficient‖ ^ 2 ≤ complexVectorEuclideanSquare coefficient := by
  have hE : 0 ≤ complexVectorEuclideanSquare coefficient := by
    unfold complexVectorEuclideanSquare
    exact Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _
  have hnorm : ‖coefficient‖ ≤ Real.sqrt (complexVectorEuclideanSquare coefficient) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro component
    rw [Real.le_sqrt (norm_nonneg _) hE]
    unfold complexVectorEuclideanSquare
    rw [← Complex.normSq_eq_norm_sq]
    exact Finset.single_le_sum (fun index _hindex ↦ Complex.normSq_nonneg _)
      (Finset.mem_univ component)
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans_eq (Real.sq_sqrt hE)

theorem smoothDyadicBandNativeAperture_card_le_eight_geometric (scale : ℕ) :
    (smoothDyadicBandNativeAperture scale).card ≤ 512 * 8 ^ scale := by
  rw [smoothDyadicBandNativeAperture, card_frequencyCube,
    dyadicHodgeOuterCutoff_eq, dyadicRadius]
  have hp : 1 ≤ 2 ^ (scale + 2) := Nat.one_le_pow _ _ (by norm_num)
  have hbase : 2 * (2 ^ (scale + 2) - 1) + 1 ≤ 2 ^ (scale + 3) := by
    calc
      2 * (2 ^ (scale + 2) - 1) + 1 ≤ 2 * 2 ^ (scale + 2) := by omega
      _ = 2 ^ (scale + 3) := by
        calc
          2 * 2 ^ (scale + 2) = 2 ^ (scale + 2) * 2 := by omega
          _ = 2 ^ ((scale + 2) + 1) := (pow_succ _ _).symm
          _ = 2 ^ (scale + 3) := rfl
  have h8 : 8 ^ scale = (2 ^ scale) ^ 3 := by
    rw [show 8 = 2 ^ 3 by norm_num]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  calc
    (2 * (2 ^ (scale + 2) - 1) + 1) ^ 3 ≤ (2 ^ (scale + 3)) ^ 3 :=
      Nat.pow_le_pow_left hbase 3
    _ = 512 * 8 ^ scale := by
      rw [show scale + 3 = 3 + scale by omega, pow_add, mul_pow, h8]
      norm_num

theorem smoothDyadicClockDensity_le_geometric (scale : ℕ) :
    ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale ≤
      512 * ((1 : ℝ) / 2) ^ scale := by
  have hcast : ((smoothDyadicBandNativeAperture scale).card : ℝ) ≤
      512 * (8 : ℝ) ^ scale := by
    exact_mod_cast smoothDyadicBandNativeAperture_card_le_eight_geometric scale
  have h16 : 0 ≤ (16 : ℝ) ^ scale := by positivity
  calc
    ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale ≤
        (512 * (8 : ℝ) ^ scale) / (16 : ℝ) ^ scale :=
      div_le_div_of_nonneg_right hcast h16
    _ = 512 * ((1 : ℝ) / 2) ^ scale := by
      rw [mul_div_assoc, ← div_pow]
      norm_num

theorem summable_smoothDyadicClockDensity : Summable (fun scale : ℕ ↦
    ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) := by
  have hgeom : Summable (fun scale : ℕ ↦ 512 * ((1 : ℝ) / 2) ^ scale) :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 : ℝ) / 2‖ < 1)).mul_left 512
  exact Summable.of_nonneg_of_le
    (fun scale ↦ by positivity) smoothDyadicClockDensity_le_geometric hgeom

theorem smoothDyadicClockDensityPrefix_le (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
      ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) ≤ 1024 := by
  calc
    (∑ scale ∈ Finset.range depth,
      ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale) ≤
        ∑ scale ∈ Finset.range depth, 512 * ((1 : ℝ) / 2) ^ scale := by
      exact Finset.sum_le_sum fun scale _hscale ↦ smoothDyadicClockDensity_le_geometric scale
    _ ≤ ∑' scale : ℕ, 512 * ((1 : ℝ) / 2) ^ scale := by
      apply Summable.sum_le_tsum
      · intro scale _hscale
        positivity
      · exact (summable_geometric_of_norm_lt_one
          (by norm_num : ‖(1 : ℝ) / 2‖ < 1)).mul_left 512
    _ = 1024 := by
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 : ℝ) / 2‖ < 1)]
      norm_num

theorem openSmoothDyadicBandCoefficientMass_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    0 ≤ openSmoothDyadicBandCoefficientMass solution t scale := by
  unfold openSmoothDyadicBandCoefficientMass complexVectorEuclideanSquare
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    Finset.sum_nonneg fun component _hcomponent ↦ Complex.normSq_nonneg _

theorem openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_coefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (scale : ℕ) :
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale ≤
      Real.sqrt ((smoothDyadicBandNativeAperture scale).card : ℝ) *
        Real.sqrt (openSmoothDyadicBandCoefficientMass solution t scale) := by
  let modes := smoothDyadicBandNativeAperture scale
  let coefficient : SpatialFrequency → ComplexVector := fun frequency ↦
    openFilteredVorticityCoefficient solution t scale frequency
  have hcoefficient :
      (∑ frequency ∈ modes, ‖coefficient frequency‖ ^ 2) ≤
        openSmoothDyadicBandCoefficientMass solution t scale := by
    unfold openSmoothDyadicBandCoefficientMass
    apply Finset.sum_le_sum
    intro frequency _hfrequency
    simpa [coefficient] using complexVectorNorm_sq_le_euclideanSquare
      (openFilteredVorticityCoefficient solution t scale frequency)
  unfold openPeriodicSmoothDyadicVorticityBandSpatialSup
    openPeriodicSmoothDyadicVorticityBand
  apply (ContinuousMap.norm_le _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  intro q
  change ‖finiteFourierSynthesis coefficient modes q‖ ≤ _
  exact (norm_finiteFourierSynthesis_le_sqrt_card_mul_sqrt_sum_sq
    coefficient modes q).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hcoefficient)
        (Real.sqrt_nonneg _))

def openSmoothDyadicClockWeightedSpatialPrefix
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale /
      (2 : ℝ) ^ scale

def smoothDyadicClockDensityPrefix (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    ((smoothDyadicBandNativeAperture scale).card : ℝ) / (16 : ℝ) ^ scale

theorem openSmoothDyadicClockWeightedSpatialPrefix_sq_le_density_mul_clockedMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    openSmoothDyadicClockWeightedSpatialPrefix solution t depth ^ 2 ≤
      smoothDyadicClockDensityPrefix depth *
        (∑ scale ∈ Finset.range depth,
          (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale) := by
  unfold openSmoothDyadicClockWeightedSpatialPrefix smoothDyadicClockDensityPrefix
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro scale _hscale
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · intro scale _hscale
    exact mul_nonneg (by positivity) (openSmoothDyadicBandCoefficientMass_nonneg solution t scale)
  · intro scale _hscale
    have hmass := openSmoothDyadicBandCoefficientMass_nonneg solution t scale
    have hspatial := openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution t scale
    have hcard : 0 ≤ ((smoothDyadicBandNativeAperture scale).card : ℝ) := by positivity
    have hbernstein := openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_coefficientMass solution t scale
    have hsquare := pow_le_pow_left₀ hspatial hbernstein 2
    rw [mul_pow, Real.sq_sqrt hcard, Real.sq_sqrt hmass] at hsquare
    have h4 : (0 : ℝ) < (4 : ℝ) ^ scale := by positivity
    have h2 : ((2 : ℝ) ^ scale) ^ 2 = (4 : ℝ) ^ scale := by
      rw [show (4 : ℝ) = (2 : ℝ) * 2 by norm_num, mul_pow, pow_two]
    have h16 : (16 : ℝ) ^ scale = ((4 : ℝ) ^ scale) ^ 2 := by
      rw [show (16 : ℝ) = (4 : ℝ) * 4 by norm_num, mul_pow, pow_two]
    calc
      (openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale /
          (2 : ℝ) ^ scale) ^ 2 =
          openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale ^ 2 /
            (4 : ℝ) ^ scale := by
        rw [div_pow, h2]
      _ ≤ (((smoothDyadicBandNativeAperture scale).card : ℝ) *
          openSmoothDyadicBandCoefficientMass solution t scale) /
            (4 : ℝ) ^ scale := div_le_div_of_nonneg_right hsquare h4.le
      _ = (((smoothDyadicBandNativeAperture scale).card : ℝ) /
          (16 : ℝ) ^ scale) *
            ((4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale) := by
        rw [h16]
        field_simp [ne_of_gt h4]

theorem openSmoothDyadicClockWeightedSpatialPrefix_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    0 ≤ openSmoothDyadicClockWeightedSpatialPrefix solution t depth := by
  unfold openSmoothDyadicClockWeightedSpatialPrefix
  exact Finset.sum_nonneg fun scale _hscale ↦ div_nonneg
    (openPeriodicSmoothDyadicVorticityBandSpatialSup_nonneg solution t scale)
    (by positivity)

theorem openSmoothDyadicClockWeightedSpatialPrefix_le_sqrtDensity_mul_sqrtClockedMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    openSmoothDyadicClockWeightedSpatialPrefix solution t depth ≤
      Real.sqrt (smoothDyadicClockDensityPrefix depth) *
        Real.sqrt (∑ scale ∈ Finset.range depth,
          (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale) := by
  have hdensity : 0 ≤ smoothDyadicClockDensityPrefix depth := by
    unfold smoothDyadicClockDensityPrefix
    positivity
  have hclock : 0 ≤ ∑ scale ∈ Finset.range depth,
      (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale := by
    exact Finset.sum_nonneg fun scale _hscale ↦
      mul_nonneg (by positivity) (openSmoothDyadicBandCoefficientMass_nonneg solution t scale)
  calc
    openSmoothDyadicClockWeightedSpatialPrefix solution t depth =
        Real.sqrt (openSmoothDyadicClockWeightedSpatialPrefix solution t depth ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (openSmoothDyadicClockWeightedSpatialPrefix_nonneg solution t depth)]
    _ ≤ Real.sqrt (smoothDyadicClockDensityPrefix depth *
        (∑ scale ∈ Finset.range depth,
          (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale)) :=
      Real.sqrt_le_sqrt (openSmoothDyadicClockWeightedSpatialPrefix_sq_le_density_mul_clockedMass solution t depth)
    _ = Real.sqrt (smoothDyadicClockDensityPrefix depth) *
        Real.sqrt (∑ scale ∈ Finset.range depth,
          (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale) := by
      rw [Real.sqrt_mul hdensity]

theorem openSmoothDyadicClockWeightedSpatialPrefix_sq_le_uniformClockedMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    openSmoothDyadicClockWeightedSpatialPrefix solution t depth ^ 2 ≤
      1024 * (∑ scale ∈ Finset.range depth,
        (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale) := by
  have hclock : 0 ≤ ∑ scale ∈ Finset.range depth,
      (4 : ℝ) ^ scale * openSmoothDyadicBandCoefficientMass solution t scale := by
    exact Finset.sum_nonneg fun scale _hscale ↦
      mul_nonneg (by positivity) (openSmoothDyadicBandCoefficientMass_nonneg solution t scale)
  exact (openSmoothDyadicClockWeightedSpatialPrefix_sq_le_density_mul_clockedMass solution t depth).trans
    (mul_le_mul_of_nonneg_right (smoothDyadicClockDensityPrefix_le depth) hclock)

def openSmoothDyadicUnweightedSpatialPrefix
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale

def openSmoothDyadicClockWeightReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℝ :=
  ∑ scale ∈ Finset.range depth,
    (1 - ((2 : ℝ) ^ scale)⁻¹) *
      openPeriodicSmoothDyadicVorticityBandSpatialSup solution t scale

theorem openSmoothDyadicUnweightedSpatialPrefix_eq_clockWeighted_add_reconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    openSmoothDyadicUnweightedSpatialPrefix solution t depth =
      openSmoothDyadicClockWeightedSpatialPrefix solution t depth + openSmoothDyadicClockWeightReconstructionFiber solution t depth := by
  unfold openSmoothDyadicUnweightedSpatialPrefix openSmoothDyadicClockWeightedSpatialPrefix openSmoothDyadicClockWeightReconstructionFiber
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro scale _hscale
  field_simp
  ring

def openSmoothDyadicClockWeightedTerminalReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℝ :=
  openSmoothDyadicClockWeightReconstructionFiber solution t depth +
    openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth

theorem criticalVorticityRate_le_clockWeightedPrefix_add_reconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate.criticalVorticityRate
        solution t.1 ≤
      Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          openSmoothDyadicClockWeightedSpatialPrefix solution t depth +
          openSmoothDyadicClockWeightedTerminalReconstructionFiber solution t depth) := by
  have hbase := criticalVorticityRate_le_finiteSmoothWord_add_fiber solution t depth
  calc
    _ ≤ Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          openSmoothDyadicUnweightedSpatialPrefix solution t depth +
          openPeriodicSmoothDyadicVorticityReconstructionFiberNorm solution t depth) := by
      simpa [openSmoothDyadicUnweightedSpatialPrefix, add_assoc] using hbase
    _ = Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSup solution t +
          openSmoothDyadicClockWeightedSpatialPrefix solution t depth +
          openSmoothDyadicClockWeightedTerminalReconstructionFiber solution t depth) := by
      rw [openSmoothDyadicUnweightedSpatialPrefix_eq_clockWeighted_add_reconstructionFiber]
      unfold openSmoothDyadicClockWeightedTerminalReconstructionFiber
      ring

def compactOpenSmoothDyadicClockWeightedSpatialPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) (time : ℝ) : ℝ :=
  openSmoothDyadicClockWeightedSpatialPrefix solution (compactInteriorTime ha hab hbT time) depth

theorem continuous_openSmoothDyadicClockWeightedSpatialPrefix
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (depth : ℕ) :
    Continuous (fun t : Set.Ioo (0 : ℝ) T ↦ openSmoothDyadicClockWeightedSpatialPrefix solution t depth) := by
  unfold openSmoothDyadicClockWeightedSpatialPrefix
  apply continuous_finsetSum
  intro scale _hscale
  exact (continuous_openPeriodicSmoothDyadicVorticityBandSpatialSup solution scale).div_const _

theorem continuous_compactOpenSmoothDyadicClockWeightedSpatialPrefix
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    Continuous (compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth) :=
  (continuous_openSmoothDyadicClockWeightedSpatialPrefix solution depth).comp
    (continuous_compactInteriorTime ha hab hbT)

theorem openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_clockedMass
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (depth : ℕ) :
    (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth time ^ 2) ≤
      1024 * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time := by
  have hleft : IntervalIntegrable
      (fun time ↦ compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth time ^ 2)
      MeasureTheory.volume a b :=
    ((continuous_compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth).pow 2).intervalIntegrable a b
  have hright : IntervalIntegrable
      (fun time ↦ 1024 * compactOpenSmoothDyadicPrefixClockedCoefficientMass
        solution ha hab hbT depth time) MeasureTheory.volume a b :=
    (compactOpenSmoothDyadicPrefixClockedCoefficientMass_intervalIntegrable
      solution ha hab hbT depth).const_mul 1024
  have hmono :
      (∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth time ^ 2) ≤
      ∫ time in a..b,
        1024 * compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time := by
    exact intervalIntegral.integral_mono_on hab hleft hright fun time _htime ↦ by
      simpa [compactOpenSmoothDyadicClockWeightedSpatialPrefix,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass,
        compactOpenSmoothDyadicBandCoefficientMass] using
        openSmoothDyadicClockWeightedSpatialPrefix_sq_le_uniformClockedMass solution
          (compactInteriorTime ha hab hbT time) depth
  simpa only [intervalIntegral.integral_const_mul] using hmono

theorem openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_linearBoundaryWork
    {T nu a b : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 < nu) (depth : ℕ) :
    nu * (∫ time in a..b,
      compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth time ^ 2) ≤
      1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) := by
  have hpacking := openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_clockedMass
    solution ha hab hbT depth
  have hclock :=
    openPeriodicSolutionOn_integral_prefixClockedCoefficientMass_le_linearBoundaryWork
      solution ha hab hbT hnu depth
  calc
    nu * (∫ time in a..b,
        compactOpenSmoothDyadicClockWeightedSpatialPrefix solution ha hab hbT depth time ^ 2) ≤
      nu * (1024 * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time) :=
      mul_le_mul_of_nonneg_left hpacking hnu.le
    _ = 1024 * (nu * ∫ time in a..b,
        compactOpenSmoothDyadicPrefixClockedCoefficientMass
          solution ha hab hbT depth time) := by ring
    _ ≤ 1024 * ((1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨a, ha, hab.trans_lt hbT⟩ ^ 2 +
        |∫ time in a..b,
          compactOpenSmoothDyadicLinearBoundarySignedWorkRate
            solution ha hab hbT depth time|) :=
      mul_le_mul_of_nonneg_left hclock (by norm_num)

section Audit

#print axioms complexVectorNorm_sq_le_euclideanSquare
#print axioms smoothDyadicBandNativeAperture_card_le_eight_geometric
#print axioms summable_smoothDyadicClockDensity
#print axioms openPeriodicSmoothDyadicVorticityBandSpatialSup_le_sqrt_card_mul_sqrt_coefficientMass
#print axioms openSmoothDyadicClockWeightedSpatialPrefix_sq_le_density_mul_clockedMass
#print axioms openSmoothDyadicClockWeightedSpatialPrefix_sq_le_uniformClockedMass
#print axioms criticalVorticityRate_le_clockWeightedPrefix_add_reconstructionFiber
#print axioms openPeriodicSolutionOn_integral_clockWeightedSpatialPrefix_sq_le_linearBoundaryWork

end Audit

end Soma.Holonics.Millennium.NavierStokesClockWeightedSpatialBandPacking

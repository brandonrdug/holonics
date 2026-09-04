import ElementaryHolonics.Millennium.NavierStokesSharpDyadicH3Tail
import ElementaryHolonics.Millennium.NavierStokesClockedBandDensity

/-!
# Sharp dyadic `H³` tail in the clocked vorticity alternative

**[proved-derived]** This owner attaches the isotropic `O(N⁻¹)` reciprocal square mass to the
actual open-solution Jacobian and vorticity remainder.  Substitution into the exact clocked
low/high alternative gives the sharp high branch `O(N⁻¹/²) · ‖u(t)‖_H³`.

At the parabolic clock `M = (N+1)²`, squaring the high branch gives the exact population law
`N (N+1)⁴ ≤ C ‖u(t)‖_H³²`, hence the scale exponent `‖u(t)‖_H³ ≳ N⁵/² ≈ M⁵/⁴`.
This is an instantaneous alternative.  It supplies no time-integrated `H³` service law.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ENNReal lp

namespace Soma.Holonics.Millennium.NavierStokesSharpClockedBandAlternative

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockedBandDensity
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesSharpDyadicH3Tail
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Actual open-solution coefficient tail -/

/-- Native-vector specialization of the sharp generic coefficient tail. -/
theorem tsum_coordinate_mul_norm_nativeUnweightedComponent_compl_dyadicCube_le
    (state : PeriodicVectorWeightedSobolev 3) (component coordinate : Fin 3)
    (depth : ℕ) :
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        |(frequency.1 coordinate : ℝ)| *
          ‖nativeUnweightedComponent state component frequency.1‖) ≤
      Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
        ‖state component‖ := by
  let coeff := weightedSobolevCoefficients 3 (state component)
  have htail := tsum_coordinate_mul_norm_compl_dyadicCube_le
    coeff coordinate depth
  have hweighted : weightedSobolevThreeCoefficient coeff = state component := by
    change coefficientWeightedRealization 3
      (weightedSobolevCoefficients 3 (state component)) = state component
    exact coefficientWeightedRealization_weightedSobolevCoefficients 3
      (state component)
  simpa only [coeff, nativeUnweightedComponent, hweighted] using htail

/-- One actual Jacobian-entry coefficient tail has the sharp `N⁻¹/²` rate. -/
theorem tsum_norm_openPeriodicJacobianFourierMode_entry_compl_dyadicCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (component coordinate : Fin 3) (depth : ℕ) :
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) ≤
      (2 * Real.pi) *
        (Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) component‖) := by
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 u hu hperiodic
  have hmoment :=
    tsum_coordinate_mul_norm_nativeUnweightedComponent_compl_dyadicCube_le
      state component coordinate depth
  have hsummable : Summable fun frequency : FrequencyCubeComplement (dyadicRadius depth) ↦
      |(frequency.1 coordinate : ℝ)| *
        ‖nativeUnweightedComponent state component frequency.1‖ :=
    (summable_coordinate_mul_norm_nativeUnweightedComponent
      state component coordinate).subtype
        {frequency : SpatialFrequency |
          frequency ∉ frequencyCube (dyadicRadius depth)}
  have hmode : ∀ frequency : FrequencyCubeComplement (dyadicRadius depth),
      ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖ =
        (2 * Real.pi) *
          (|(frequency.1 coordinate : ℝ)| *
            ‖nativeUnweightedComponent state component frequency.1‖) := by
    intro frequency
    have hcoefficient := actualJacobianFourierMode_eq_multiplier
      u (hu.of_le (by norm_num)) hperiodic frequency.1 component coordinate
    change ‖actualJacobianFourierMode u (hu.of_le (by norm_num)) hperiodic
        frequency.1 component coordinate‖ = _
    rw [hcoefficient]
    have hunweighted := unweighted_smoothSliceVectorWeightedH3_apply
      u hu hperiodic component frequency.1
    change nativeUnweightedComponent state component frequency.1 = _ at hunweighted
    rw [hunweighted]
    simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I,
      Complex.norm_intCast]
    ring
  calc
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) =
        ∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
          (2 * Real.pi) *
            (|(frequency.1 coordinate : ℝ)| *
              ‖nativeUnweightedComponent state component frequency.1‖) := by
      apply tsum_congr
      exact hmode
    _ = (2 * Real.pi) *
        ∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
          |(frequency.1 coordinate : ℝ)| *
            ‖nativeUnweightedComponent state component frequency.1‖ :=
      hsummable.tsum_mul_left _
    _ ≤ (2 * Real.pi) *
        (Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
          ‖state component‖) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)

/-- All nine Jacobian faces share the sharp dyadic tail scale. -/
theorem openPeriodicJacobianCoefficientTailMass_frequencyDyadicCube_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (dyadicRadius depth)) ≤
      (2 * Real.pi) *
        Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ := by
  let state : PeriodicVectorWeightedSobolev 3 :=
    smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
  let factor : ℝ :=
    (2 * Real.pi) * Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹)
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  unfold openPeriodicJacobianCoefficientTailMass
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hfactor (norm_nonneg state))]
  intro component
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hfactor (norm_nonneg state))]
  intro coordinate
  have hsumNonneg :
      0 ≤ ∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖ :=
    tsum_nonneg fun _ ↦ norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg hsumNonneg]
  calc
    (∑' frequency : FrequencyCubeComplement (dyadicRadius depth),
        ‖openPeriodicJacobianFourierMode solution t frequency.1
          component coordinate‖) ≤
        (2 * Real.pi) *
          (Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
            ‖state component‖) :=
      tsum_norm_openPeriodicJacobianFourierMode_entry_compl_dyadicCube_le
        solution t component coordinate depth
    _ = factor * ‖state component‖ := by
      dsimp [factor]
      ring
    _ ≤ factor * ‖state‖ := by
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm state component) hfactor

/-! ## Sharp actual-vorticity high branch -/

/-- The actual vorticity cube-complement remainder has the sharp pointwise `N⁻¹/² H³` rate. -/
theorem norm_openPeriodicVorticityFrequencyRemainder_frequencyDyadicCube_le_sharpH3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    ‖openPeriodicVorticityFrequencyRemainder solution t
        (frequencyCube (dyadicRadius depth)) q‖ ≤
      6 * ((2 * Real.pi) *
        Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
  exact
    (norm_openPeriodicVorticityFrequencyRemainder_le_six_mul_jacobianTailMass
      solution t (frequencyCube (dyadicRadius depth)) q).trans
      (mul_le_mul_of_nonneg_left
        (openPeriodicJacobianCoefficientTailMass_frequencyDyadicCube_le
          solution t depth) (by norm_num))

/-- Sharp substitution into the collapsed clocked low/high inequality. -/
theorem criticalVorticityRate_le_dyadicCubeEnstrophy_add_sharpH3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (density : ℝ) (hdensity : 0 ≤ density)
    (hcount : ((((2 * dyadicRadius depth + 1) ^ 3 : ℕ) : ℝ)) ≤
      density * criticalVorticityRate solution t.1) :
    criticalVorticityRate solution t.1 ≤
      24 * density * periodicEnstrophy velocity t.1 +
        12 * Real.sqrt 3 * ((2 * Real.pi) *
          Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
  have hbase := criticalVorticityRate_le_cubeEnstrophy_add_frequencyRemainder
    solution t (dyadicRadius depth) density hdensity hcount
  let tailBound : ℝ := 6 * ((2 * Real.pi) *
    Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)
  have htailBound : 0 ≤ tailBound := by
    dsimp [tailBound]
    positivity
  have htailNorm :
      ‖openPeriodicVorticityFrequencyRemainder solution t
          (frequencyCube (dyadicRadius depth))‖ ≤ tailBound := by
    apply (ContinuousMap.norm_le _ htailBound).2
    intro q
    exact
      norm_openPeriodicVorticityFrequencyRemainder_frequencyDyadicCube_le_sharpH3Tail
        solution t depth q
  have hhighFactor : 0 ≤ 2 * Real.sqrt 3 := by positivity
  calc
    criticalVorticityRate solution t.1 ≤
        24 * density * periodicEnstrophy velocity t.1 +
          2 * Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t
              (frequencyCube (dyadicRadius depth))‖ := hbase
    _ ≤ 24 * density * periodicEnstrophy velocity t.1 +
          2 * Real.sqrt 3 * tailBound := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left htailNorm hhighFactor)
    _ = 24 * density * periodicEnstrophy velocity t.1 +
        12 * Real.sqrt 3 * ((2 * Real.pi) *
          Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
      dsimp [tailBound]
      ring

/-! ## Exact parabolic exponent -/

/-- At the dyadic parabolic clock, the low branch is paid only by enstrophy, while the high branch
has the sharp `N⁻¹/² H³` price. -/
theorem exists_parabolicDyadicFrequencyLength_le_enstrophy_or_sharpH3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ)
    (hclock : criticalVorticityRate solution t.1 =
      (dyadicRadius depth + 1 : ℝ) ^ 2) :
    (dyadicRadius depth + 1 : ℝ) ≤
        192 * periodicEnstrophy velocity t.1 ∨
      criticalVorticityRate solution t.1 / 2 ≤
        Real.sqrt 3 *
          (6 * ((2 * Real.pi) *
            Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
              ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
                (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
                (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)) := by
  obtain ⟨q, hlow | hhigh⟩ := exists_parabolicFrequencyLength_le_enstrophy_or_high
    solution t (dyadicRadius depth) hclock
  · exact Or.inl hlow
  · refine Or.inr (hhigh.trans ?_)
    exact mul_le_mul_of_nonneg_left
      (norm_openPeriodicVorticityFrequencyRemainder_frequencyDyadicCube_le_sharpH3Tail
        solution t depth q) (Real.sqrt_nonneg 3)

/-- Squared form of the sharp high branch.  The factor on the left is `N M²`; under
`M=(N+1)²` this is the exact fifth-power population `N(N+1)⁴`. -/
theorem parabolicSharpHighBranch_forces_dyadic_fifthPower_H3
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ)
    (hclock : criticalVorticityRate solution t.1 =
      (dyadicRadius depth + 1 : ℝ) ^ 2)
    (hhigh : criticalVorticityRate solution t.1 / 2 ≤
      Real.sqrt 3 *
        (6 * ((2 * Real.pi) *
          Real.sqrt (250 * ((dyadicRadius depth : ℝ))⁻¹) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖))) :
    (dyadicRadius depth : ℝ) * (dyadicRadius depth + 1 : ℝ) ^ 4 ≤
      432000 * Real.pi ^ 2 *
        ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
          (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
          (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ ^ 2 := by
  let N : ℝ := dyadicRadius depth
  let H : ℝ :=
    ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖
  have hNpos : 0 < N := by
    dsimp [N, dyadicRadius]
    positivity
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hinvN : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hsqrtArg : 0 ≤ 250 * N⁻¹ := mul_nonneg (by norm_num) hinvN
  have hleft : 0 ≤ criticalVorticityRate solution t.1 / 2 :=
    div_nonneg (criticalVorticityRate_nonneg solution t.1) (by norm_num)
  have hright : 0 ≤ Real.sqrt 3 *
      (6 * ((2 * Real.pi) * Real.sqrt (250 * N⁻¹) * H)) := by
    dsimp [H]
    positivity
  have hsquare := (sq_le_sq₀ hleft hright).2 (by simpa [N, H] using hhigh)
  rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt hsqrtArg] at hsquare
  have hNinv : N * N⁻¹ = 1 := mul_inv_cancel₀ hNne
  rw [hclock] at hsquare
  have hscaled := mul_le_mul_of_nonneg_left hsquare
    (show 0 ≤ 4 * N by positivity)
  have hcancel :
      N * Real.pi ^ 2 * N⁻¹ * H ^ 2 * 432000 =
        Real.pi ^ 2 * H ^ 2 * 432000 := by
    calc
      N * Real.pi ^ 2 * N⁻¹ * H ^ 2 * 432000 =
          (N * N⁻¹) * (Real.pi ^ 2 * H ^ 2 * 432000) := by ring
      _ = Real.pi ^ 2 * H ^ 2 * 432000 := by rw [hNinv]; ring
  dsimp [N, H] at hsquare hscaled hNinv hcancel ⊢
  norm_num at hscaled
  ring_nf at hscaled ⊢
  exact hscaled.trans_eq hcancel

/-- The complete sharp parabolic alternative after eliminating the point receiver: either the
frequency length is paid by instantaneous enstrophy, or the instantaneous `H³` norm pays the
exact fifth-power dyadic population. -/
theorem parabolicDyadicFrequencyLength_le_enstrophy_or_fifthPower_H3
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ)
    (hclock : criticalVorticityRate solution t.1 =
      (dyadicRadius depth + 1 : ℝ) ^ 2) :
    (dyadicRadius depth + 1 : ℝ) ≤
        192 * periodicEnstrophy velocity t.1 ∨
      (dyadicRadius depth : ℝ) * (dyadicRadius depth + 1 : ℝ) ^ 4 ≤
        432000 * Real.pi ^ 2 *
          ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
            (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
            (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖ ^ 2 := by
  rcases exists_parabolicDyadicFrequencyLength_le_enstrophy_or_sharpH3Tail
    solution t depth hclock with hlow | hhigh
  · exact Or.inl hlow
  · exact Or.inr
      (parabolicSharpHighBranch_forces_dyadic_fifthPower_H3
        solution t depth hclock hhigh)

#print axioms openPeriodicJacobianCoefficientTailMass_frequencyDyadicCube_le
#print axioms norm_openPeriodicVorticityFrequencyRemainder_frequencyDyadicCube_le_sharpH3Tail
#print axioms criticalVorticityRate_le_dyadicCubeEnstrophy_add_sharpH3Tail
#print axioms exists_parabolicDyadicFrequencyLength_le_enstrophy_or_sharpH3Tail
#print axioms parabolicSharpHighBranch_forces_dyadic_fifthPower_H3
#print axioms parabolicDyadicFrequencyLength_le_enstrophy_or_fifthPower_H3

end Soma.Holonics.Millennium.NavierStokesSharpClockedBandAlternative

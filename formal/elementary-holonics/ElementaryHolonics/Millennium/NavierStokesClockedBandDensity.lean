import ElementaryHolonics.Millennium.NavierStokesVorticityBandBernsteinAlternative
import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime

/-!
# Clocked mode-density payment for the vorticity low/high alternative

**[proved-derived]** The finite-band alternative becomes an actual time-payment statement once
the admitted low-frequency population is no larger than a declared multiple of the critical
vorticity amplitude.  On that branch, one factor of the squared critical amplitude cancels and
the remaining amplitude is paid by enstrophy, whose time integral is already globally controlled
by the open energy identity.

In three spatial dimensions this payment requires a cube radius of order `M^(1/3)`, because its
mode population grows cubically.  A parabolic radius has `M ~ N^2`, while the cube population is
`N^3`; the final theorem records exactly that no fixed density constant can identify those two
counts.  Thus the high-frequency branch retains a genuine half-power reconstruction fibre rather
than disappearing through dimensional notation.
-/

noncomputable section

open MeasureTheory Real Set

namespace Soma.Holonics.Millennium.NavierStokesClockedBandDensity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative

/-! ## Global time payment of the low branch -/

/-- **[proved-derived; formal-checked]** The open energy identity pays the actual enstrophy
population over the whole open lifespan, including the terminal approach.  This is the exact
time-current used by the density-controlled low branch below. -/
theorem openPeriodicSolutionOn_periodicEnstrophy_integrableOn_and_integral_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntegrableOn (periodicEnstrophy velocity) (Ioo (0 : ℝ) T) volume ∧
      (∫ t in Ioo (0 : ℝ) T, periodicEnstrophy velocity t) ≤
        periodicKineticEnergy velocity 0 / nu := by
  have hmoment :=
    openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le
      solution hnu
  let moment : ℝ → ℝ := fun t ↦
    ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2
  have hmomentEq : ∀ t : ℝ, moment t = 2 * periodicEnstrophy velocity t :=
    integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy velocity
  have hscaled : IntegrableOn (fun t ↦ (1 / 2 : ℝ) * moment t)
      (Ioo (0 : ℝ) T) volume := hmoment.1.const_mul (1 / 2 : ℝ)
  have henstrophyIntegrable : IntegrableOn (periodicEnstrophy velocity)
      (Ioo (0 : ℝ) T) volume := by
    refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
    intro t _ht
    change (1 / 2 : ℝ) * moment t = periodicEnstrophy velocity t
    rw [hmomentEq]
    ring
  refine ⟨henstrophyIntegrable, ?_⟩
  calc
    (∫ t in Ioo (0 : ℝ) T, periodicEnstrophy velocity t) =
        ∫ t in Ioo (0 : ℝ) T, (1 / 2 : ℝ) * moment t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _ht
      change periodicEnstrophy velocity t = (1 / 2 : ℝ) * moment t
      rw [hmomentEq]
      ring
    _ = (1 / 2 : ℝ) * ∫ t in Ioo (0 : ℝ) T, moment t := by
      rw [integral_const_mul]
    _ ≤ (1 / 2 : ℝ) * (2 * (periodicKineticEnergy velocity 0 / nu)) := by
      exact mul_le_mul_of_nonneg_left hmoment.2 (by norm_num)
    _ = periodicKineticEnergy velocity 0 / nu := by ring

/-- The exact service-law rate paid by a mode population of density `density`. -/
def clockedModeDensityPaidRate
    (density : ℝ) (velocity : VelocityField) (t : ℝ) : ℝ :=
  24 * density * periodicEnstrophy velocity t

/-- The low-band service-law current is globally integrable on the whole open lifespan. -/
theorem integrableOn_clockedModeDensityPaidRate
    {T nu density : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntegrableOn (clockedModeDensityPaidRate density velocity)
      (Ioo (0 : ℝ) T) volume := by
  exact (openPeriodicSolutionOn_periodicEnstrophy_integrableOn_and_integral_le
    solution hnu).1.const_mul (24 * density)

/-- Its complete time cost is bounded by the initial kinetic budget divided by viscosity. -/
theorem integral_clockedModeDensityPaidRate_le
    {T nu density : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hdensity : 0 ≤ density) :
    (∫ t in Ioo (0 : ℝ) T, clockedModeDensityPaidRate density velocity t) ≤
      24 * density * (periodicKineticEnergy velocity 0 / nu) := by
  have hbase :=
    (openPeriodicSolutionOn_periodicEnstrophy_integrableOn_and_integral_le
      solution hnu).2
  unfold clockedModeDensityPaidRate
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hbase
    (mul_nonneg (by norm_num) hdensity)

/-- **[proved-derived; formal-checked]** If the declared finite mode population is at most
`density * M`, the low branch of the exact Bernstein alternative pays the critical amplitude
linearly from enstrophy.  The other branch retains the literal frequency remainder. -/
theorem exists_criticalVorticityRate_le_modeDensity_mul_enstrophy_or_high
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (density : ℝ)
    (hdensity : 0 ≤ density)
    (hcount : (modes.card : ℝ) ≤
      density * criticalVorticityRate solution t.1) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 ≤
          24 * density * periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ := by
  obtain ⟨q, hlow | hhigh⟩ :=
    exists_criticalVorticityRate_sq_le_card_mul_enstrophy_or_high
      solution t modes
  · refine ⟨q, Or.inl ?_⟩
    let M := criticalVorticityRate solution t.1
    let E := periodicEnstrophy velocity t.1
    have hM : 0 ≤ M := criticalVorticityRate_nonneg solution t.1
    have hE : 0 ≤ E := periodicEnstrophy_nonneg_receiver velocity t.1
    by_cases hMzero : M = 0
    · change M ≤ 24 * density * E
      rw [hMzero]
      positivity
    · have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hMzero)
      have hcountPay :
          24 * (modes.card : ℝ) * E ≤ 24 * (density * M) * E := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcount (by norm_num)) hE
      have hpaid : M ^ 2 ≤ 24 * (density * M) * E := by
        exact hlow.trans hcountPay
      dsimp only [M, E] at hpaid ⊢
      nlinarith
  · exact ⟨q, Or.inr hhigh⟩

/-- Cube specialization of the mode-density clock.  The hypothesis is the exact incidence count
that must be supplied by the chosen amplitude-to-length scale law. -/
theorem exists_criticalVorticityRate_le_cubeDensity_mul_enstrophy_or_high
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (density : ℝ) (hdensity : 0 ≤ density)
    (hcount : ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) ≤
      density * criticalVorticityRate solution t.1) :
    ∃ q : SpatialTorus,
      criticalVorticityRate solution t.1 ≤
          24 * density * periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t
              (frequencyCube radius) q‖ := by
  apply exists_criticalVorticityRate_le_modeDensity_mul_enstrophy_or_high
    solution t (frequencyCube radius) density hdensity
  simpa [card_frequencyCube] using hcount

/-- The existential receiver point can be collapsed without losing its lineage: the complete
continuous-map norm of the exact frequency remainder pays the high branch.  This is an
unconditional pointwise inequality once the declared mode-density incidence law is supplied. -/
theorem criticalVorticityRate_le_enstrophy_add_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (density : ℝ)
    (hdensity : 0 ≤ density)
    (hcount : (modes.card : ℝ) ≤
      density * criticalVorticityRate solution t.1) :
    criticalVorticityRate solution t.1 ≤
      24 * density * periodicEnstrophy velocity t.1 +
        2 * Real.sqrt 3 *
          ‖openPeriodicVorticityFrequencyRemainder solution t modes‖ := by
  obtain ⟨q, hlow | hhigh⟩ :=
    exists_criticalVorticityRate_le_modeDensity_mul_enstrophy_or_high
      solution t modes density hdensity hcount
  · exact hlow.trans (le_add_of_nonneg_right (by positivity))
  · have hpoint :
        ‖openPeriodicVorticityFrequencyRemainder solution t modes q‖ ≤
          ‖openPeriodicVorticityFrequencyRemainder solution t modes‖ :=
      (openPeriodicVorticityFrequencyRemainder solution t modes).norm_coe_le_norm q
    have hhighNorm : criticalVorticityRate solution t.1 / 2 ≤
        Real.sqrt 3 *
          ‖openPeriodicVorticityFrequencyRemainder solution t modes‖ :=
      hhigh.trans (mul_le_mul_of_nonneg_left hpoint (Real.sqrt_nonneg 3))
    have hpaid : 0 ≤ 24 * density * periodicEnstrophy velocity t.1 :=
      mul_nonneg (mul_nonneg (by norm_num) hdensity)
        (periodicEnstrophy_nonneg_receiver velocity t.1)
    nlinarith

/-- Cube form of the collapsed paid-plus-high clock inequality. -/
theorem criticalVorticityRate_le_cubeEnstrophy_add_frequencyRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (density : ℝ) (hdensity : 0 ≤ density)
    (hcount : ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) ≤
      density * criticalVorticityRate solution t.1) :
    criticalVorticityRate solution t.1 ≤
      24 * density * periodicEnstrophy velocity t.1 +
        2 * Real.sqrt 3 *
          ‖openPeriodicVorticityFrequencyRemainder solution t
            (frequencyCube radius)‖ := by
  apply criticalVorticityRate_le_enstrophy_add_frequencyRemainder
    solution t (frequencyCube radius) density hdensity
  simpa [card_frequencyCube] using hcount

/-- The exact existing `H³` reconstruction fibre can be substituted for the high remainder.
This exposes, in one inequality, the globally payable enstrophy current and the still-unpaid
high-order tail current. -/
theorem criticalVorticityRate_le_cubeEnstrophy_add_H3Tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (density : ℝ) (hdensity : 0 ≤ density)
    (hcount : ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) ≤
      density * criticalVorticityRate solution t.1) :
    criticalVorticityRate solution t.1 ≤
      24 * density * periodicEnstrophy velocity t.1 +
        12 * Real.sqrt 3 * ((2 * Real.pi) *
          Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
  have hbase := criticalVorticityRate_le_cubeEnstrophy_add_frequencyRemainder
    solution t radius density hdensity hcount
  let tailBound : ℝ := 6 * ((2 * Real.pi) *
    Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
      ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
        (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
        (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖)
  have htailBound : 0 ≤ tailBound := by
    dsimp [tailBound]
    positivity
  have htailNorm :
      ‖openPeriodicVorticityFrequencyRemainder solution t
          (frequencyCube radius)‖ ≤ tailBound := by
    apply (ContinuousMap.norm_le _ htailBound).2
    intro q
    exact norm_openPeriodicVorticityFrequencyRemainder_frequencyCube_le_H3Tail
      solution t radius q
  have hhighFactor : 0 ≤ 2 * Real.sqrt 3 := by positivity
  calc
    criticalVorticityRate solution t.1 ≤
        24 * density * periodicEnstrophy velocity t.1 +
          2 * Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t
              (frequencyCube radius)‖ := hbase
    _ ≤ 24 * density * periodicEnstrophy velocity t.1 +
          2 * Real.sqrt 3 * tailBound := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left htailNorm hhighFactor)
    _ = 24 * density * periodicEnstrophy velocity t.1 +
        12 * Real.sqrt 3 * ((2 * Real.pi) *
          Real.sqrt (jacobianTailScale radius * jacobianTailLatticeMass) *
            ‖smoothSliceVectorWeightedH3 (fun x ↦ velocity x t.1)
              (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)
              (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)‖) := by
      dsimp [tailBound]
      ring

/-! ## The discrete parabolic clock and its residual length -/

/-- **[proved-derived; formal-checked]** If the critical vorticity amplitude is clocked by the
parabolic law `M = L²` with integer spatial frequency length `L = radius + 1`, then the
three-dimensional low band pays only `L = sqrt M` from enstrophy.  The alternative retains the
entire high-frequency remainder.  This is the exact discrete length/time incidence behind the
otherwise informal phrase "the low branch loses a half power." -/
theorem exists_parabolicFrequencyLength_le_enstrophy_or_high
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ)
    (hclock : criticalVorticityRate solution t.1 = (radius + 1 : ℝ) ^ 2) :
    ∃ q : SpatialTorus,
      (radius + 1 : ℝ) ≤ 192 * periodicEnstrophy velocity t.1 ∨
        criticalVorticityRate solution t.1 / 2 ≤
          Real.sqrt 3 *
            ‖openPeriodicVorticityFrequencyRemainder solution t
              (frequencyCube radius) q‖ := by
  obtain ⟨q, hlow | hhigh⟩ :=
    exists_criticalVorticityRate_sq_le_cubeCount_mul_enstrophy_or_high
      solution t radius
  · refine ⟨q, Or.inl ?_⟩
    let L : ℝ := radius + 1
    let E : ℝ := periodicEnstrophy velocity t.1
    have hLpos : 0 < L := by
      dsimp [L]
      positivity
    have hE : 0 ≤ E := periodicEnstrophy_nonneg_receiver velocity t.1
    have hcount : ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) ≤ 8 * L ^ 3 := by
      dsimp [L]
      norm_num [Nat.cast_pow, Nat.cast_add, Nat.cast_mul]
      nlinarith [show 0 ≤ (radius : ℝ) by positivity,
        sq_nonneg (radius : ℝ)]
    have hpaid : L ^ 4 ≤ 192 * L ^ 3 * E := by
      have hlow' : L ^ 4 ≤
          24 * ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) * E := by
        rw [hclock] at hlow
        convert hlow using 1 <;> dsimp [L, E] <;> ring
      calc
        L ^ 4 ≤ 24 * ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) * E := hlow'
        _ ≤ 24 * (8 * L ^ 3) * E := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hcount (by norm_num)) hE
        _ = 192 * L ^ 3 * E := by ring
    have hfactor : 0 < L ^ 3 := pow_pos hLpos 3
    have hcancel : L ^ 3 * L ≤ L ^ 3 * (192 * E) := by
      nlinarith
    have hlength : L ≤ 192 * E := by
      by_contra hnot
      have hstrict : L ^ 3 * (192 * E) < L ^ 3 * L :=
        mul_lt_mul_of_pos_left (lt_of_not_ge hnot) hfactor
      exact (not_lt_of_ge hcancel) hstrict
    simpa [L, E] using hlength
  · exact ⟨q, Or.inr hhigh⟩

/-- **[proved-derived; formal-checked]** There is no uniform density constant that can pay a
three-dimensional cube population `~ N^3` from a parabolic vorticity amplitude `~ N^2`.
This is the exact residual half-power in the parabolic low branch. -/
theorem no_uniform_cubeModePopulation_le_density_mul_parabolicAmplitude :
    ¬ ∃ density : ℝ, ∀ radius : ℕ,
      ((((2 * radius + 1) ^ 3 : ℕ) : ℝ)) ≤
        density * (radius : ℝ) ^ 2 := by
  rintro ⟨density, hdensity⟩
  obtain ⟨radius : ℕ, hradius⟩ := exists_nat_gt (max 1 density)
  have hradiusPosNat : 0 < radius := by
    have hOne : (1 : ℝ) < radius :=
      lt_of_le_of_lt (le_max_left 1 density) hradius
    have hOneNat : 1 < radius := by exact_mod_cast hOne
    omega
  have hradiusPos : 0 < (radius : ℝ) := by exact_mod_cast hradiusPosNat
  have hdensityLt : density < (radius : ℝ) :=
    (le_max_right 1 density).trans_lt hradius
  have hmul : density * (radius : ℝ) ^ 2 <
      (radius : ℝ) * (radius : ℝ) ^ 2 :=
    mul_lt_mul_of_pos_right hdensityLt (sq_pos_of_pos hradiusPos)
  have hpow : (radius : ℝ) ^ 3 ≤ (2 * (radius : ℝ) + 1) ^ 3 := by
    gcongr
    nlinarith
  have hbound := hdensity radius
  norm_num [Nat.cast_pow, Nat.cast_add, Nat.cast_mul] at hbound
  nlinarith

#print axioms openPeriodicSolutionOn_periodicEnstrophy_integrableOn_and_integral_le
#print axioms integrableOn_clockedModeDensityPaidRate
#print axioms integral_clockedModeDensityPaidRate_le
#print axioms exists_criticalVorticityRate_le_modeDensity_mul_enstrophy_or_high
#print axioms exists_criticalVorticityRate_le_cubeDensity_mul_enstrophy_or_high
#print axioms criticalVorticityRate_le_enstrophy_add_frequencyRemainder
#print axioms criticalVorticityRate_le_cubeEnstrophy_add_frequencyRemainder
#print axioms criticalVorticityRate_le_cubeEnstrophy_add_H3Tail
#print axioms exists_parabolicFrequencyLength_le_enstrophy_or_high
#print axioms no_uniform_cubeModePopulation_le_density_mul_parabolicAmplitude

end Soma.Holonics.Millennium.NavierStokesClockedBandDensity

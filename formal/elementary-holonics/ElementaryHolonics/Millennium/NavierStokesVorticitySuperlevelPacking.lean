import ElementaryHolonics.Millennium.NavierStokesOverlapUniqueness
import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy
import ElementaryHolonics.Millennium.NavierStokesTorusVorticity

/-!
# Unconditional vorticity super-level packing on the periodic cell

Geometric depletion arguments ask how much of one spatial cell can carry vorticity above a
declared amplitude.  This file records the exact fixed-time receiver already forced by the
genuine vorticity population.

**[proved-derived; formal-checked]** On every admitted open-lifespan slice, a squared-vorticity
threshold times the measure of its super-level population is at most twice the periodic
enstrophy.  This is an unconditional packing bound for the actual solution.  It does not impose
direction coherence, a critical concentration profile, or terminal uniformity, and therefore is
not by itself a regularity theorem.
-/

noncomputable section

open MeasureTheory Set

namespace Soma.Holonics.Millennium.NavierStokesVorticitySuperlevelPacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- [definition] Real measure, inside one periodic cube, of the population whose squared
vorticity magnitude exceeds the addressed threshold. -/
def periodicSquaredVorticitySuperlevelMeasure
    (velocity : VelocityField) (t threshold : ℝ) : ℝ :=
  (volume.restrict unitCube).real
    {x : Space | threshold ≤ ‖vorticityField velocity x t‖ ^ 2}

/-- [definition] The same occupied cell population addressed by vorticity amplitude rather than
its square. -/
def periodicVorticityAmplitudeSuperlevelMeasure
    (velocity : VelocityField) (t level : ℝ) : ℝ :=
  (volume.restrict unitCube).real
    {x : Space | level ≤ ‖vorticityField velocity x t‖}

/-- [proved-derived; formal-checked] At a nonnegative amplitude the squared-threshold and
amplitude charts select exactly the same spatial population. -/
theorem periodicSquaredVorticitySuperlevelMeasure_sq_eq_amplitude
    (velocity : VelocityField) (t level : ℝ) (hlevel : 0 ≤ level) :
    periodicSquaredVorticitySuperlevelMeasure velocity t (level ^ 2) =
      periodicVorticityAmplitudeSuperlevelMeasure velocity t level := by
  unfold periodicSquaredVorticitySuperlevelMeasure
    periodicVorticityAmplitudeSuperlevelMeasure
  congr 2
  ext x
  exact sq_le_sq₀ hlevel (norm_nonneg _)

/-- [proved-derived; formal-checked] The squared vorticity population is integrable on the
periodic cube at every admitted open-lifespan time. -/
theorem integrableOn_norm_vorticity_sq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) :
    IntegrableOn (fun x : Space ↦ ‖vorticityField velocity x t‖ ^ 2) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have homega : ContDiff ℝ 1 (fun x ↦ vorticityField velocity x t) := by
    exact vorticityField_contDiff_one velocity t
      ((Soma.Holonics.Millennium.NavierStokesOverlapUniqueness.OpenPeriodicSolutionOn.velocitySpatialSmooth
        solution ht).of_le (WithTop.coe_le_coe.mpr le_top))
  exact homega.continuous.norm.pow 2 |>.continuousOn.integrableOn_compact hcubeCompact

/-- [proved-derived; formal-checked] Exact Chebyshev/Markov packing of the actual periodic
vorticity population. -/
theorem threshold_mul_periodicSquaredVorticitySuperlevelMeasure_le_two_mul_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) (threshold : ℝ) :
    threshold * periodicSquaredVorticitySuperlevelMeasure velocity t threshold ≤
      2 * periodicEnstrophy velocity t := by
  have hintegrable := integrableOn_norm_vorticity_sq solution ht
  have hnonneg : 0 ≤ᵐ[volume.restrict unitCube]
      (fun x : Space ↦ ‖vorticityField velocity x t‖ ^ 2) :=
    Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hnonneg hintegrable threshold
  simpa [periodicSquaredVorticitySuperlevelMeasure, periodicEnstrophy,
    periodicKineticEnergy, kineticEnergyDensity, integral_const_mul] using hmarkov

/-- [proved-derived; formal-checked] At a positive threshold the same receipt is an explicit
upper bound on occupied cell volume. -/
theorem periodicSquaredVorticitySuperlevelMeasure_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) {threshold : ℝ} (hthreshold : 0 < threshold) :
    periodicSquaredVorticitySuperlevelMeasure velocity t threshold ≤
      2 * periodicEnstrophy velocity t / threshold := by
  rw [le_div_iff₀ hthreshold]
  simpa [mul_comm] using
    threshold_mul_periodicSquaredVorticitySuperlevelMeasure_le_two_mul_enstrophy
      solution ht threshold

/-- [proved-derived; formal-checked] The physically addressed amplitude form of the cell-packing
law. -/
theorem level_sq_mul_periodicVorticityAmplitudeSuperlevelMeasure_le_two_mul_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ openTimeSlab T) {level : ℝ} (hlevel : 0 ≤ level) :
    level ^ 2 * periodicVorticityAmplitudeSuperlevelMeasure velocity t level ≤
      2 * periodicEnstrophy velocity t := by
  rw [← periodicSquaredVorticitySuperlevelMeasure_sq_eq_amplitude
    velocity t level hlevel]
  exact threshold_mul_periodicSquaredVorticitySuperlevelMeasure_le_two_mul_enstrophy
    solution ht (level ^ 2)

/-! ## One spatial cell crossed with one clock interval -/

/-- [definition] The compact interior space--time cell. -/
def periodicSpacetimeCell (source target : ℝ) : Set (Space × ℝ) :=
  unitCube ×ˢ Icc source target

/-- [definition] The exact second-moment population carried by one compact interior space--time
cell. -/
def periodicSpacetimeVorticitySecondMoment
    (velocity : VelocityField) (source target : ℝ) : ℝ :=
  ∫ z in periodicSpacetimeCell source target,
    ‖vorticityField velocity z.1 z.2‖ ^ 2
      ∂((volume : Measure Space).prod volume)

/-- [definition] Product-measure occupancy of the part of a compact interior cell above a
declared vorticity amplitude. -/
def periodicSpacetimeVorticityAmplitudeSuperlevelMeasure
    (velocity : VelocityField) (source target level : ℝ) : ℝ :=
  (((volume : Measure Space).prod volume).restrict
      (periodicSpacetimeCell source target)).real
    {z : Space × ℝ | level ≤ ‖vorticityField velocity z.1 z.2‖}

/-- [proved-derived; formal-checked] Joint smoothness makes the actual squared-vorticity
population integrable on every compact cell strictly inside the lifespan. -/
theorem integrableOn_norm_vorticity_sq_spacetimeCell
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target : ℝ} (hsource : 0 < source) (htarget : target < T) :
    IntegrableOn (fun z : Space × ℝ ↦
        ‖vorticityField velocity z.1 z.2‖ ^ 2)
      (periodicSpacetimeCell source target)
      ((volume : Measure Space).prod volume) := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcellCompact : IsCompact (periodicSpacetimeCell source target) := by
    exact hcubeCompact.prod isCompact_Icc
  have hsubset : periodicSpacetimeCell source target ⊆ Set.univ ×ˢ Ioo (0 : ℝ) T := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    exact ⟨Set.mem_univ x, lt_of_lt_of_le hsource ht.1, lt_of_le_of_lt ht.2 htarget⟩
  have hcontinuous : ContinuousOn
      (fun z : Space × ℝ ↦ ‖vorticityField velocity z.1 z.2‖ ^ 2)
      (periodicSpacetimeCell source target) :=
    ((openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).continuousOn
      |>.norm.pow 2).mono hsubset
  exact hcontinuous.integrableOn_compact hcellCompact

/-- [proved-derived; formal-checked] Unconditional four-dimensional packing: amplitude squared
times occupied space--time volume is bounded by the exact second moment transported through that
cell. -/
theorem level_sq_mul_periodicSpacetimeVorticityAmplitudeSuperlevelMeasure_le_secondMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {source target : ℝ} (hsource : 0 < source) (htarget : target < T)
    {level : ℝ} (hlevel : 0 ≤ level) :
    level ^ 2 *
        periodicSpacetimeVorticityAmplitudeSuperlevelMeasure
          velocity source target level ≤
      periodicSpacetimeVorticitySecondMoment velocity source target := by
  let μ : Measure (Space × ℝ) :=
    ((volume : Measure Space).prod volume).restrict
      (periodicSpacetimeCell source target)
  let f : Space × ℝ → ℝ := fun z ↦ ‖vorticityField velocity z.1 z.2‖ ^ 2
  have hintegrable : Integrable f μ :=
    integrableOn_norm_vorticity_sq_spacetimeCell solution hsource htarget
  have hnonneg : 0 ≤ᵐ[μ] f :=
    Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hnonneg hintegrable (level ^ 2)
  have hsets : {z : Space × ℝ | level ^ 2 ≤ f z} =
      {z : Space × ℝ | level ≤ ‖vorticityField velocity z.1 z.2‖} := by
    ext z
    exact sq_le_sq₀ hlevel (norm_nonneg _)
  rw [hsets] at hmarkov
  simpa [μ, f, periodicSpacetimeVorticityAmplitudeSuperlevelMeasure,
    periodicSpacetimeVorticitySecondMoment] using hmarkov

section Audit

#print axioms integrableOn_norm_vorticity_sq
#print axioms periodicSquaredVorticitySuperlevelMeasure_sq_eq_amplitude
#print axioms threshold_mul_periodicSquaredVorticitySuperlevelMeasure_le_two_mul_enstrophy
#print axioms periodicSquaredVorticitySuperlevelMeasure_le
#print axioms level_sq_mul_periodicVorticityAmplitudeSuperlevelMeasure_le_two_mul_enstrophy
#print axioms integrableOn_norm_vorticity_sq_spacetimeCell
#print axioms level_sq_mul_periodicSpacetimeVorticityAmplitudeSuperlevelMeasure_le_secondMoment

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticitySuperlevelPacking

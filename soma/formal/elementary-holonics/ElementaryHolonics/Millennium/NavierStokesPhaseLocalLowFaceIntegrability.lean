import ElementaryHolonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime

/-!
# The phase-local low vorticity face is globally time-integrable

**[proved-derived; formal-checked]** The retained low-frequency face in the phase-local dyadic
receiver is a fixed finite Fourier population.  Its spatial supremum is therefore paid by the
square root of the actual vorticity second moment.  On a finite open lifespan, the elementary
square-root inequality promotes the existing global second-moment estimate to integrability of
the low face all the way to the terminal approach.

This result is unconditional for positive-viscosity unforced admitted solutions.  It removes the
low face from the open terminal obstruction; it supplies no summability or terminal control for
the infinitely many dyadic shells.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityBandBernsteinAlternative

/- Keep the probability-Haar chart used by the Fourier source owners. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Continuity of the finite low face -/

/-- Each actual vorticity Fourier coefficient varies continuously on its native open time
carrier.  The proof integrates the jointly continuous descended world-tube against one fixed
torus character. -/
theorem continuous_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (k : SpatialFrequency) :
    Continuous (fun t : Ioo (0 : ℝ) T ↦
      openPeriodicVorticityFourierMode solution t k) := by
  let _ : LocallyCompactSpace (Ioo (0 : ℝ) T) := isOpen_Ioo.locallyCompactSpace
  have hjoint : Continuous (fun z : (Ioo (0 : ℝ) T) × SpatialTorus ↦
      UnitAddTorus.mFourier (-k) z.2 •
        complexifySpace (torusVorticityWorldTube solution z)) :=
    ((UnitAddTorus.mFourier (-k)).continuous.comp continuous_snd).smul
      (continuous_complexifySpace.comp (torusVorticityWorldTube solution).continuous)
  have hintegral := continuous_parametric_integral_of_continuous
    (X := Ioo (0 : ℝ) T) (Y := SpatialTorus) (E := ComplexVector)
    (μ := (volume : Measure SpatialTorus))
    (f := fun t q ↦ UnitAddTorus.mFourier (-k) q •
      complexifySpace (torusVorticityWorldTube solution (t, q)))
    (s := (Set.univ : Set SpatialTorus)) hjoint isCompact_univ
  simpa [openPeriodicVorticityFourierMode_eq_mFourierCoeff,
    UnitAddTorus.mFourierCoeff, complexTorusVorticitySlice,
    torusVorticityEvolution] using hintegral

/-- A fixed finite actual-vorticity band is a continuous path in the spatial continuous-map
norm. -/
theorem continuous_openPeriodicVorticityBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (modes : Finset SpatialFrequency) :
    Continuous (fun t : Ioo (0 : ℝ) T ↦
      openPeriodicVorticityBandProjector solution t modes) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  unfold openPeriodicVorticityBandProjector finiteFourierSynthesis
  exact continuous_finsetSum modes fun k _hk ↦
    ((UnitAddTorus.mFourier k).continuous.comp continuous_snd).smul
      ((continuous_openPeriodicVorticityFourierMode solution k).comp continuous_fst)

/-- Consequently the native retained low-face spatial supremum is continuous on the open
lifespan. -/
theorem continuous_openPeriodicVorticityLowSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (openPeriodicVorticityLowSpatialSup solution) := by
  exact continuous_norm.comp
    (continuous_openPeriodicVorticityBandProjector solution lowFrequencyModes)

/-! ## Real-time receiver and finite-band payment -/

/-- The real-time presentation of the actual low face, totalized by zero outside the admitted
open lifespan solely for integration. -/
def openPeriodicVorticityLowSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) T then
    openPeriodicVorticityLowSpatialSup solution ⟨t, ht⟩
  else 0

@[simp]
theorem openPeriodicVorticityLowSpatialSupRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    openPeriodicVorticityLowSpatialSupRate solution t =
      openPeriodicVorticityLowSpatialSup solution ⟨t, ht⟩ := by
  simp [openPeriodicVorticityLowSpatialSupRate, ht]

/-- The totalized low-face rate is continuous exactly on the admitted open lifespan. -/
theorem continuousOn_openPeriodicVorticityLowSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContinuousOn (openPeriodicVorticityLowSpatialSupRate solution) (Ioo 0 T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (continuous_openPeriodicVorticityLowSpatialSup solution).congr
  intro t
  simp [openPeriodicVorticityLowSpatialSupRate, t.2]

/-- The fixed low face is paid pointwise by square-root mode count times the square root of the
actual vorticity second moment. -/
theorem openPeriodicVorticityLowSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicVorticityLowSpatialSup solution t ≤
      Real.sqrt (lowFrequencyModes.card : ℝ) *
        Real.sqrt (∫ x in unitCube, ‖vorticityField velocity x t.1‖ ^ 2) := by
  unfold openPeriodicVorticityLowSpatialSup
  apply (ContinuousMap.norm_le _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2
  intro q
  rw [integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy]
  exact
    norm_openPeriodicVorticityBandProjector_le_sqrt_card_mul_sqrt_two_enstrophy
      solution t lowFrequencyModes q

/-- **[proved-derived; formal-checked]** For positive viscosity and zero force, the actual
phase-local low-frequency face is integrable over the entire open lifespan.  No terminal
vorticity-control premise is used. -/
theorem openPeriodicSolutionOn_lowSpatialSupRate_integrableOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntegrableOn (openPeriodicVorticityLowSpatialSupRate solution)
      (Ioo (0 : ℝ) T) volume := by
  let moment : ℝ → ℝ := fun t ↦
    ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2
  have hmoment : IntegrableOn moment (Ioo (0 : ℝ) T) volume :=
    (openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le
      solution hnu).1
  have hmajorant : IntegrableOn
      (fun t ↦ Real.sqrt (lowFrequencyModes.card : ℝ) * (1 + moment t))
      (Ioo (0 : ℝ) T) volume :=
    ((integrableOn_const (s := Ioo (0 : ℝ) T) (C := (1 : ℝ))
      (measure_Ioo_lt_top.ne)).add hmoment).const_mul
      (Real.sqrt (lowFrequencyModes.card : ℝ))
  apply Integrable.mono' hmajorant
    ((continuousOn_openPeriodicVorticityLowSpatialSupRate solution)
      |>.aestronglyMeasurable measurableSet_Ioo)
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards with t
  intro ht
  have hmomentNonneg : 0 ≤ moment t := integral_nonneg fun x ↦ sq_nonneg _
  have hsqrt : Real.sqrt (moment t) ≤ 1 + moment t := by
    nlinarith [Real.sq_sqrt hmomentNonneg,
      Real.sqrt_nonneg (moment t), sq_nonneg (Real.sqrt (moment t) - 1)]
  rw [Real.norm_of_nonneg (by
    rw [openPeriodicVorticityLowSpatialSupRate_eq solution ht]
    exact openPeriodicVorticityLowSpatialSup_nonneg solution ⟨t, ht⟩)]
  calc
    openPeriodicVorticityLowSpatialSupRate solution t ≤
        Real.sqrt (lowFrequencyModes.card : ℝ) * Real.sqrt (moment t) := by
      rw [openPeriodicVorticityLowSpatialSupRate_eq solution ht]
      exact openPeriodicVorticityLowSpatialSup_le_sqrt_card_mul_sqrt_secondMoment
        solution ⟨t, ht⟩
    _ ≤ Real.sqrt (lowFrequencyModes.card : ℝ) * (1 + moment t) :=
      mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)

/-- The same global result in the literal interval-integral interface used by the phase-local
terminal receiver. -/
theorem openPeriodicSolutionOn_lowSpatialSupRate_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntervalIntegrable (openPeriodicVorticityLowSpatialSupRate solution)
      volume 0 T := by
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le
    solution.terminal_pos.le).2
      (openPeriodicSolutionOn_lowSpatialSupRate_integrableOn solution hnu)

#print axioms continuous_openPeriodicVorticityFourierMode
#print axioms continuous_openPeriodicVorticityBandProjector
#print axioms openPeriodicSolutionOn_lowSpatialSupRate_integrableOn
#print axioms openPeriodicSolutionOn_lowSpatialSupRate_intervalIntegrable

end Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability

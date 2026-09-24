import ElementaryHolonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability

/-!
# Terminal spacetime packing of the actual dyadic vorticity shells

**[definition; formal-checked]** The terminal shell-packing receiver below measures the actual
signed dyadic vorticity shell only after spatial Fourier synthesis, then embeds its nonnegative
spatial supremum into `ℝ≥0∞`.  Its spacetime population is a Lebesgue `lintegral` of an `ENNReal`
series.  Consequently a divergent population remains `∞`; it cannot disappear through the
totalized value of a nonintegrable Bochner integral.

**[proved-derived; formal-checked]** Tonelli identifies this spacetime population with the sum of
the individual shell `lintegral`s.  If the population is finite, the shell contribution is
integrable on the whole open lifespan.  The separately proved unconditional low-frequency payment
then yields the existing one-field `OpenPeriodicPhaseLocalDiniReceipt`.

**[open]** No finiteness theorem for the terminal shell population is proved here.  That is exactly
the remaining scale-critical PDE obligation; this file constructs its robust receiver and the
passage to the already checked continuation criterion.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ENNReal Interval Topology

namespace Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability

/-! ## The totalized actual-shell current -/

/-- Real-time presentation of one actual signed-shell spatial supremum.  It is extended by zero
outside the admitted open lifespan solely so that every shell has one common real time carrier. -/
def openPeriodicVorticityDyadicShellSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (level : ℕ) (t : ℝ) : ℝ :=
  if ht : t ∈ Ioo (0 : ℝ) T then
    openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level
  else 0

@[simp]
theorem openPeriodicVorticityDyadicShellSpatialSupRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (level : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    openPeriodicVorticityDyadicShellSpatialSupRate solution level t =
      openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level := by
  simp [openPeriodicVorticityDyadicShellSpatialSupRate, ht]

theorem openPeriodicVorticityDyadicShellSpatialSupRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (level : ℕ) (t : ℝ) :
    0 ≤ openPeriodicVorticityDyadicShellSpatialSupRate solution level t := by
  by_cases ht : t ∈ Ioo (0 : ℝ) T
  · rw [openPeriodicVorticityDyadicShellSpatialSupRate_eq solution level ht]
    exact openPeriodicVorticityDyadicShellSpatialSup_nonneg solution ⟨t, ht⟩ level
  · simp [openPeriodicVorticityDyadicShellSpatialSupRate, ht]

/-- A fixed actual signed-shell spatial supremum varies continuously on the native open time
carrier. -/
theorem continuous_openPeriodicVorticityDyadicShellSpatialSup
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (level : ℕ) :
    Continuous (fun t : Ioo (0 : ℝ) T ↦
      openPeriodicVorticityDyadicShellSpatialSup solution t level) := by
  exact continuous_norm.comp
    (continuous_openPeriodicVorticityBandProjector solution
      (Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors.dyadicFrequencyShell level))

/-- The zero-totalized shell rate is continuous, and hence measurable, on the integration
aperture. -/
theorem continuousOn_openPeriodicVorticityDyadicShellSpatialSupRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (level : ℕ) :
    ContinuousOn (openPeriodicVorticityDyadicShellSpatialSupRate solution level)
      (Ioo (0 : ℝ) T) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply (continuous_openPeriodicVorticityDyadicShellSpatialSup solution level).congr
  intro t
  simp [openPeriodicVorticityDyadicShellSpatialSupRate, t.2]

/-- The nonnegative extended-real shell density.  The sum occurs after each signed shell has
reached its spatial receiver. -/
def openPeriodicVorticityTerminalDyadicShellDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : ℝ) : ℝ≥0∞ :=
  ∑' level : ℕ,
    ENNReal.ofReal (openPeriodicVorticityDyadicShellSpatialSupRate solution level t)

theorem aemeasurable_openPeriodicVorticityTerminalDyadicShellDensity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    AEMeasurable (openPeriodicVorticityTerminalDyadicShellDensity solution)
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  unfold openPeriodicVorticityTerminalDyadicShellDensity
  apply AEMeasurable.tsum
  intro level
  exact ((continuousOn_openPeriodicVorticityDyadicShellSpatialSupRate solution level)
    |>.aestronglyMeasurable measurableSet_Ioo).aemeasurable.ennreal_ofReal

/-! ## Robust spacetime packing and Tonelli -/

/-- The actual terminal spacetime dyadic shell population.  Because the codomain is `ℝ≥0∞`, a
nonintegrable shell family returns `∞` rather than the totalized zero of a Bochner integral. -/
def openPeriodicVorticityTerminalDyadicShellPacking
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : ℝ≥0∞ :=
  ∫⁻ t in Ioo (0 : ℝ) T,
    openPeriodicVorticityTerminalDyadicShellDensity solution t ∂volume

/-- **[proved-derived; formal-checked]** Tonelli exposes the exact individual-shell payment of the
terminal packing receiver. -/
theorem openPeriodicVorticityTerminalDyadicShellPacking_eq_tsum_lintegral
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    openPeriodicVorticityTerminalDyadicShellPacking solution =
      ∑' level : ℕ, ∫⁻ t in Ioo (0 : ℝ) T,
        ENNReal.ofReal
          (openPeriodicVorticityDyadicShellSpatialSupRate solution level t) ∂volume := by
  unfold openPeriodicVorticityTerminalDyadicShellPacking
    openPeriodicVorticityTerminalDyadicShellDensity
  rw [lintegral_tsum]
  intro level
  exact ((continuousOn_openPeriodicVorticityDyadicShellSpatialSupRate solution level)
    |>.aestronglyMeasurable measurableSet_Ioo).aemeasurable.ennreal_ofReal

/-- Finiteness of the robust terminal shell population.  This is the exact open PDE property, not
an assertion supplied by this file. -/
structure OpenPeriodicTerminalDyadicShellPackingReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) : Prop where
  packing_lt_top : openPeriodicVorticityTerminalDyadicShellPacking solution < ∞

/-! ## Passage to the phase-local Dini receipt -/

/-- On every admitted time slice, converting the extended-real density back to `ℝ` recovers the
actual summable real shell population exactly. -/
theorem openPeriodicVorticityTerminalDyadicShellDensity_toReal_eq_tsum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal =
      ∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level := by
  have hsummable : Summable (fun level : ℕ ↦
      openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level) :=
    summable_openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩
  have hnonneg : ∀ level : ℕ,
      0 ≤ openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level :=
    fun level ↦
      openPeriodicVorticityDyadicShellSpatialSup_nonneg solution ⟨t, ht⟩ level
  have hofReal := ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable
  have hsumNonneg : 0 ≤ ∑' level : ℕ,
      openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level :=
    tsum_nonneg hnonneg
  calc
    (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal =
        (ENNReal.ofReal (∑' level : ℕ,
          openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level)).toReal := by
      congr 1
      simpa [openPeriodicVorticityTerminalDyadicShellDensity,
        openPeriodicVorticityDyadicShellSpatialSupRate, ht] using hofReal.symm
    _ = ∑' level : ℕ,
        openPeriodicVorticityDyadicShellSpatialSup solution ⟨t, ht⟩ level :=
      ENNReal.toReal_ofReal hsumNonneg

/-- A finite robust shell-packing receipt makes the real shell density integrable on the whole
open lifespan. -/
theorem openPeriodicVorticityTerminalDyadicShellDensity_toReal_integrableOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (receipt : OpenPeriodicTerminalDyadicShellPackingReceipt solution) :
    IntegrableOn
      (fun t : ℝ ↦ (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal)
      (Ioo (0 : ℝ) T) volume := by
  apply integrable_toReal_of_lintegral_ne_top
    (aemeasurable_openPeriodicVorticityTerminalDyadicShellDensity solution)
  exact receipt.packing_lt_top.ne

/-- **[proved-derived; formal-checked]** Positive viscosity pays the finite low face
unconditionally.  Therefore finiteness of the nonnegative spacetime shell receiver is precisely
enough to construct the existing one-field phase-local Dini receipt. -/
theorem phaseLocalDiniReceipt_of_terminalDyadicShellPacking
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu)
    (receipt : OpenPeriodicTerminalDyadicShellPackingReceipt solution) :
    OpenPeriodicPhaseLocalDiniReceipt solution := by
  constructor
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le solution.terminal_pos.le]
  have hlow : IntegrableOn (openPeriodicVorticityLowSpatialSupRate solution)
      (Ioo (0 : ℝ) T) volume :=
    openPeriodicSolutionOn_lowSpatialSupRate_integrableOn solution hnu
  have hshell : IntegrableOn
      (fun t : ℝ ↦ (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal)
      (Ioo (0 : ℝ) T) volume :=
    openPeriodicVorticityTerminalDyadicShellDensity_toReal_integrableOn solution receipt
  have hmodel : IntegrableOn (fun t : ℝ ↦ Real.sqrt 3 *
      (openPeriodicVorticityLowSpatialSupRate solution t +
        (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal))
      (Ioo (0 : ℝ) T) volume :=
    (hlow.add hshell).const_mul (Real.sqrt 3)
  refine IntegrableOn.congr_fun hmodel ?_ measurableSet_Ioo
  intro t ht
  rw [openPeriodicVorticityPhaseLocalDiniPopulation]
  simp only [ht, dite_true]
  unfold openPeriodicVorticityPhaseLocalDiniPopulationOn
  rw [openPeriodicVorticityLowSpatialSupRate_eq solution ht,
    openPeriodicVorticityTerminalDyadicShellDensity_toReal_eq_tsum solution ht]

/-- Universal finiteness of the robust shell receiver would discharge the already formalized
critical-vorticity terminal-control object.  This theorem states only that exact implication. -/
theorem criticalVorticityTerminalControl_of_terminalDyadicShellPacking
    (packing : ∀ {T nu : ℝ} {initial : InitialVelocity}
      {velocity : VelocityField} {pressure : PressureField},
      0 < nu →
      InitialVelocityConditionPeriodic initial →
      (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
        OpenPeriodicTerminalDyadicShellPackingReceipt solution) :
    Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage.CriticalVorticityTerminalControl := by
  apply criticalVorticityTerminalControl_of_phaseLocalDini
  intro T nu initial velocity pressure hnu hinitial solution
  exact phaseLocalDiniReceipt_of_terminalDyadicShellPacking
    solution hnu (packing hnu hinitial solution)

section Audit

#print axioms openPeriodicVorticityTerminalDyadicShellPacking_eq_tsum_lintegral
#print axioms openPeriodicVorticityTerminalDyadicShellDensity_toReal_integrableOn
#print axioms phaseLocalDiniReceipt_of_terminalDyadicShellPacking
#print axioms criticalVorticityTerminalControl_of_terminalDyadicShellPacking

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking

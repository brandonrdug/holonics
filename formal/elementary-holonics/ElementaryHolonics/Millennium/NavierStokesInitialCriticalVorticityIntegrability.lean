import ElementaryHolonics.Millennium.NavierStokesPantographicTerminalShellReduction

/-!
# The compact initial face of the critical vorticity receiver

The pantographic terminal-shell reduction naturally begins at a strictly positive restart time.
This file pays the complementary initial face without adding a terminal hypothesis.  Smoothness
on every closed slab strictly inside the open lifespan supplies a uniform spatial-Jacobian bound;
curl is a fixed continuous-linear receiver, and periodicity transports the bound from the unit
cube to every Euclidean representative of the spatial torus.

Thus the literal critical-vorticity rate is interval-integrable on `[0,s]` for every `s < T`.
The theorem does not control the terminal tail `[s,T)`; that remains exactly the nonlinear
pantographic shell-packing obligation isolated by the preceding owner.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesInitialCriticalVorticityIntegrability

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOverlapUniqueness
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesPhaseLocalLowFaceIntegrability
open Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking
open Soma.Holonics.Millennium.NavierStokesPantographicTerminalShellReduction
open Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage

/-- **[proved-derived; formal-checked]** Every compact initial subslab has one uniform bound for
the actual critical vorticity receiver.  The bound is obtained before quotient collapse from the
closed-slab spatial Jacobian, then transported through curl and the periodic torus projection. -/
theorem exists_initial_criticalVorticityRate_bound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : 0 < s) (hsT : s < T) :
    ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) s,
      criticalVorticityRate solution t ≤ C := by
  let closed := solution.toClosedInterior hs hsT
  obtain ⟨K, hK⟩ :=
    PeriodicSolutionOn.exists_uniform_spatialJacobian_bound closed (b := s) le_rfl
  have hKnonneg : 0 ≤ K := by
    have hzeroCube : (0 : Space) ∈ unitCube := by
      unfold unitCube
      constructor
      · exact le_rfl
      · intro i
        norm_num
    exact (norm_nonneg _).trans (hK 0 ⟨le_rfl, hs.le⟩ 0 hzeroCube)
  refine ⟨‖derivativeCurlLinearMap‖ * K, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa [criticalVorticityRate, solution.terminal_pos] using
      mul_nonneg (norm_nonneg derivativeCurlLinearMap) hKnonneg
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htT : t < T := ht.2.trans_lt hsT
  rw [criticalVorticityRate_le_iff solution ⟨htpos, htT⟩]
  intro x
  let representative := fractionalUnitCubeRepresentative x
  have hrepresentative : representative ∈ unitCube :=
    fractionalUnitCubeRepresentative_mem x
  have hperiodic : IsOnePeriodic (fun y ↦ vorticityField velocity y t) :=
    vorticityField_isOnePeriodic velocity t
      (solution.velocityPeriodic t ⟨htpos.le, htT⟩)
  have hsame : vorticityField velocity x t =
      vorticityField velocity representative t := by
    exact isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun y ↦ vorticityField velocity y t) hperiodic
      (euclideanToSpatialTorus_fractionalUnitCubeRepresentative x).symm
  rw [hsame]
  change ‖derivativeCurlLinearMap
      (fderiv ℝ (fun y ↦ velocity y t) representative)‖ ≤
    ‖derivativeCurlLinearMap‖ * K
  exact (derivativeCurlLinearMap.le_opNorm
      (fderiv ℝ (fun y ↦ velocity y t) representative)).trans
    (mul_le_mul_of_nonneg_left
      (hK t ht representative hrepresentative) (norm_nonneg _))

/-- **[proved-derived; formal-checked]** The initial face of the exact BKM receiver is
unconditionally finite on every compact subinterval strictly before the open terminal time. -/
theorem intervalIntegrable_criticalVorticityRate_initial
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : 0 < s) (hsT : s < T) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.le]
  obtain ⟨C, hC⟩ := exists_initial_criticalVorticityRate_bound solution hs hsT
  have hconstant : IntegrableOn (fun _ : ℝ ↦ C) (Icc (0 : ℝ) s) volume :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  apply Integrable.mono' hconstant
    (criticalVorticityRate_measurable solution).aestronglyMeasurable.restrict
  apply (ae_restrict_iff' measurableSet_Icc).2
  filter_upwards with t
  intro ht
  rw [Real.norm_eq_abs, abs_of_nonneg (criticalVorticityRate_nonneg solution t)]
  exact hC t ht

/-! ## Gluing the initial face to the pantographic terminal tail -/

/-- A finite pantographic terminal population makes the actual shell-density real face
integrable on the same addressed tail.  The `ENNReal` source is retained until its finiteness has
been proved, so a divergent shell population cannot be totalized away. -/
theorem integrableOn_terminalDyadicShellDensity_toReal_of_pantographic
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ)
    (receipt :
      OpenPeriodicPantographicTerminalShellPackingReceipt solution hs depth) :
    IntegrableOn
      (fun t : ℝ ↦
        (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal)
      (Ioo s T) volume := by
  have hsubset : Ioo s T ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨hs.trans ht.1, ht.2⟩
  apply integrable_toReal_of_lintegral_ne_top
    ((aemeasurable_openPeriodicVorticityTerminalDyadicShellDensity solution).mono_measure
      (Measure.restrict_mono hsubset le_rfl))
  exact (openPeriodicVorticityTailDyadicShellPacking_lt_top_of_pantographic
    solution hnu hs hsT depth receipt).ne

/-- **[proved-derived; formal-checked, conditional]** The single finite nonlinear
pantographic scale--time population controls the literal critical-vorticity rate on its terminal
tail.  The unconditional low face and fixed earlier heat face have already been paid. -/
theorem intervalIntegrable_criticalVorticityRate_terminal_of_pantographic
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ)
    (receipt :
      OpenPeriodicPantographicTerminalShellPackingReceipt solution hs depth) :
    IntervalIntegrable (criticalVorticityRate solution) volume s T := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hsT.le]
  have hsubset : Ioo s T ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨hs.trans ht.1, ht.2⟩
  have hlow : IntegrableOn (openPeriodicVorticityLowSpatialSupRate solution)
      (Ioo s T) volume :=
    (openPeriodicSolutionOn_lowSpatialSupRate_integrableOn solution hnu).mono_set hsubset
  have hshell : IntegrableOn
      (fun t : ℝ ↦
        (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal)
      (Ioo s T) volume :=
    integrableOn_terminalDyadicShellDensity_toReal_of_pantographic
      solution hnu hs hsT depth receipt
  have hmodel : IntegrableOn (fun t : ℝ ↦ Real.sqrt 3 *
      (openPeriodicVorticityLowSpatialSupRate solution t +
        (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal))
      (Ioo s T) volume :=
    (hlow.add hshell).const_mul (Real.sqrt 3)
  apply Integrable.mono' hmodel
    (criticalVorticityRate_measurable solution).aestronglyMeasurable.restrict
  apply (ae_restrict_iff' measurableSet_Ioo).2
  filter_upwards with t
  intro ht
  have htOpen : t ∈ Ioo (0 : ℝ) T := hsubset ht
  have hlowNonneg : 0 ≤ openPeriodicVorticityLowSpatialSupRate solution t := by
    rw [openPeriodicVorticityLowSpatialSupRate_eq solution htOpen]
    exact openPeriodicVorticityLowSpatialSup_nonneg solution ⟨t, htOpen⟩
  have hmodelNonneg : 0 ≤ Real.sqrt 3 *
      (openPeriodicVorticityLowSpatialSupRate solution t +
        (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal) :=
    mul_nonneg (Real.sqrt_nonneg 3)
      (add_nonneg hlowNonneg ENNReal.toReal_nonneg)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (criticalVorticityRate_nonneg solution t)]
  calc
    criticalVorticityRate solution t ≤
        openPeriodicVorticityPhaseLocalDiniPopulation solution t :=
      criticalVorticityRate_le_phaseLocalDiniPopulation solution t
    _ = Real.sqrt 3 *
        (openPeriodicVorticityLowSpatialSupRate solution t +
          (openPeriodicVorticityTerminalDyadicShellDensity solution t).toReal) := by
      rw [openPeriodicVorticityPhaseLocalDiniPopulation]
      simp only [htOpen, dite_true]
      unfold openPeriodicVorticityPhaseLocalDiniPopulationOn
      rw [openPeriodicVorticityLowSpatialSupRate_eq solution htOpen,
        openPeriodicVorticityTerminalDyadicShellDensity_toReal_eq_tsum solution htOpen]

/-- **[proved-derived; formal-checked, conditional]** The compact initial face and the
pantographic terminal tail compose at the addressed restart time into the complete exact BKM
integral on `[0,T]`. -/
theorem intervalIntegrable_criticalVorticityRate_of_pantographic
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hsT : s < T) (depth : ℕ)
    (receipt :
      OpenPeriodicPantographicTerminalShellPackingReceipt solution hs depth) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T :=
  (intervalIntegrable_criticalVorticityRate_initial solution hs hsT).trans
    (intervalIntegrable_criticalVorticityRate_terminal_of_pantographic
      solution hnu hs hsT depth receipt)

/-- Universal finiteness of the one signed pantographic terminal population is now connected to
the repository's exact scale-critical finish-line receiver. -/
theorem criticalVorticityTerminalControl_of_pantographic
    (packing : ∀ {T nu : ℝ} {initial : InitialVelocity}
      {velocity : VelocityField} {pressure : PressureField},
      0 < nu →
      InitialVelocityConditionPeriodic initial →
      (solution :
        OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
        ∃ (s : ℝ) (depth : ℕ) (hs : 0 < s) (_hsT : s < T),
          OpenPeriodicPantographicTerminalShellPackingReceipt solution hs depth) :
    CriticalVorticityTerminalControl := by
  intro T nu initial velocity pressure hnu hinitial solution
  obtain ⟨s, depth, hs, hsT, receipt⟩ := packing hnu hinitial solution
  exact intervalIntegrable_criticalVorticityRate_of_pantographic
    solution hnu hs hsT depth receipt

section Audit

#print axioms exists_initial_criticalVorticityRate_bound
#print axioms intervalIntegrable_criticalVorticityRate_initial
#print axioms integrableOn_terminalDyadicShellDensity_toReal_of_pantographic
#print axioms intervalIntegrable_criticalVorticityRate_terminal_of_pantographic
#print axioms intervalIntegrable_criticalVorticityRate_of_pantographic
#print axioms criticalVorticityTerminalControl_of_pantographic

end Audit

end Soma.Holonics.Millennium.NavierStokesInitialCriticalVorticityIntegrability

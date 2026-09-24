import ElementaryHolonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
import ElementaryHolonics.Millennium.NavierStokesVorticityCrossSeamClock

/-!
# The own-mode Hermitian projective clock

**[proved-derived; formal-checked]**  At one compact Fourier address, the nonlinear vorticity
source is the sum of the actual vorticity-mode time jet and a viscous Stokes current parallel to
the contemporaneous vorticity coefficient.  The Hermitian phase receiver therefore returns the
same phase from the nonlinear source and from the time jet.

The proof is total at a zero vorticity coefficient: no reciprocal magnitude or nonvanishing
hypothesis is introduced.  The zero receiver keeps the complete source and time-jet occurrences,
and their equality follows from the fact that the Stokes current itself is then zero.  The final
theorem joins this exact phase identity to the existing `HasDerivAt` owner on the declared compact
interior interval.

This is an exact clock/reconstruction law only.  It supplies no norm estimate, time-integrated
phase payment, terminal bound, or continuation theorem.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2ModeReceiverRebase
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityCrossSeamClock

/-! ## Division-free radial invariance of the Hermitian phase -/

/-- Adding any current parallel to the receiver does not change its Hermitian phase.  The theorem
is total at `receiver = 0`; the zero fibre is handled as an actual case rather than by cancelling
the Hermitian square. -/
theorem modeHermitianPhase_add_smul_self
    (receiver source : ComplexVector) (scale : ℂ) :
    modeHermitianPhase receiver (source + scale • receiver) =
      modeHermitianPhase receiver source := by
  by_cases hreceiver : receiver = 0
  · subst receiver
    simp [modeHermitianPhase, modeHermitianAlignedAmplitude]
  · have hself : complexVectorHermitianPairing receiver receiver ≠ 0 := by
      rw [complexVectorHermitianPairing_self_eq]
      apply Complex.ofReal_ne_zero.mpr
      have hfunction : (fun component : Fin 3 ↦ receiver component) ≠ 0 := by
        simpa only using hreceiver
      obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hfunction
      exact (Finset.sum_pos'
        (fun index _hindex ↦ Complex.normSq_nonneg _)
        ⟨component, Finset.mem_univ component,
          Complex.normSq_pos.mpr hcomponent⟩).ne'
    have hpair :
        complexVectorHermitianPairing receiver (source + scale • receiver) =
          complexVectorHermitianPairing receiver source +
            scale * complexVectorHermitianPairing receiver receiver := by
      unfold complexVectorHermitianPairing
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
        Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      apply congrArg
      apply Finset.sum_congr rfl
      intro index _hindex
      ring
    unfold modeHermitianPhase modeHermitianAlignedAmplitude
    rw [hpair]
    ext component
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

/-! ## The actual compact Fourier source clock -/

/-- The viscous Stokes return is radial for the contemporaneous physical vorticity mode, so it
vanishes from the own-mode Hermitian phase.  This includes the zero-vorticity fibre and holds for
the complete compact source occurrence, not merely for a scalar reading of it. -/
theorem compactVorticityNonlinearMode_ownModeHermitianPhase_eq_timeJet
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) :
    modeHermitianPhase
        (physicalVorticityMode velocity frequency sourceTime)
        (compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime) =
      modeHermitianPhase
        (physicalVorticityMode velocity frequency sourceTime)
        (compactPhysicalVorticityModeTimeJet
          solution ha hab hbT frequency sourceTime) := by
  rw [compactVorticityNonlinearMode_eq_timeJet_add_stokes]
  exact modeHermitianPhase_add_smul_self _ _ _

/-- On the zero-own-vorticity fibre the complete compact nonlinear source equals the complete
time jet.  This is the reconstruction statement hidden by their common zero phase covector: the
source occurrence itself is retained rather than replaced by the scalar zero reading. -/
theorem compactVorticityNonlinearMode_eq_timeJet_of_zeroOwnMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ)
    (hzero : physicalVorticityMode velocity frequency sourceTime = 0) :
    compactVorticityNonlinearMode
        solution ha hab hbT frequency sourceTime =
      compactPhysicalVorticityModeTimeJet
        solution ha hab hbT frequency sourceTime := by
  have hsplit := compactVorticityNonlinearMode_eq_timeJet_add_stokes
    solution ha hab hbT frequency sourceTime
  rw [hzero] at hsplit
  simpa using hsplit

/-! ## The unclamped actual source occurrence -/

/-- At a strict interior occurrence, the actual nonlinear vorticity source and the literal
Stokes-ODE derivative have the same own-mode Hermitian phase. -/
theorem vorticityNonlinearMode_ownModeHermitianPhase_eq_actualTimeJet
    {T nu : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo (0 : ℝ) T) (frequency : SpatialFrequency) :
    modeHermitianPhase
        (physicalVorticityMode velocity frequency time.1)
        (vorticityNonlinearMode solution time frequency) =
      modeHermitianPhase
        (physicalVorticityMode velocity frequency time.1)
        ((((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
            physicalVorticityMode velocity frequency time.1) +
          vorticityNonlinearMode solution time frequency) := by
  rw [add_comm]
  exact (modeHermitianPhase_add_smul_self
    (physicalVorticityMode velocity frequency time.1)
    (vorticityNonlinearMode solution time frequency)
    (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ))).symm

/-- The exact derivative supplied by the actual open solution and its own-mode projective clock
are one joined return at every strict interior occurrence. -/
theorem openPeriodicSolutionOn_hasDerivAt_actualOwnModeHermitianPhaseClock
    {T nu : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (time : Ioo (0 : ℝ) T) (frequency : SpatialFrequency) :
    HasDerivAt
        (fun tau ↦ physicalVorticityMode velocity frequency tau)
        ((((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
            physicalVorticityMode velocity frequency time.1) +
          vorticityNonlinearMode solution time frequency) time.1 ∧
      modeHermitianPhase
          (physicalVorticityMode velocity frequency time.1)
          (vorticityNonlinearMode solution time frequency) =
        modeHermitianPhase
          (physicalVorticityMode velocity frequency time.1)
          ((((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
              physicalVorticityMode velocity frequency time.1) +
            vorticityNonlinearMode solution time frequency) := by
  exact ⟨openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes
      solution time frequency,
    vorticityNonlinearMode_ownModeHermitianPhase_eq_actualTimeJet
      solution time frequency⟩

/-- On an addressed compact interior event, the phase identity above is joined to the literal
derivative of the physical vorticity coefficient.  The first conjunct retains the derivative
occurrence and the second retains the complete source/time-jet phase equality. -/
theorem openPeriodicSolutionOn_hasDerivAt_ownModeHermitianPhaseClock
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (hsourceTime : sourceTime ∈ Icc a b) :
    HasDerivAt
        (fun tau ↦ physicalVorticityMode velocity frequency tau)
        (compactPhysicalVorticityModeTimeJet
          solution ha hab hbT frequency sourceTime) sourceTime ∧
      modeHermitianPhase
          (physicalVorticityMode velocity frequency sourceTime)
          (compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime) =
        modeHermitianPhase
          (physicalVorticityMode velocity frequency sourceTime)
          (compactPhysicalVorticityModeTimeJet
            solution ha hab hbT frequency sourceTime) := by
  exact ⟨
    openPeriodicSolutionOn_hasDerivAt_compactPhysicalVorticityMode
      solution ha hab hbT frequency hsourceTime,
    compactVorticityNonlinearMode_ownModeHermitianPhase_eq_timeJet
      solution ha hab hbT frequency sourceTime⟩

section Audit

#print axioms modeHermitianPhase_add_smul_self
#print axioms compactVorticityNonlinearMode_ownModeHermitianPhase_eq_timeJet
#print axioms compactVorticityNonlinearMode_eq_timeJet_of_zeroOwnMode
#print axioms vorticityNonlinearMode_ownModeHermitianPhase_eq_actualTimeJet
#print axioms openPeriodicSolutionOn_hasDerivAt_actualOwnModeHermitianPhaseClock
#print axioms openPeriodicSolutionOn_hasDerivAt_ownModeHermitianPhaseClock

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock

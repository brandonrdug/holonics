import ElementaryHolonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock
import Mathlib.Analysis.Calculus.TangentCone.DimOne
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.Order.LeftRightNhds

/-!
# The zero-set chronology of the own-mode projective clock

**[proved-derived; formal-checked]**  A differentiable path from real time into a normed real
vector space has zero derivative at every non-right-isolated point of each value fibre.  Hence the
points of its zero fibre carrying a nonzero derivative form a countable, Lebesgue-null population.
Equivalently, the derivative vanishes almost everywhere on the zero fibre.

No analyticity or unique-continuation hypothesis is used.  Isolated zero crossings are retained as
pointwise occurrences: their derivative, and therefore the physical source represented by that
derivative at a zero own mode, need not vanish.  They simply carry no interval mass.  The compact
physical-vorticity specialization below therefore removes the zero-own-mode fibre from an
absolutely continuous time payment up to a null population without replacing every pointwise
source occurrence by zero.

This is a chronology and reconstruction statement only.  It supplies no source estimate,
time-integrated bound, terminal control, or continuation theorem.
-/

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockZeroSet

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhysicalH2OwnModeProjectiveClock
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityCrossSeamClock

/-! ## A general differentiable zero-fibre theorem -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The time fibre on which a vector-valued clock path has the displayed value. -/
def valueFibre (path : ℝ → E) (value : E) : Set ℝ :=
  {time | path time = value}

/-- The zero fibre of a vector-valued clock path. -/
def zeroFibre (path : ℝ → E) : Set ℝ :=
  valueFibre path 0

/-- The addressed population of zero-fibre occurrences whose supplied time jet is nonzero. -/
def activeZeroCrossingsOn
    (domain : Set ℝ) (path timeJet : ℝ → E) : Set ℝ :=
  {time | time ∈ domain ∧ path time = 0 ∧ timeJet time ≠ 0}

/-- At a non-right-isolated zero occurrence, a supplied derivative is exactly zero.

The proof restricts both the path and the constant-zero path to the right-hand zero fibre.  A
nontrivial neighbourhood filter makes the clock occurrence an accumulation point; mathlib's
one-dimensional `AccPt.uniqueDiffWithinAt` then makes the two within-derivatives unique. -/
theorem hasDerivAt_eq_zero_of_mem_zeroFibre_of_rightAccumulation
    {path : ℝ → E} {timeJet : E} {time : ℝ}
    (hpath : HasDerivAt path timeJet time)
    (hzero : path time = 0)
    (hright : (𝓝[zeroFibre path ∩ Ioi time] time).NeBot) :
    timeJet = 0 := by
  let rightZeroFibre : Set ℝ := zeroFibre path ∩ Ioi time
  have htimeNotMem : time ∉ rightZeroFibre := by
    simp [rightZeroFibre]
  have hacc : AccPt time (𝓟 rightZeroFibre) := by
    rw [accPt_principal_iff_nhdsWithin,
      sdiff_singleton_eq_self htimeNotMem]
    exact hright
  have hunique : UniqueDiffWithinAt ℝ rightZeroFibre time :=
    hacc.uniqueDiffWithinAt
  apply hunique.eq_deriv rightZeroFibre hpath.hasDerivWithinAt
  apply (hasDerivWithinAt_const time rightZeroFibre (0 : E)).congr
  · intro other hother
    exact hother.1
  · exact hzero

/-- A zero occurrence with a nonzero supplied derivative is right-isolated in the zero fibre.
This retains ordinary isolated crossings pointwise rather than asserting that their jet vanishes.
-/
theorem zeroFibre_rightIsolated_of_hasDerivAt_of_ne_zero
    {path : ℝ → E} {timeJet : E} {time : ℝ}
    (hpath : HasDerivAt path timeJet time)
    (hzero : path time = 0)
    (htimeJet : timeJet ≠ 0) :
    𝓝[zeroFibre path ∩ Ioi time] time = ⊥ := by
  by_contra hfilter
  have hright : (𝓝[zeroFibre path ∩ Ioi time] time).NeBot :=
    ⟨hfilter⟩
  exact htimeJet
    (hasDerivAt_eq_zero_of_mem_zeroFibre_of_rightAccumulation
      hpath hzero hright)

/-- On any addressed time domain, the zero occurrences carrying a nonzero derivative are
countable.  Differentiability is required only at occurrences in that exceptional population. -/
theorem activeZeroCrossingsOn_countable
    {domain : Set ℝ} {path timeJet : ℝ → E}
    (hpath : ∀ time ∈ domain, HasDerivAt path (timeJet time) time) :
    (activeZeroCrossingsOn domain path timeJet).Countable := by
  apply (countable_setOfPred_isolated_right_within
    (s := zeroFibre path)).mono
  intro time htime
  exact ⟨htime.2.1,
    zeroFibre_rightIsolated_of_hasDerivAt_of_ne_zero
      (hpath time htime.1) htime.2.1 htime.2.2⟩

/-- The exceptional zero crossings have zero Lebesgue time mass. -/
theorem volume_activeZeroCrossingsOn_eq_zero
    {domain : Set ℝ} {path timeJet : ℝ → E}
    (hpath : ∀ time ∈ domain, HasDerivAt path (timeJet time) time) :
    volume (activeZeroCrossingsOn domain path timeJet) = 0 :=
  (activeZeroCrossingsOn_countable hpath).measure_zero volume

/-- A supplied derivative vanishes for almost every occurrence in the addressed zero fibre. -/
theorem timeJet_eq_zero_ae_on_zeroFibre
    {domain : Set ℝ} {path timeJet : ℝ → E}
    (hpath : ∀ time ∈ domain, HasDerivAt path (timeJet time) time) :
    ∀ᵐ time ∂volume,
      time ∈ domain ∧ path time = 0 → timeJet time = 0 := by
  rw [ae_iff]
  simpa only [Classical.not_imp, activeZeroCrossingsOn, and_assoc] using
    volume_activeZeroCrossingsOn_eq_zero hpath

/-- In particular, a globally differentiable path has zero derivative almost everywhere on its
zero fibre. -/
theorem derivative_eq_zero_ae_on_zeroFibre
    {path timeJet : ℝ → E}
    (hpath : ∀ time, HasDerivAt path (timeJet time) time) :
    ∀ᵐ time ∂volume, path time = 0 → timeJet time = 0 := by
  simpa only [mem_univ, true_and] using
    timeJet_eq_zero_ae_on_zeroFibre
      (domain := (Set.univ : Set ℝ)) (fun time _htime ↦ hpath time)

/-! ## The actual compact physical-vorticity clock -/

/-- The compact physical time jet is zero almost everywhere on the zero-own-vorticity fibre of
the declared time interval.  Isolated crossings remain outside this almost-everywhere conclusion.
-/
theorem compactPhysicalVorticityModeTimeJet_eq_zero_ae_on_zeroOwnMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) :
    ∀ᵐ sourceTime ∂volume,
      sourceTime ∈ Icc a b ∧
          physicalVorticityMode velocity frequency sourceTime = 0 →
        compactPhysicalVorticityModeTimeJet
          solution ha hab hbT frequency sourceTime = 0 := by
  apply timeJet_eq_zero_ae_on_zeroFibre
  intro sourceTime hsourceTime
  exact openPeriodicSolutionOn_hasDerivAt_compactPhysicalVorticityMode
    solution ha hab hbT frequency hsourceTime

/-- A nonzero compact nonlinear source at a zero own mode is retained as an isolated crossing.
At that occurrence the exact reconstruction theorem identifies the source with the time jet; it
does not identify either occurrence with zero. -/
theorem zeroOwnMode_nonzeroCompactSource_is_rightIsolated
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (hsourceTime : sourceTime ∈ Icc a b)
    (hzero : physicalVorticityMode velocity frequency sourceTime = 0)
    (hsource :
      compactVorticityNonlinearMode
        solution ha hab hbT frequency sourceTime ≠ 0) :
    𝓝[zeroFibre (fun time ↦ physicalVorticityMode velocity frequency time) ∩
        Ioi sourceTime] sourceTime = ⊥ := by
  have hsourceEqTimeJet :=
    compactVorticityNonlinearMode_eq_timeJet_of_zeroOwnMode
      solution ha hab hbT frequency sourceTime hzero
  apply zeroFibre_rightIsolated_of_hasDerivAt_of_ne_zero
    (openPeriodicSolutionOn_hasDerivAt_compactPhysicalVorticityMode
      solution ha hab hbT frequency hsourceTime) hzero
  rwa [← hsourceEqTimeJet]

/-- Consequently, nonzero compact sources on the zero-own-mode fibre form a countable
population.  This is the exact exceptional population retained by the projective clock. -/
theorem zeroOwnMode_nonzeroCompactSource_countable
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) :
    {sourceTime : ℝ |
      sourceTime ∈ Icc a b ∧
        physicalVorticityMode velocity frequency sourceTime = 0 ∧
          compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime ≠ 0}.Countable := by
  apply (countable_setOfPred_isolated_right_within
    (s := zeroFibre
      (fun time ↦ physicalVorticityMode velocity frequency time))).mono
  intro sourceTime hsourceTime
  exact ⟨hsourceTime.2.1,
    zeroOwnMode_nonzeroCompactSource_is_rightIsolated
      solution ha hab hbT frequency hsourceTime.1 hsourceTime.2.1 hsourceTime.2.2⟩

/-- The compact nonlinear source is therefore zero almost everywhere on the zero-own-mode
fibre, while its countable isolated-crossing reconstruction population remains explicit above. -/
theorem compactVorticityNonlinearMode_eq_zero_ae_on_zeroOwnMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) :
    ∀ᵐ sourceTime ∂volume,
      sourceTime ∈ Icc a b ∧
          physicalVorticityMode velocity frequency sourceTime = 0 →
        compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime = 0 := by
  rw [ae_iff]
  simpa only [Classical.not_imp, and_assoc] using
    (zeroOwnMode_nonzeroCompactSource_countable
      solution ha hab hbT frequency).measure_zero volume

section Audit

#print axioms hasDerivAt_eq_zero_of_mem_zeroFibre_of_rightAccumulation
#print axioms activeZeroCrossingsOn_countable
#print axioms derivative_eq_zero_ae_on_zeroFibre
#print axioms compactPhysicalVorticityModeTimeJet_eq_zero_ae_on_zeroOwnMode
#print axioms zeroOwnMode_nonzeroCompactSource_is_rightIsolated
#print axioms zeroOwnMode_nonzeroCompactSource_countable
#print axioms compactVorticityNonlinearMode_eq_zero_ae_on_zeroOwnMode

end Audit

end Soma.Holonics.Millennium.NavierStokesPhysicalH2ProjectiveClockZeroSet

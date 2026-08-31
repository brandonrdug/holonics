import ElementaryHolonics.Millennium.NavierStokesCriticalTimeReflection
import ElementaryHolonics.Millennium.NavierStokesOpenCompactWeightedPath

/-!
# Clocked pantographic swings of the actual nonlinear source

**[proved-derived; formal-checked]**  Fix an actual strict-interior target time `t` and an
elapsed length `r < t`.  The addressed pantographic clock samples the earlier times

`s j = t - r / 2^j`.

The signed source swings `N(s j) - N(s (j+1))` telescope before any Fourier coefficient norm
or triangle inequality is taken.  Every finite chain returns the original source increment
with one explicitly retained reconstruction fibre, `N(s m) - N(t)`.  Compact-interior native
`H3` continuity makes that fibre tend to zero in native `H2`, so the partial swing chain
converges to the literal `openSharpNonlinearSourceIncrement`.

This is an exact compact-interior clocked reconstruction.  It supplies no terminal-uniform
modulus, Dini estimate, or critical terminal receiver.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace Soma.Holonics.Millennium.NavierStokesClockedPantographicSourceSwing

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Addressed dyadic clock -/

/-- The absolute clock face at pantographic scale `scale`: the elapsed arm is compressed by
one dyadic factor at every swing. -/
def pantographicReflectedTime (target elapsed : ℝ) (scale : ℕ) : ℝ :=
  target - elapsed / (2 : ℝ) ^ scale

@[simp]
theorem pantographicReflectedTime_zero (target elapsed : ℝ) :
    pantographicReflectedTime target elapsed 0 = target - elapsed := by
  simp [pantographicReflectedTime]

/-- Every dyadic clock face remains in the original addressed interval `(0,T)`. -/
theorem pantographicReflectedTime_mem_Ioo
    {T target elapsed : ℝ} (htarget : target ∈ Ioo (0 : ℝ) T)
    (helapsed : 0 < elapsed) (helapsedTarget : elapsed < target) (scale : ℕ) :
    pantographicReflectedTime target elapsed scale ∈ Ioo (0 : ℝ) T := by
  have hpowPos : 0 < (2 : ℝ) ^ scale := pow_pos (by norm_num) _
  have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ scale := one_le_pow₀ (by norm_num)
  have hquotNonneg : 0 ≤ elapsed / (2 : ℝ) ^ scale :=
    div_nonneg helapsed.le hpowPos.le
  have hquotLe : elapsed / (2 : ℝ) ^ scale ≤ elapsed := by
    exact (div_le_iff₀ hpowPos).2 (le_mul_of_one_le_right helapsed.le hpowOne)
  constructor
  · simp only [pantographicReflectedTime]
    linarith
  · simp only [pantographicReflectedTime]
    linarith [htarget.2]

/-- The pantographic clock as an actual strict-interior time address. -/
def openSharpPantographicTime
    {T target elapsed : ℝ} (htarget : target ∈ Ioo (0 : ℝ) T)
    (helapsed : 0 < elapsed) (helapsedTarget : elapsed < target) (scale : ℕ) :
    Ioo (0 : ℝ) T :=
  ⟨pantographicReflectedTime target elapsed scale,
    pantographicReflectedTime_mem_Ioo htarget helapsed helapsedTarget scale⟩

@[simp]
theorem openSharpPantographicTime_coe
    {T target elapsed : ℝ} (htarget : target ∈ Ioo (0 : ℝ) T)
    (helapsed : 0 < elapsed) (helapsedTarget : elapsed < target) (scale : ℕ) :
    (openSharpPantographicTime htarget helapsed helapsedTarget scale : ℝ) =
      pantographicReflectedTime target elapsed scale :=
  rfl

/-- The same clock face addressed in the closed compact interval from the first source time to
the target.  This is the reconstruction chart used by compact native continuity. -/
def compactSharpPantographicTime
    {target elapsed : ℝ} (helapsed : 0 < elapsed) (scale : ℕ) :
    Icc (target - elapsed) target := by
  have hpowPos : 0 < (2 : ℝ) ^ scale := pow_pos (by norm_num) _
  have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ scale := one_le_pow₀ (by norm_num)
  have hquotNonneg : 0 ≤ elapsed / (2 : ℝ) ^ scale :=
    div_nonneg helapsed.le hpowPos.le
  have hquotLe : elapsed / (2 : ℝ) ^ scale ≤ elapsed := by
    exact (div_le_iff₀ hpowPos).2 (le_mul_of_one_le_right helapsed.le hpowOne)
  exact ⟨pantographicReflectedTime target elapsed scale, by
    constructor <;> simp only [pantographicReflectedTime] <;> linarith⟩

@[simp]
theorem compactSharpPantographicTime_coe
    {target elapsed : ℝ} (helapsed : 0 < elapsed) (scale : ℕ) :
    (compactSharpPantographicTime (target := target) helapsed scale : ℝ) =
      pantographicReflectedTime target elapsed scale :=
  rfl

/-- Dyadic clock faces converge to their addressed target time. -/
theorem tendsto_pantographicReflectedTime (target elapsed : ℝ) :
    Tendsto (pantographicReflectedTime target elapsed) atTop (nhds target) := by
  have hdyadic : Tendsto (fun scale : ℕ ↦ (((2 : ℝ)⁻¹) ^ scale)) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul hdyadic) :
      Tendsto (fun scale : ℕ ↦ target - elapsed * ((2 : ℝ)⁻¹) ^ scale)
        atTop (nhds (target - elapsed * 0)))
  simpa only [sub_zero, mul_zero] using hlimit.congr' (by
    filter_upwards [] with scale
    simp only [pantographicReflectedTime, div_eq_mul_inv, inv_pow])

/-- The compact time addresses converge to the target face of their retained interval. -/
theorem tendsto_compactSharpPantographicTime
    {target elapsed : ℝ} (helapsed : 0 < elapsed) :
    Tendsto (compactSharpPantographicTime (target := target) helapsed) atTop
      (nhds (⟨target, by constructor <;> linarith⟩ : Icc (target - elapsed) target)) := by
  rw [tendsto_subtype_rng]
  exact tendsto_pantographicReflectedTime target elapsed

/-! ## Actual source swings and finite reconstruction -/

/-- The exact projected nonlinear source at one addressed pantographic clock face. -/
def openSharpPantographicSource
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) (scale : ℕ) :
    PeriodicVectorWeightedSobolev 2 :=
  sharpNonlinearSource
    (openVelocityWeightedH3State solution
      (openSharpPantographicTime htarget helapsed helapsedTarget scale))

/-- One oriented source swing between successive pantographic time faces. -/
def openSharpPantographicSwing
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) (scale : ℕ) :
    PeriodicVectorWeightedSobolev 2 :=
  openSharpPantographicSource solution htarget helapsed helapsedTarget scale -
    openSharpPantographicSource solution htarget helapsed helapsedTarget (scale + 1)

/-- The finite oriented chain of source swings through scales strictly below `depth`. -/
def openSharpPantographicPartialChain
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) (depth : ℕ) :
    PeriodicVectorWeightedSobolev 2 :=
  ∑ scale ∈ Finset.range depth,
    openSharpPantographicSwing solution htarget helapsed helapsedTarget scale

/-- The unreconstructed terminal fibre after a finite pantographic chain. -/
def openSharpPantographicResidual
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) (depth : ℕ) :
    PeriodicVectorWeightedSobolev 2 :=
  openSharpPantographicSource solution htarget helapsed helapsedTarget depth -
    sharpNonlinearSource (openVelocityWeightedH3State solution ⟨target, htarget⟩)

/-- Each finite chain plus its retained terminal fibre reconstructs the original actual source
increment exactly, before any coefficient norm. -/
theorem openSharpPantographicFiniteReconstruction
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) (depth : ℕ) :
    openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
        (openSharpPantographicTime htarget helapsed helapsedTarget 0) =
      openSharpPantographicPartialChain solution htarget helapsed helapsedTarget depth +
        openSharpPantographicResidual solution htarget helapsed helapsedTarget depth := by
  induction depth with
  | zero =>
      simp [openSharpNonlinearSourceIncrement, openSharpPantographicPartialChain,
        openSharpPantographicResidual, openSharpPantographicSource]
  | succ depth ih =>
      rw [openSharpPantographicPartialChain, Finset.sum_range_succ]
      change
        openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
            (openSharpPantographicTime htarget helapsed helapsedTarget 0) =
          (openSharpPantographicPartialChain solution htarget helapsed helapsedTarget depth +
              openSharpPantographicSwing solution htarget helapsed helapsedTarget depth) +
            openSharpPantographicResidual solution htarget helapsed helapsedTarget (depth + 1)
      rw [ih]
      simp only [openSharpPantographicSwing, openSharpPantographicResidual]
      abel

/-! ## Vanishing reconstruction fibre and infinite chain return -/

/-- The actual sharp source sampled by the pantographic clock converges in native `H2` to its
target-time source.  Only compact-interior continuity is used. -/
theorem tendsto_openSharpPantographicSource
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) :
    Tendsto
      (openSharpPantographicSource solution htarget helapsed helapsedTarget)
      atTop
      (nhds (sharpNonlinearSource
        (openVelocityWeightedH3State solution ⟨target, htarget⟩))) := by
  have ha : 0 < target - elapsed := sub_pos.mpr helapsedTarget
  have hab : target - elapsed ≤ target := sub_le_self target helapsed.le
  have hstate := continuous_compactOpenVelocityWeightedH3State solution ha hab htarget.2
  have hsource : Continuous
      (fun state : PeriodicVectorWeightedSobolev 3 ↦
        weightedLerayDivergenceConvolutionContinuous state state) :=
    weightedLerayDivergenceConvolutionContinuous.continuous.clm_apply continuous_id
  have hcompact : Continuous
      (fun time : Icc (target - elapsed) target ↦
        sharpNonlinearSource
          (compactOpenVelocityWeightedH3State solution ha htarget.2 time)) :=
    hsource.comp hstate
  have htend := hcompact.continuousAt.tendsto.comp
    (tendsto_compactSharpPantographicTime helapsed)
  apply htend.congr'
  filter_upwards [] with scale
  rfl

/-- The explicit reconstruction fibre of the finite swing chain vanishes in native `H2`. -/
theorem tendsto_openSharpPantographicResidual_zero
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) :
    Tendsto
      (openSharpPantographicResidual solution htarget helapsed helapsedTarget)
      atTop (nhds 0) := by
  let targetSource : PeriodicVectorWeightedSobolev 2 :=
    sharpNonlinearSource (openVelocityWeightedH3State solution ⟨target, htarget⟩)
  have hconst : Tendsto (fun _ : ℕ ↦ targetSource) atTop (nhds targetSource) :=
    tendsto_const_nhds
  have hdifference :=
    (tendsto_openSharpPantographicSource solution htarget helapsed helapsedTarget).sub hconst
  change Tendsto
    (fun depth : ℕ ↦
      openSharpPantographicSource solution htarget helapsed helapsedTarget depth - targetSource)
    atTop (nhds 0)
  simpa only [targetSource, sub_self] using hdifference

/-- The infinite clocked pantographic chain returns the literal actual source increment.  The
chain remains signed throughout; the only discarded object in the limit is its displayed native
`H2` reconstruction fibre. -/
theorem tendsto_openSharpPantographicPartialChain_increment
    {T nu target elapsed : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (helapsed : 0 < elapsed)
    (helapsedTarget : elapsed < target) :
    Tendsto
      (openSharpPantographicPartialChain solution htarget helapsed helapsedTarget)
      atTop
      (nhds (openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
        (openSharpPantographicTime htarget helapsed helapsedTarget 0))) := by
  have hres :=
    tendsto_openSharpPantographicResidual_zero solution htarget helapsed helapsedTarget
  have htargetLimit : Tendsto
      (fun depth : ℕ ↦
        openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
            (openSharpPantographicTime htarget helapsed helapsedTarget 0) -
          openSharpPantographicResidual solution htarget helapsed helapsedTarget depth)
      atTop
      (nhds (openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
        (openSharpPantographicTime htarget helapsed helapsedTarget 0))) := by
    simpa using tendsto_const_nhds.sub hres
  apply htargetLimit.congr'
  filter_upwards [] with depth
  have hreconstruct :=
    openSharpPantographicFiniteReconstruction solution htarget helapsed helapsedTarget depth
  rw [hreconstruct]
  abel

section Audit

#print axioms openSharpPantographicFiniteReconstruction
#print axioms tendsto_openSharpPantographicResidual_zero
#print axioms tendsto_openSharpPantographicPartialChain_increment

end Audit

end Soma.Holonics.Millennium.NavierStokesClockedPantographicSourceSwing

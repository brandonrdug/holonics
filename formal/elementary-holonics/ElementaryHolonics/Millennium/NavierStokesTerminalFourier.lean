import ElementaryHolonics.Millennium.NavierStokesTerminalTrace

/-!
# Fourier constraints at the completed terminal face

**[conditional]** A Lipschitz tail in the continuous-field norm has the terminal trace constructed
by `NavierStokesTerminalTrace`.  This module asks which derivative-free Fourier consequences of
interior incompressibility survive that `C⁰` completion.

**[open]** The result sought here is only modewise longitudinal annihilation.  It does not promote
the terminal field to `C¹`, identify a pointwise divergence there, preserve an H³ jet, or construct
a restarted Navier--Stokes solution.
-/

noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesTerminalFourier

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTerminalTrace
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/- Keep the probability-Haar chart used by the torus Fourier owner. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- One complexified coordinate of a continuous real vector field on the genuine torus. -/
def complexTorusVelocityComponent
    (field : C(SpatialTorus, Space)) (component : Fin 3) : C(SpatialTorus, ℂ) where
  toFun q := (field q component : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj component).continuous.comp field.continuous)

/-- The genuine-torus Fourier coefficient of a continuous real vector field. -/
def continuousTorusVectorFourierCoeff
    (field : C(SpatialTorus, Space)) (k : SpatialFrequency) : ComplexVector :=
  fun component =>
    torusSpatialFourierCoeff (complexTorusVelocityComponent field component) k

/-- One Fourier component is nonexpanding from the uniform continuous-field norm. -/
theorem norm_continuousTorusVectorFourierCoeff_sub_le
    (field₁ field₂ : C(SpatialTorus, Space))
    (k : SpatialFrequency) (component : Fin 3) :
    ‖continuousTorusVectorFourierCoeff field₁ k component -
        continuousTorusVectorFourierCoeff field₂ k component‖ ≤ ‖field₁ - field₂‖ := by
  rw [continuousTorusVectorFourierCoeff, continuousTorusVectorFourierCoeff,
    ← torusSpatialFourierCoeff_sub]
  rw [torusSpatialFourierCoeff, UnitAddTorus.mFourierCoeff]
  have hpoint : ∀ᵐ q : SpatialTorus,
      ‖UnitAddTorus.mFourier (-k) q •
        (complexTorusVelocityComponent field₁ component -
          complexTorusVelocityComponent field₂ component) q‖ ≤ ‖field₁ - field₂‖ := by
    filter_upwards [] with q
    rw [norm_smul]
    have hcharacter : ‖UnitAddTorus.mFourier (-k) q‖ = 1 := by
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
        norm_prod, Circle.norm_coe, Finset.prod_const_one]
    rw [hcharacter, one_mul]
    change ‖complexTorusVelocityComponent field₁ component q -
      complexTorusVelocityComponent field₂ component q‖ ≤ ‖field₁ - field₂‖
    change ‖(field₁ q component : ℂ) - (field₂ q component : ℂ)‖ ≤ ‖field₁ - field₂‖
    rw [← Complex.ofReal_sub, Complex.norm_real]
    exact (PiLp.norm_apply_le (field₁ q - field₂ q) component).trans
      ((field₁ - field₂).norm_coe_le_norm q)
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := (volume : Measure SpatialTorus)) hpoint
  simpa using h

/-- Each fixed Fourier-coordinate receiver is `1`-Lipschitz. -/
theorem continuousTorusVectorFourierCoeff_component_lipschitz
    (k : SpatialFrequency) (component : Fin 3) :
    LipschitzWith 1
      (fun field : C(SpatialTorus, Space) =>
        continuousTorusVectorFourierCoeff field k component) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro field₁ field₂
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
    norm_continuousTorusVectorFourierCoeff_sub_le field₁ field₂ k component

/-- The complete fixed-mode Fourier receiver is continuous in the uniform field norm. -/
theorem continuous_continuousTorusVectorFourierCoeff (k : SpatialFrequency) :
    Continuous
      (fun field : C(SpatialTorus, Space) => continuousTorusVectorFourierCoeff field k) := by
  rw [continuous_pi_iff]
  intro component
  exact (continuousTorusVectorFourierCoeff_component_lipschitz k component).continuous

/-- Every controlled tail time is a strict interior time for the open solution. -/
def tailTimeToStrictInterior
    {a T : ℝ} (ha : 0 < a) (t : TailTime a T) : Ioo 0 T :=
  ⟨t.1, ha.trans_le t.2.1, t.2.2⟩

/-- The coefficient of the descended torus slice is the established coefficient of the actual
Euclidean solution slice. -/
theorem continuousTorusVectorFourierCoeff_tailSlice_eq
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (t : TailTime a T) (k : SpatialFrequency) :
    continuousTorusVectorFourierCoeff (tailTorusVelocitySlice solution ha t) k =
      openPeriodicVelocityFourierMode solution (tailTimeToStrictInterior ha t) k := by
  ext component
  rw [continuousTorusVectorFourierCoeff, openPeriodicVelocityFourierMode,
    vectorSpatialFourierCoeff_apply]
  unfold complexTorusVelocityComponent
  apply congrArg (fun field : SpatialTorus → ℂ => torusSpatialFourierCoeff field k)
  funext q
  obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_isOpenQuotientMap.surjective q
  rw [periodicTorusLift_projection]
  change ((tailTorusVelocitySlice solution ha t
    (euclideanToSpatialTorus x) component : ℝ) : ℂ) =
      ((velocity x t.1 component : ℝ) : ℂ)
  rw [tailTorusVelocitySlice_projection]

/-- Every strict-tail coefficient obeys the exact Fourier incompressibility constraint. -/
theorem complexDot_continuousTorusVectorFourierCoeff_tailSlice_eq_zero
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (t : TailTime a T) (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k)
      (continuousTorusVectorFourierCoeff (tailTorusVelocitySlice solution ha t) k) = 0 := by
  rw [continuousTorusVectorFourierCoeff_tailSlice_eq]
  exact complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (fun x => velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution
      (tailTimeToStrictInterior ha t).2)
    (solution.velocityPeriodic t.1
      ⟨(tailTimeToStrictInterior ha t).2.1.le, (tailTimeToStrictInterior ha t).2.2⟩)
    (fun x => solution.incompressible x t.1
      ⟨(tailTimeToStrictInterior ha t).2.1.le, (tailTimeToStrictInterior ha t).2.2⟩)
    k

/-- Uniform convergence of the complete strict tail passes through every fixed Fourier mode. -/
theorem TerminalTorusVelocityTrace.tendsto_continuousTorusVectorFourierCoeff
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control)
    (k : SpatialFrequency) :
    Tendsto
      (fun s : ClosedTailPreterminalTimes a T =>
        continuousTorusVectorFourierCoeff
          (closedPreterminalTorusVelocitySlice solution control.base_pos s) k)
      (Filter.comap ((↑) : ClosedTailPreterminalTimes a T → Icc a T)
        (𝓝 (closedTailTerminalTime a T control.base_lt_terminal.le)))
      (𝓝 (continuousTorusVectorFourierCoeff terminal.trace k)) := by
  exact (continuous_continuousTorusVectorFourierCoeff k).continuousAt.tendsto.comp
    terminal.tendsto_fullTail

/-- **Fourier incompressibility survives the `C⁰` terminal completion.**  Every terminal velocity
mode remains transverse to its integer frequency.  This is a weak, derivative-free consequence;
it is not pointwise divergence of the terminal field. -/
theorem TerminalTorusVelocityTrace.complexDot_terminalFourierCoeff_eq_zero
    {T nu a : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    {solution : OpenPeriodicSolutionOn T nu initial force velocity pressure}
    {control : UniformTorusVelocityTailControl (a := a) solution}
    (terminal : TerminalTorusVelocityTrace (a := a) solution control)
    (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k)
      (continuousTorusVectorFourierCoeff terminal.trace k) = 0 := by
  let terminalTime := closedTailTerminalTime a T control.base_lt_terminal.le
  let terminalFilter := Filter.comap
    ((↑) : ClosedTailPreterminalTimes a T → Icc a T) (𝓝 terminalTime)
  haveI : NeBot terminalFilter :=
    (closedTailPreterminalTimes_dense control.base_lt_terminal).comap_val_nhds_neBot terminalTime
  have hmode :=
    Soma.Holonics.Millennium.NavierStokesTerminalFourier.TerminalTorusVelocityTrace.tendsto_continuousTorusVectorFourierCoeff
      terminal k
  change Tendsto
    (fun s : ClosedTailPreterminalTimes a T =>
      continuousTorusVectorFourierCoeff
        (closedPreterminalTorusVelocitySlice solution control.base_pos s) k)
    terminalFilter
    (𝓝 (continuousTorusVectorFourierCoeff terminal.trace k)) at hmode
  have hcontinuousDot : Continuous
      (fun mode : ComplexVector => complexDot (complexFrequencyVector k) mode) := by
    exact continuous_const.dotProduct continuous_id
  have hdot := hcontinuousDot.continuousAt.tendsto.comp hmode
  change Tendsto
    (fun s : ClosedTailPreterminalTimes a T =>
      complexDot (complexFrequencyVector k)
        (continuousTorusVectorFourierCoeff
          (closedPreterminalTorusVelocitySlice solution control.base_pos s) k))
    terminalFilter
    (𝓝 (complexDot (complexFrequencyVector k)
      (continuousTorusVectorFourierCoeff terminal.trace k))) at hdot
  have hsource :
      (fun s : ClosedTailPreterminalTimes a T =>
        complexDot (complexFrequencyVector k)
          (continuousTorusVectorFourierCoeff
            (closedPreterminalTorusVelocitySlice solution control.base_pos s) k)) =
        (fun _ => (0 : ℂ)) := by
    funext s
    exact complexDot_continuousTorusVectorFourierCoeff_tailSlice_eq_zero
      solution control.base_pos (closedPreterminalToTailTime s) k
  rw [hsource] at hdot
  exact tendsto_nhds_unique hdot tendsto_const_nhds

section Audit

#print axioms norm_continuousTorusVectorFourierCoeff_sub_le
#print axioms continuous_continuousTorusVectorFourierCoeff
#print axioms continuousTorusVectorFourierCoeff_tailSlice_eq
#print axioms complexDot_continuousTorusVectorFourierCoeff_tailSlice_eq_zero
#print axioms TerminalTorusVelocityTrace.tendsto_continuousTorusVectorFourierCoeff
#print axioms TerminalTorusVelocityTrace.complexDot_terminalFourierCoeff_eq_zero

end Audit

end Soma.Holonics.Millennium.NavierStokesTerminalFourier

import ElementaryHolonics.Millennium.NavierStokesClockedPantographicSourceSwing
import ElementaryHolonics.Millennium.NavierStokesFrozenSharpSourceBoundary

/-!
# The signed pantographic source chain after heat/curl transport

**[proved-derived; formal-checked]**  This file supplies the compact elapsed-time chart needed
to pass the already-founded pantographic source swings through the actual heat/curl carrier and
then through the Bochner integral.  The chain remains signed until after elapsed integration.

At every finite depth the returned object has three exact faces:

* the transported finite swing population;
* its explicitly retained terminal reconstruction fibre; and
* the frozen target-time source, whose elapsed integral is the existing finite heat-boundary
  action `(I - S_h)(nu A)⁻¹ curl`.

No coefficient norm occurs in these identities.  No terminal-uniform estimate is asserted.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Interval NNReal Topology

namespace Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingChain

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesClockedPantographicSourceSwing
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFrozenSharpSourceBoundary
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## One continuous compact chart of the same pantographic source chain -/

/-- The elapsed clock `[0,h]` transported to the absolute source interval `[t-h,t]` at one
pantographic scale.  This is a continuous chart of the same time occurrence used by
`openSharpPantographicTime`. -/
def compactElapsedPantographicTime
    (target horizon : ℝ) (hhorizon : 0 ≤ horizon)
    (elapsed : Icc (0 : ℝ) horizon) (scale : ℕ) :
    Icc (target - horizon) target := by
  have hpowPos : 0 < (2 : ℝ) ^ scale := pow_pos (by norm_num) _
  have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ scale := one_le_pow₀ (by norm_num)
  have hquotNonneg : 0 ≤ elapsed.1 / (2 : ℝ) ^ scale :=
    div_nonneg elapsed.2.1 hpowPos.le
  have hquotLeElapsed : elapsed.1 / (2 : ℝ) ^ scale ≤ elapsed.1 := by
    exact (div_le_iff₀ hpowPos).2
      (le_mul_of_one_le_right elapsed.2.1 hpowOne)
  exact ⟨target - elapsed.1 / (2 : ℝ) ^ scale, by
    constructor
    · linarith [elapsed.2.2]
    · linarith⟩

@[simp]
theorem compactElapsedPantographicTime_coe
    (target horizon : ℝ) (hhorizon : 0 ≤ horizon)
    (elapsed : Icc (0 : ℝ) horizon) (scale : ℕ) :
    (compactElapsedPantographicTime target horizon hhorizon elapsed scale : ℝ) =
      target - elapsed.1 / (2 : ℝ) ^ scale :=
  rfl

theorem continuous_compactElapsedPantographicTime
    (target horizon : ℝ) (hhorizon : 0 ≤ horizon) (scale : ℕ) :
    Continuous
      (compactElapsedPantographicTime target horizon hhorizon · scale) := by
  apply Continuous.subtype_mk
  fun_prop

/-- The actual sharp nonlinear source on one compact elapsed pantographic face. -/
def compactElapsedOpenSharpPantographicSource
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (elapsed : Icc (0 : ℝ) horizon)
    (scale : ℕ) : PeriodicVectorWeightedSobolev 2 :=
  sharpNonlinearSource
    (compactOpenVelocityWeightedH3State solution hstart htarget
      (compactElapsedPantographicTime target horizon hhorizon elapsed scale))

theorem continuous_compactElapsedOpenSharpPantographicSource
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (scale : ℕ) :
    Continuous
      (compactElapsedOpenSharpPantographicSource
        solution hstart htarget hhorizon · scale) := by
  have hstate := continuous_compactOpenVelocityWeightedH3State
    solution hstart (sub_le_self target hhorizon) htarget
  have htime := continuous_compactElapsedPantographicTime
    target horizon hhorizon scale
  have hsource : Continuous
      (fun state : PeriodicVectorWeightedSobolev 3 ↦
        weightedLerayDivergenceConvolutionContinuous state state) :=
    weightedLerayDivergenceConvolutionContinuous.continuous.clm_apply continuous_id
  exact hsource.comp (hstate.comp htime)

/-- The source at the target face of the compact elapsed chart. -/
def compactElapsedOpenSharpTargetSource
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) : PeriodicVectorWeightedSobolev 2 :=
  sharpNonlinearSource
    (compactOpenVelocityWeightedH3State solution hstart htarget
      ⟨target, sub_le_self target hhorizon, le_rfl⟩)

/-- One signed source swing on the compact elapsed chart. -/
def compactElapsedOpenSharpPantographicSwing
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (elapsed : Icc (0 : ℝ) horizon)
    (scale : ℕ) : PeriodicVectorWeightedSobolev 2 :=
  compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon elapsed scale -
    compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon elapsed (scale + 1)

/-- The finite signed compact-elapsed swing chain. -/
def compactElapsedOpenSharpPantographicPartialChain
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (elapsed : Icc (0 : ℝ) horizon) : PeriodicVectorWeightedSobolev 2 :=
  ∑ scale ∈ Finset.range depth,
    compactElapsedOpenSharpPantographicSwing
      solution hstart htarget hhorizon elapsed scale

/-- The explicit source reconstruction fibre remaining at finite depth. -/
def compactElapsedOpenSharpPantographicResidual
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (elapsed : Icc (0 : ℝ) horizon) : PeriodicVectorWeightedSobolev 2 :=
  compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon elapsed depth -
    compactElapsedOpenSharpTargetSource
      solution hstart htarget hhorizon

/-- Every finite compact-elapsed chain reconstructs the literal source increment before any
heat transport or coefficient norm. -/
theorem compactElapsedOpenSharpPantographicFiniteReconstruction
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (elapsed : Icc (0 : ℝ) horizon) :
    compactElapsedOpenSharpPantographicSource
        solution hstart htarget hhorizon elapsed 0 -
      compactElapsedOpenSharpTargetSource
        solution hstart htarget hhorizon =
      compactElapsedOpenSharpPantographicPartialChain
          solution hstart htarget hhorizon depth elapsed +
        compactElapsedOpenSharpPantographicResidual
          solution hstart htarget hhorizon depth elapsed := by
  induction depth with
  | zero =>
      simp [compactElapsedOpenSharpPantographicPartialChain,
        compactElapsedOpenSharpPantographicResidual]
  | succ depth ih =>
      rw [compactElapsedOpenSharpPantographicPartialChain,
        Finset.sum_range_succ]
      change
        compactElapsedOpenSharpPantographicSource
            solution hstart htarget hhorizon elapsed 0 -
          compactElapsedOpenSharpTargetSource
            solution hstart htarget hhorizon =
          (compactElapsedOpenSharpPantographicPartialChain
              solution hstart htarget hhorizon depth elapsed +
            compactElapsedOpenSharpPantographicSwing
              solution hstart htarget hhorizon elapsed depth) +
          compactElapsedOpenSharpPantographicResidual
            solution hstart htarget hhorizon (depth + 1) elapsed
      rw [ih]
      simp only [compactElapsedOpenSharpPantographicSwing,
        compactElapsedOpenSharpPantographicResidual]
      abel

theorem continuous_compactElapsedOpenSharpPantographicSwing
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (scale : ℕ) :
    Continuous
      (compactElapsedOpenSharpPantographicSwing
        solution hstart htarget hhorizon · scale) :=
  (continuous_compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon scale).sub
    (continuous_compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon (scale + 1))

theorem continuous_compactElapsedOpenSharpPantographicPartialChain
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ) :
    Continuous
      (compactElapsedOpenSharpPantographicPartialChain
        solution hstart htarget hhorizon depth) := by
  unfold compactElapsedOpenSharpPantographicPartialChain
  apply continuous_finsetSum (Finset.range depth)
  intro scale _hscale
  exact continuous_compactElapsedOpenSharpPantographicSwing
    solution hstart htarget hhorizon scale

theorem continuous_compactElapsedOpenSharpPantographicResidual
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ) :
    Continuous
      (compactElapsedOpenSharpPantographicResidual
        solution hstart htarget hhorizon depth) := by
  unfold compactElapsedOpenSharpPantographicResidual
  exact (continuous_compactElapsedOpenSharpPantographicSource
    solution hstart htarget hhorizon depth).sub continuous_const

/-- The compact chart is exactly the earlier addressed pantographic source on every positive
elapsed face. -/
theorem compactElapsedOpenSharpPantographicSource_eq_open
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 < horizon) (elapsed : Icc (0 : ℝ) horizon)
    (helapsed : 0 < elapsed.1) (scale : ℕ) :
    compactElapsedOpenSharpPantographicSource
        solution hstart htarget hhorizon.le elapsed scale =
      openSharpPantographicSource solution
        (show target ∈ Ioo (0 : ℝ) T from
          ⟨by linarith [hstart, hhorizon], htarget⟩)
        helapsed (elapsed.2.2.trans_lt (by linarith [hstart] : horizon < target)) scale := by
  unfold compactElapsedOpenSharpPantographicSource
    openSharpPantographicSource compactOpenVelocityWeightedH3State
  congr 2

/-! ## Heat/curl transport of the complete signed chain -/

theorem heatTransportedH2SourceCurlCoefficient_add
    (nu elapsed : ℝ) (left right : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient nu elapsed (left + right) k =
      heatTransportedH2SourceCurlCoefficient nu elapsed left k +
        heatTransportedH2SourceCurlCoefficient nu elapsed right k := by
  change frequencyCurlMultiplierCLM k
      (heatTransportedH2SourceCoefficient nu elapsed (left + right) k) =
    frequencyCurlMultiplierCLM k
        (heatTransportedH2SourceCoefficient nu elapsed left k) +
      frequencyCurlMultiplierCLM k
        (heatTransportedH2SourceCoefficient nu elapsed right k)
  have hcoefficient : heatTransportedH2SourceCoefficient nu elapsed (left + right) k =
      heatTransportedH2SourceCoefficient nu elapsed left k +
        heatTransportedH2SourceCoefficient nu elapsed right k := by
    ext component
    simp only [heatTransportedH2SourceCoefficient, Pi.add_apply,
      weightedSobolevRawCoefficients_apply, lp.coeFn_add]
    ring
  rw [hcoefficient]
  exact (frequencyCurlMultiplierCLM k).map_add _ _

/-- Project any real elapsed coordinate onto the one declared compact aperture. -/
def compactElapsedProjection
    (horizon : ℝ) (hhorizon : 0 ≤ horizon) (elapsed : ℝ) :
    Icc (0 : ℝ) horizon :=
  Set.projIcc 0 horizon hhorizon elapsed

theorem continuous_compactElapsedProjection
    (horizon : ℝ) (hhorizon : 0 ≤ horizon) :
    Continuous (compactElapsedProjection horizon hhorizon) :=
  continuous_projIcc (h := hhorizon)

theorem compactElapsedProjection_eq
    {horizon elapsed : ℝ} (hhorizon : 0 ≤ horizon)
    (helapsed : elapsed ∈ Icc (0 : ℝ) horizon) :
    compactElapsedProjection horizon hhorizon elapsed =
      (⟨elapsed, helapsed⟩ : Icc (0 : ℝ) horizon) := by
  apply Subtype.ext
  exact congrArg Subtype.val (Set.projIcc_of_mem hhorizon helapsed)

/-- Joint continuity of heat time and a continuously moving native weighted source, observed at
one fixed curl/Fourier address. -/
theorem continuous_heatTransportedH2SourceCurlCoefficient_comp
    (nu : ℝ) (source : ℝ → PeriodicVectorWeightedSobolev 2)
    (hsource : Continuous source) (k : SpatialFrequency) :
    Continuous (fun elapsed ↦
      heatTransportedH2SourceCurlCoefficient nu elapsed (source elapsed) k) := by
  change Continuous (fun elapsed ↦ frequencyCurlMultiplierCLM k
    (heatTransportedH2SourceCoefficient nu elapsed (source elapsed) k))
  apply (frequencyCurlMultiplierCLM k).continuous.comp
  apply continuous_pi
  intro component
  have hcomponent : Continuous (fun elapsed ↦ source elapsed component) :=
    (continuous_apply component).comp hsource
  have heval : Continuous (fun elapsed ↦ source elapsed component k) :=
    (lp.evalCLM ℂ (fun _ : SpatialFrequency ↦ ℂ) 2 k).continuous.comp hcomponent
  have hclockReal : Continuous (fun elapsed : ℝ ↦
      heatStokesMultiplier nu elapsed k) := by
    unfold heatStokesMultiplier
    fun_prop
  simp only [heatTransportedH2SourceCoefficient,
    weightedSobolevRawCoefficients_apply]
  exact (Complex.continuous_ofReal.comp hclockReal).mul
    (continuous_const.mul heval)

/-- Heat/curl transport of the literal compact-reflected source. -/
def transportedCompactElapsedSharpSourceCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (k : SpatialFrequency) (elapsed : ℝ) : ComplexVector :=
  heatTransportedH2SourceCurlCoefficient nu elapsed
    (compactElapsedOpenSharpPantographicSource
      solution hstart htarget hhorizon
        (compactElapsedProjection horizon hhorizon elapsed) 0) k

/-- Heat/curl transport of the finite signed swing population. -/
def transportedCompactElapsedSharpPantographicPartialChainCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (k : SpatialFrequency) (elapsed : ℝ) : ComplexVector :=
  heatTransportedH2SourceCurlCoefficient nu elapsed
    (compactElapsedOpenSharpPantographicPartialChain
      solution hstart htarget hhorizon depth
        (compactElapsedProjection horizon hhorizon elapsed)) k

/-- Heat/curl transport of the explicitly retained finite-depth source residual. -/
def transportedCompactElapsedSharpPantographicResidualCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (k : SpatialFrequency) (elapsed : ℝ) : ComplexVector :=
  heatTransportedH2SourceCurlCoefficient nu elapsed
    (compactElapsedOpenSharpPantographicResidual
      solution hstart htarget hhorizon depth
        (compactElapsedProjection horizon hhorizon elapsed)) k

theorem continuous_transportedCompactElapsedSharpSourceCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (k : SpatialFrequency) :
    Continuous
      (transportedCompactElapsedSharpSourceCoefficient
        solution hstart htarget hhorizon k) := by
  unfold transportedCompactElapsedSharpSourceCoefficient
  apply continuous_heatTransportedH2SourceCurlCoefficient_comp
  exact (continuous_compactElapsedOpenSharpPantographicSource
    solution hstart htarget hhorizon 0).comp
      (continuous_compactElapsedProjection horizon hhorizon)

theorem continuous_transportedCompactElapsedSharpPantographicPartialChainCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ) (k : SpatialFrequency) :
    Continuous
      (transportedCompactElapsedSharpPantographicPartialChainCoefficient
        solution hstart htarget hhorizon depth k) := by
  unfold transportedCompactElapsedSharpPantographicPartialChainCoefficient
  apply continuous_heatTransportedH2SourceCurlCoefficient_comp
  exact (continuous_compactElapsedOpenSharpPantographicPartialChain
    solution hstart htarget hhorizon depth).comp
      (continuous_compactElapsedProjection horizon hhorizon)

theorem continuous_transportedCompactElapsedSharpPantographicResidualCoefficient
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ) (k : SpatialFrequency) :
    Continuous
      (transportedCompactElapsedSharpPantographicResidualCoefficient
        solution hstart htarget hhorizon depth k) := by
  unfold transportedCompactElapsedSharpPantographicResidualCoefficient
  apply continuous_heatTransportedH2SourceCurlCoefficient_comp
  exact (continuous_compactElapsedOpenSharpPantographicResidual
    solution hstart htarget hhorizon depth).comp
      (continuous_compactElapsedProjection horizon hhorizon)

/-- **Exact transported finite-chain reconstruction.**  Heat and curl act on the complete signed
source population before any norm; the finite residual and frozen target source remain separate. -/
theorem transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_frozen
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ)
    (k : SpatialFrequency) (elapsed : ℝ) :
    transportedCompactElapsedSharpSourceCoefficient
        solution hstart htarget hhorizon k elapsed =
      transportedCompactElapsedSharpPantographicPartialChainCoefficient
          solution hstart htarget hhorizon depth k elapsed +
        transportedCompactElapsedSharpPantographicResidualCoefficient
          solution hstart htarget hhorizon depth k elapsed +
        heatTransportedH2SourceCurlCoefficient nu elapsed
          (compactElapsedOpenSharpTargetSource
            solution hstart htarget hhorizon) k := by
  let clockElapsed := compactElapsedProjection horizon hhorizon elapsed
  have hreconstruct :=
    compactElapsedOpenSharpPantographicFiniteReconstruction
      solution hstart htarget hhorizon depth clockElapsed
  have hsource :
      compactElapsedOpenSharpPantographicSource
          solution hstart htarget hhorizon clockElapsed 0 =
        compactElapsedOpenSharpPantographicPartialChain
            solution hstart htarget hhorizon depth clockElapsed +
          compactElapsedOpenSharpPantographicResidual
            solution hstart htarget hhorizon depth clockElapsed +
          compactElapsedOpenSharpTargetSource
            solution hstart htarget hhorizon := by
    calc
      compactElapsedOpenSharpPantographicSource
          solution hstart htarget hhorizon clockElapsed 0 =
          (compactElapsedOpenSharpPantographicSource
              solution hstart htarget hhorizon clockElapsed 0 -
            compactElapsedOpenSharpTargetSource
              solution hstart htarget hhorizon) +
            compactElapsedOpenSharpTargetSource
              solution hstart htarget hhorizon := by abel
      _ = _ := by rw [hreconstruct]
  unfold transportedCompactElapsedSharpSourceCoefficient
    transportedCompactElapsedSharpPantographicPartialChainCoefficient
    transportedCompactElapsedSharpPantographicResidualCoefficient
  change heatTransportedH2SourceCurlCoefficient nu elapsed
      (compactElapsedOpenSharpPantographicSource
        solution hstart htarget hhorizon clockElapsed 0) k = _
  rw [hsource, heatTransportedH2SourceCurlCoefficient_add,
    heatTransportedH2SourceCurlCoefficient_add]

/-- On the declared elapsed interval, the projected compact source face is literally the actual
open-solution source at `target - elapsed`. -/
theorem transportedCompactElapsedSharpSourceCoefficient_eq_actual
    {T nu target horizon elapsed : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (k : SpatialFrequency)
    (helapsed : elapsed ∈ Icc (0 : ℝ) horizon) :
    transportedCompactElapsedSharpSourceCoefficient
        solution hstart htarget hhorizon k elapsed =
      heatTransportedH2SourceCurlCoefficient nu elapsed
        (sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨target - elapsed, by
              constructor
              · linarith [hstart, helapsed.2]
              · linarith [htarget, helapsed.1]⟩)) k := by
  unfold transportedCompactElapsedSharpSourceCoefficient
    compactElapsedOpenSharpPantographicSource
    compactOpenVelocityWeightedH3State
  rw [compactElapsedProjection_eq hhorizon helapsed]
  congr 3
  apply Subtype.ext
  simp [compactElapsedPantographicTime]

/-- The compact source-time mild integrand is the negative of the same actual source observed in
the reflected elapsed chart.  This is the exact orientation change `sourceTime = target-elapsed`.
-/
theorem compactStokesTransportedVorticityNonlinearMode_reflected_eq_neg_transportedSource
    {T nu s t : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) (elapsed : Icc (0 : ℝ) (t - s)) :
    compactStokesTransportedVorticityNonlinearMode
        solution hs hst ht k (t - elapsed.1) =
      -transportedCompactElapsedSharpSourceCoefficient solution
        (by simpa only [sub_sub_cancel] using hs) ht
        (sub_nonneg.mpr hst) k elapsed.1 := by
  have hsourceTime : t - elapsed.1 ∈ Icc s t := by
    constructor <;> linarith [elapsed.2.1, elapsed.2.2]
  rw [compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
    solution hs hst ht k hsourceTime]
  rw [transportedCompactElapsedSharpSourceCoefficient_eq_actual
    solution (by simpa only [sub_sub_cancel] using hs) ht
      (sub_nonneg.mpr hst) k elapsed.2]
  congr 3
  ring

/-! ## Elapsed integration and the exact frozen boundary face -/

/-- **Exact elapsed-integrated finite-chain return.**  The frozen source is integrated as the
existing heat-boundary/resolvent action.  The finite swing integral and finite residual integral
remain signed vector populations; no coefficient mass has yet been taken. -/
theorem intervalIntegral_transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_boundary
    {T nu target horizon : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hstart : 0 < target - horizon) (htarget : target < T)
    (hhorizon : 0 ≤ horizon) (depth : ℕ) (k : SpatialFrequency) :
    (∫ elapsed in 0..horizon,
        transportedCompactElapsedSharpSourceCoefficient
          solution hstart htarget hhorizon k elapsed) =
      (∫ elapsed in 0..horizon,
          transportedCompactElapsedSharpPantographicPartialChainCoefficient
            solution hstart htarget hhorizon depth k elapsed) +
        (∫ elapsed in 0..horizon,
          transportedCompactElapsedSharpPantographicResidualCoefficient
            solution hstart htarget hhorizon depth k elapsed) +
        frozenH2SourceCurlBoundaryAction nu horizon
          (compactElapsedOpenSharpTargetSource
            solution hstart htarget hhorizon) k := by
  let chain : ℝ → ComplexVector :=
    transportedCompactElapsedSharpPantographicPartialChainCoefficient
      solution hstart htarget hhorizon depth k
  let residual : ℝ → ComplexVector :=
    transportedCompactElapsedSharpPantographicResidualCoefficient
      solution hstart htarget hhorizon depth k
  let frozen : ℝ → ComplexVector := fun elapsed ↦
    heatTransportedH2SourceCurlCoefficient nu elapsed
      (compactElapsedOpenSharpTargetSource
        solution hstart htarget hhorizon) k
  have hchain : IntervalIntegrable chain volume 0 horizon :=
    (continuous_transportedCompactElapsedSharpPantographicPartialChainCoefficient
      solution hstart htarget hhorizon depth k).intervalIntegrable _ _
  have hresidual : IntervalIntegrable residual volume 0 horizon :=
    (continuous_transportedCompactElapsedSharpPantographicResidualCoefficient
      solution hstart htarget hhorizon depth k).intervalIntegrable _ _
  have hfrozen : IntervalIntegrable frozen volume 0 horizon :=
    (continuous_heatTransportedH2SourceCurlCoefficient nu
      (compactElapsedOpenSharpTargetSource
        solution hstart htarget hhorizon) k).intervalIntegrable _ _
  calc
    (∫ elapsed in 0..horizon,
        transportedCompactElapsedSharpSourceCoefficient
          solution hstart htarget hhorizon k elapsed) =
        ∫ elapsed in 0..horizon,
          (chain elapsed + residual elapsed) + frozen elapsed := by
      apply intervalIntegral.integral_congr
      intro elapsed _helapsed
      exact transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_frozen
        solution hstart htarget hhorizon depth k elapsed
    _ = (∫ elapsed in 0..horizon, chain elapsed) +
          (∫ elapsed in 0..horizon, residual elapsed) +
          ∫ elapsed in 0..horizon, frozen elapsed := by
      rw [intervalIntegral.integral_add (hchain.add hresidual) hfrozen,
        intervalIntegral.integral_add hchain hresidual]
    _ = _ := by
      rw [intervalIntegral_heatTransportedH2SourceCurlCoefficient_eq_boundaryAction
        hnu horizon
          (compactElapsedOpenSharpTargetSource
            solution hstart htarget hhorizon) k]

/-! ## Return to the source-time Duhamel receiver -/

/-- The source-time compact mild coefficient is exactly the negative elapsed-time transported
source integral.  The sign is the existing curl/source convention; the interval reflection itself
preserves orientation through its paired endpoint reversal and differential sign. -/
theorem intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_elapsedSource
    {T nu s t : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    (∫ sourceTime in s..t,
        compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k sourceTime) =
      -(∫ elapsed in 0..(t - s),
          transportedCompactElapsedSharpSourceCoefficient solution
            (by simpa only [sub_sub_cancel] using hs) ht
            (sub_nonneg.mpr hst) k elapsed) := by
  let mildCoefficient : ℝ → ComplexVector := fun sourceTime ↦
    compactStokesTransportedVorticityNonlinearMode
      solution hs hst ht k sourceTime
  have hreflect :
      (∫ elapsed in 0..(t - s), mildCoefficient (t - elapsed)) =
        ∫ sourceTime in s..t, mildCoefficient sourceTime := by
    simpa only [sub_sub_cancel, sub_zero] using
      (intervalIntegral.integral_comp_sub_left mildCoefficient t
        (a := (0 : ℝ)) (b := t - s))
  calc
    (∫ sourceTime in s..t,
        compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k sourceTime) =
        ∫ elapsed in 0..(t - s), mildCoefficient (t - elapsed) :=
      hreflect.symm
    _ = ∫ elapsed in 0..(t - s),
          -transportedCompactElapsedSharpSourceCoefficient solution
            (by simpa only [sub_sub_cancel] using hs) ht
            (sub_nonneg.mpr hst) k elapsed := by
      apply intervalIntegral.integral_congr
      intro elapsed helapsed
      have helapsed' : elapsed ∈ Icc (0 : ℝ) (t - s) := by
        simpa only [uIcc_of_le (sub_nonneg.mpr hst)] using helapsed
      exact compactStokesTransportedVorticityNonlinearMode_reflected_eq_neg_transportedSource
        solution hs hst ht k ⟨elapsed, helapsed'⟩
    _ = -(∫ elapsed in 0..(t - s),
          transportedCompactElapsedSharpSourceCoefficient solution
            (by simpa only [sub_sub_cancel] using hs) ht
            (sub_nonneg.mpr hst) k elapsed) := by
      rw [intervalIntegral.integral_neg]

/-- **Exact signed pantographic Duhamel chain.**  The actual source-time mild coefficient has now
passed through reflection, heat/curl transport, and elapsed integration.  At every finite depth it
is the negative of the transported signed swing population, its uncollapsed terminal residual,
and the frozen target-source boundary action. -/
theorem intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_chain_add_residual_add_boundary
    {T nu s t : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (depth : ℕ) (k : SpatialFrequency) :
    (∫ sourceTime in s..t,
        compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k sourceTime) =
      -((∫ elapsed in 0..(t - s),
          transportedCompactElapsedSharpPantographicPartialChainCoefficient
            solution (by simpa only [sub_sub_cancel] using hs) ht
              (sub_nonneg.mpr hst) depth k elapsed) +
        (∫ elapsed in 0..(t - s),
          transportedCompactElapsedSharpPantographicResidualCoefficient
            solution (by simpa only [sub_sub_cancel] using hs) ht
              (sub_nonneg.mpr hst) depth k elapsed) +
        frozenH2SourceCurlBoundaryAction nu (t - s)
          (compactElapsedOpenSharpTargetSource solution
            (by simpa only [sub_sub_cancel] using hs) ht
            (sub_nonneg.mpr hst)) k) := by
  rw [intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_elapsedSource
    solution hs hst ht k]
  rw [intervalIntegral_transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_boundary
    solution hnu (by simpa only [sub_sub_cancel] using hs) ht
      (sub_nonneg.mpr hst) depth k]

section Audit

#print axioms compactElapsedOpenSharpPantographicFiniteReconstruction
#print axioms compactElapsedOpenSharpPantographicSource_eq_open
#print axioms transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_frozen
#print axioms intervalIntegral_transportedCompactElapsedSharpSourceCoefficient_eq_chain_add_residual_add_boundary
#print axioms intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_elapsedSource
#print axioms intervalIntegral_compactStokesTransportedVorticityNonlinearMode_eq_neg_chain_add_residual_add_boundary

end Audit

end Soma.Holonics.Millennium.NavierStokesTransportedPantographicSwingChain

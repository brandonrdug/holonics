import ElementaryHolonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Cofinal depth limit of the actual fixed-time linear multiplier work

**[proved-derived; formal-checked]**  The cumulative Hodge boundary weight is

`V_depth - V_0`.

For every fixed frequency, `V_depth` is eventually one.  Thus the cumulative weight tends to
`1 - V_0`, not to an unqualified constant one.  This owner keeps the scale-zero stretching
boundary explicitly, applies Tannery to the complete stretching population, and combines that
passage with complete transport cancellation.

The result is pointwise at one interior time.  No time-uniform, terminal, or regularity conclusion
is asserted.
-/

noncomputable section

open Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Exact pointwise multiplier limit -/

/-- The cumulative boundary weight tends to one minus its retained scale-zero multiplier. -/
theorem tendsto_finiteDepthBoundaryWeight_atTop
    (frequency : SpatialFrequency) :
    Tendsto
      (fun depth : ℕ ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
      atTop
      (nhds ((1 : ℂ) -
        (tensorValleePoussinWeight
          (dyadicHodgeParameter 0) frequency : ℂ))) := by
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [eventually_tensorValleePoussinWeight_dyadic_eq_one frequency]
    with depth hdepth
  simp [finiteDepthBoundaryWeight, hdepth]

/-! ## Complete stretching population and retained low-pass boundary -/

/-- The complete unweighted stretching population at one fixed interior time. -/
def completeFullStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    completeOpenVorticityStretchingFace solution t address

/-- The scale-zero stretching boundary retained by the cumulative multiplier. -/
def completeLowPassStretchingBoundary
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    (tensorValleePoussinWeight
      (dyadicHodgeParameter 0) address.1 : ℂ) *
      completeOpenVorticityStretchingFace solution t address

/-- The complete cumulative stretching population before taking depth cofinally. -/
def completeCumulativeStretchingContribution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    (finiteDepthBoundaryWeight depth address.1 : ℂ) *
      completeOpenVorticityStretchingFace solution t address

theorem summable_completeCumulativeStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    Summable fun address : CompleteStretchingAddress ↦
      (finiteDepthBoundaryWeight depth address.1 : ℂ) *
        completeOpenVorticityStretchingFace solution t address := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_norm_completeOpenVorticityStretchingFace solution t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (abs_finiteDepthBoundaryWeight_le_one depth address.1)

/-- The finite native output presentation of complete receiver stretching is exactly the complete
address population because the cumulative output multiplier vanishes outside that aperture. -/
theorem completeReceiverStretchingWork_eq_completeCumulativeStretchingContribution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) (depth : ℕ) :
    completeReceiverStretchingWork solution t depth =
      completeCumulativeStretchingContribution solution t depth := by
  let population : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth address.1 : ℂ) *
      completeOpenVorticityStretchingFace solution t address
  have hpopulation : Summable population :=
    summable_completeCumulativeStretchingPopulation solution t depth
  have hfiber (output : SpatialFrequency) : Summable fun parent ↦
      population (output, parent) := by
    apply hpopulation.comp_injective
    intro first second heq
    exact congrArg Prod.snd heq
  have hprod := hpopulation.tsum_prod' hfiber
  unfold completeCumulativeStretchingContribution
  change completeReceiverStretchingWork solution t depth =
    ∑' address : CompleteStretchingAddress, population address
  rw [hprod]
  rw [tsum_eq_sum (s := smoothDyadicBandNativeAperture depth)
    (fun output houtput ↦ by
      have hzero :=
        finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture depth houtput
      simp [population, hzero])]
  unfold completeReceiverStretchingWork completeReceiverStretchingPhaseAtOutput
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [← tsum_mul_left]

/-- The scale-zero weighted stretching population is absolutely summable. -/
theorem summable_completeLowPassStretchingPopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Summable fun address : CompleteStretchingAddress ↦
      (tensorValleePoussinWeight
        (dyadicHodgeParameter 0) address.1 : ℂ) *
        completeOpenVorticityStretchingFace solution t address := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    (summable_norm_completeOpenVorticityStretchingFace solution t)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (abs_tensorValleePoussinWeight_zero_le_one address.1)

/-- **Complete stretching Tannery passage.**  The receiver stretching contribution tends to the
full complete stretching population minus its retained scale-zero boundary. -/
theorem tendsto_completeReceiverStretchingWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto (completeReceiverStretchingWork solution t) atTop
      (nhds (completeFullStretchingPopulation solution t -
        completeLowPassStretchingBoundary solution t)) := by
  let face : CompleteStretchingAddress → ℂ :=
    completeOpenVorticityStretchingFace solution t
  let lowWeight : CompleteStretchingAddress → ℂ := fun address ↦
    (tensorValleePoussinWeight
      (dyadicHodgeParameter 0) address.1 : ℂ)
  have hpointwise (address : CompleteStretchingAddress) :
      Tendsto
        (fun depth : ℕ ↦
          (finiteDepthBoundaryWeight depth address.1 : ℂ) * face address)
        atTop
        (nhds (((1 : ℂ) - lowWeight address) * face address)) :=
    (tendsto_finiteDepthBoundaryWeight_atTop address.1).mul_const (face address)
  have hbound : ∀ᶠ depth in atTop, ∀ address : CompleteStretchingAddress,
      ‖(finiteDepthBoundaryWeight depth address.1 : ℂ) * face address‖ ≤
        ‖face address‖ := by
    filter_upwards [] with depth address
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (abs_finiteDepthBoundaryWeight_le_one depth address.1)
  have htannery := tendsto_tsum_of_dominated_convergence
    (summable_norm_completeOpenVorticityStretchingFace solution t)
    hpointwise hbound
  have hface : Summable face :=
    (summable_norm_completeOpenVorticityStretchingFace solution t).of_norm
  have hlow : Summable fun address ↦ lowWeight address * face address := by
    simpa only [lowWeight, face] using
      summable_completeLowPassStretchingPopulation solution t
  have htarget :
      (∑' address : CompleteStretchingAddress,
        ((1 : ℂ) - lowWeight address) * face address) =
      completeFullStretchingPopulation solution t -
        completeLowPassStretchingBoundary solution t := by
    have hreexpress (address : CompleteStretchingAddress) :
        ((1 : ℂ) - lowWeight address) * face address =
          face address - lowWeight address * face address := by ring
    rw [tsum_congr hreexpress, hface.tsum_sub hlow]
    rfl
  have hcumulative : Tendsto
      (completeCumulativeStretchingContribution solution t) atTop
      (nhds (completeFullStretchingPopulation solution t -
        completeLowPassStretchingBoundary solution t)) := by
    change Tendsto
      (fun depth ↦ ∑' address : CompleteStretchingAddress,
        (finiteDepthBoundaryWeight depth address.1 : ℂ) * face address)
      atTop
      (nhds (completeFullStretchingPopulation solution t -
        completeLowPassStretchingBoundary solution t))
    rw [← htarget]
    exact htannery
  apply Tendsto.congr' _ hcumulative
  exact Filter.Eventually.of_forall fun depth ↦
    (completeReceiverStretchingWork_eq_completeCumulativeStretchingContribution
      solution t depth).symm

/-! ## Actual nonlinear-work cofinal limit -/

/-- The exact fixed-time depth-cofinal receiver for the actual nonlinear multiplier work. -/
def completeCofinalLinearMultiplierWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) : ℂ :=
  completeFullStretchingPopulation solution t -
    completeLowPassStretchingBoundary solution t -
      (1 / 2 : ℂ) *
        (completeLowPassTransportBoundary solution t +
          conj (completeLowPassTransportBoundary solution t))

/-- **Actual fixed-time cofinal linear-work limit.**  Complete stretching survives, while the
scale-zero stretching and Hermitian transport boundaries remain explicit with their exact signs.
No time or terminal passage is included. -/
theorem tendsto_actualLinearMultiplierCoefficientWork_atTop
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Set.Ioo 0 T) :
    Tendsto
      (fun depth : ℕ ↦
        linearMultiplierCoefficientWork
          (smoothDyadicCumulativeBoundaryMultiplier depth)
          (smoothDyadicBandNativeAperture depth)
          (openPeriodicVorticityFourierMode solution t)
          (vorticityNonlinearMode solution t))
      atTop
      (nhds (completeCofinalLinearMultiplierWork solution t)) := by
  have hstretch := tendsto_completeReceiverStretchingWork_atTop solution t
  have htransport := tendsto_completeSymmetricReceiverTransportWork_atTop solution t
  have hcombined := hstretch.sub htransport
  apply Tendsto.congr' _ hcombined
  exact Filter.Eventually.of_forall fun depth ↦
    (linearMultiplierCoefficientWork_eq_completeStretching_sub_transport
      solution t depth).symm

section Audit

#print axioms tendsto_finiteDepthBoundaryWeight_atTop
#print axioms completeReceiverStretchingWork_eq_completeCumulativeStretchingContribution
#print axioms tendsto_completeReceiverStretchingWork_atTop
#print axioms tendsto_actualLinearMultiplierCoefficientWork_atTop

end Audit

end Soma.Holonics.Millennium.NavierStokesCompleteLinearWorkCofinalLimit

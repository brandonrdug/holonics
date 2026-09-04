import ElementaryHolonics.Millennium.NavierStokesCoordinateJacobianTailBalance

/-!
# The exact dyadic Hodge scale chain

**[proved-derived]** The integer-radius Hodge scale chain admits a literal dyadic rebase.  Scale
`s` uses de la Vallée--Poussin parameter `2^s - 1`; consequently its multiplier is exactly one
on the frequency cube of radius `2^s` and is supported in the cube of radius `2^(s+1) - 1`.

The direct dyadic band is the difference between two consecutive dyadic low passes.  Its
recurrence and finite telescoping word are exact, and the complete physical Jacobian remains the
base face plus that word plus the addressed reconstruction fibre.  The fibre is never discarded:
its coefficient tail is attached below to the quantitative `H^3` decay theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianMatrixBridge
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianReceiver
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailDecay
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianTailBalance
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesHodgeBandReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothHodgeJacobianBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := inferInstance

/-! ## Exact dyadic aperture arithmetic -/

/-- The de la Vallée--Poussin parameter whose plateau cutoff is exactly `2^scale`. -/
def dyadicHodgeParameter (scale : ℕ) : ℕ :=
  dyadicRadius scale - 1

/-- The exact plateau cutoff of the dyadic chart. -/
def dyadicHodgeInnerCutoff (scale : ℕ) : ℕ :=
  dyadicRadius scale

/-- The exact outer support cutoff of the dyadic chart. -/
def dyadicHodgeOuterCutoff (scale : ℕ) : ℕ :=
  valleePoussinOuterRadius (dyadicHodgeParameter scale)

theorem dyadicHodgeParameter_add_one (scale : ℕ) :
    dyadicHodgeParameter scale + 1 = dyadicRadius scale := by
  have hpositive : 1 ≤ dyadicRadius scale := by
    exact Nat.one_le_pow scale 2 (by norm_num)
  unfold dyadicHodgeParameter
  omega

theorem dyadicHodgeOuterCutoff_eq (scale : ℕ) :
    dyadicHodgeOuterCutoff scale = dyadicRadius (scale + 1) - 1 := by
  have hpositive : 1 ≤ dyadicRadius scale := by
    exact Nat.one_le_pow scale 2 (by norm_num)
  calc
    dyadicHodgeOuterCutoff scale =
        2 * (dyadicRadius scale - 1) + 1 := rfl
    _ = 2 * dyadicRadius scale - 1 := by omega
    _ = dyadicRadius (scale + 1) - 1 := by
      simp only [dyadicRadius, pow_succ]
      omega

theorem dyadicHodgeInnerCube_eq_parameterPlateau (scale : ℕ) :
    frequencyCube (dyadicHodgeInnerCutoff scale) =
      frequencyCube (dyadicHodgeParameter scale + 1) := by
  rw [dyadicHodgeParameter_add_one]
  rfl

theorem dyadicHodgeOuterCube_eq_parameterSupport (scale : ℕ) :
    frequencyCube (dyadicHodgeOuterCutoff scale) =
      frequencyCube (valleePoussinOuterRadius (dyadicHodgeParameter scale)) := by
  rfl

/-! ## Direct dyadic low passes and bands -/

/-- The actual smooth Hodge low pass rebased to the exact dyadic plateau `2^scale`. -/
def openPeriodicDyadicHodgeJacobianLowPass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ComplexJacobianArray) :=
  openPeriodicSmoothHodgeJacobianLowPass solution t (dyadicHodgeParameter scale)

/-- One direct dyadic passage, retaining the two consecutive low-pass endpoints. -/
def openPeriodicDyadicHodgeJacobianBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) : C(SpatialTorus, ComplexJacobianArray) :=
  openPeriodicDyadicHodgeJacobianLowPass solution t (scale + 1) -
    openPeriodicDyadicHodgeJacobianLowPass solution t scale

/-- **One dyadic scale passage.** -/
theorem openPeriodicDyadicHodgeJacobianLowPass_succ
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicDyadicHodgeJacobianLowPass solution t (scale + 1) =
      openPeriodicDyadicHodgeJacobianLowPass solution t scale +
        openPeriodicDyadicHodgeJacobianBand solution t scale := by
  unfold openPeriodicDyadicHodgeJacobianBand
  abel

/-- **Complete finite dyadic word.**  Every dyadic band occurs once and in scale order. -/
theorem openPeriodicDyadicHodgeJacobianLowPass_eq_base_add_sum_bands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    openPeriodicDyadicHodgeJacobianLowPass solution t depth =
      openPeriodicDyadicHodgeJacobianLowPass solution t 0 +
        ∑ scale ∈ Finset.range depth,
          openPeriodicDyadicHodgeJacobianBand solution t scale := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      rw [openPeriodicDyadicHodgeJacobianLowPass_succ,
        inductionHypothesis, Finset.sum_range_succ]
      abel

theorem openPeriodicDyadicHodgeJacobianLowPass_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    openPeriodicDyadicHodgeJacobianLowPass solution t 0 =
      openPeriodicSmoothHodgeJacobianLowPass solution t 0 := by
  simp [openPeriodicDyadicHodgeJacobianLowPass, dyadicHodgeParameter,
    dyadicRadius]

/-! ## The direct dyadic physical Hodge kernel -/

/-- The direct multiplier passage between consecutive dyadic low passes. -/
def dyadicHodgeBandWeight
    (scale : ℕ) (frequency : SpatialFrequency) : ℝ :=
  tensorValleePoussinWeight (dyadicHodgeParameter (scale + 1)) frequency -
    tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency

/-- The direct dyadic multiplier acting on one vorticity pin. -/
def dyadicHodgeJacobianMode
    (scale : ℕ) (frequency : SpatialFrequency) (vorticityMode : ComplexVector) :
    ComplexJacobianArray :=
  (dyadicHodgeBandWeight scale frequency : ℂ) •
    hodgeJacobianMode frequency vorticityMode

theorem dyadicHodgeOuterCutoff_mono (scale : ℕ) :
    dyadicHodgeOuterCutoff scale ≤ dyadicHodgeOuterCutoff (scale + 1) := by
  rw [dyadicHodgeOuterCutoff_eq, dyadicHodgeOuterCutoff_eq]
  apply Nat.sub_le_sub_right
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ (scale + 1))

/-- The direct band cancels every frequency in its exact inner dyadic cube. -/
theorem dyadicHodgeBandWeight_eq_zero_of_mem_inner
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∈ frequencyCube (dyadicHodgeInnerCutoff scale)) :
    dyadicHodgeBandWeight scale frequency = 0 := by
  have hnextInner :
      dyadicHodgeInnerCutoff scale ≤ dyadicHodgeInnerCutoff (scale + 1) := by
    unfold dyadicHodgeInnerCutoff dyadicRadius
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ scale)
  have hnextRaw :
      frequency ∈ frequencyCube (dyadicHodgeInnerCutoff (scale + 1)) :=
    frequencyCube_mono hnextInner hfrequency
  have hcurrent :
      frequency ∈ frequencyCube (dyadicHodgeParameter scale + 1) := by
    simpa only [dyadicHodgeParameter_add_one, dyadicHodgeInnerCutoff] using hfrequency
  have hnext :
      frequency ∈ frequencyCube (dyadicHodgeParameter (scale + 1) + 1) := by
    simpa only [dyadicHodgeParameter_add_one, dyadicHodgeInnerCutoff] using hnextRaw
  rw [dyadicHodgeBandWeight,
    tensorValleePoussinWeight_eq_one _ hnext,
    tensorValleePoussinWeight_eq_one _ hcurrent, sub_self]

/-- The direct dyadic band vanishes outside the next chart's exact finite support. -/
theorem dyadicHodgeBandWeight_eq_zero_of_not_mem_outer
    (scale : ℕ) {frequency : SpatialFrequency}
    (hfrequency : frequency ∉
      frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) :
    dyadicHodgeBandWeight scale frequency = 0 := by
  have hsmaller : frequency ∉ frequencyCube (dyadicHodgeOuterCutoff scale) := by
    intro hmem
    exact hfrequency (frequencyCube_mono (dyadicHodgeOuterCutoff_mono scale) hmem)
  rw [dyadicHodgeBandWeight,
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter (scale + 1)) (by simpa [dyadicHodgeOuterCutoff] using hfrequency),
    tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter scale) (by simpa [dyadicHodgeOuterCutoff] using hsmaller),
    sub_zero]

/-- The direct Hodge multiplier applied to actual vorticity is exactly the direct scalar chart
applied to the actual Jacobian coefficient. -/
theorem dyadicHodgeJacobianMode_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (frequency : SpatialFrequency) :
    dyadicHodgeJacobianMode scale frequency
        (openPeriodicVorticityFourierMode solution t frequency) =
      (dyadicHodgeBandWeight scale frequency : ℂ) •
        openPeriodicJacobianFourierMode solution t frequency := by
  unfold dyadicHodgeJacobianMode
  rw [hodgeJacobianMode_openPeriodicVorticityFourierMode]

/-- The smaller dyadic low pass can be mounted in the next dyadic chart's aperture without
changing its value. -/
theorem openPeriodicDyadicHodgeJacobianLowPass_eq_nextAperture
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicDyadicHodgeJacobianLowPass solution t scale =
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) := by
  unfold openPeriodicDyadicHodgeJacobianLowPass
    openPeriodicSmoothHodgeJacobianLowPass
  apply finiteFourierSynthesis_eq_of_subset_of_eq_zero
  · apply frequencyCube_mono
    simpa only [dyadicHodgeOuterCutoff] using dyadicHodgeOuterCutoff_mono scale
  · intro frequency _houter hinner
    rw [tensorValleePoussinWeight_eq_zero_of_not_mem_outer
      (dyadicHodgeParameter scale) (by
        simpa [dyadicHodgeOuterCutoff] using hinner)]
    simp

/-- The direct dyadic band is exactly its direct multiplier applied to actual Jacobian pins. -/
theorem openPeriodicDyadicHodgeJacobianBand_eq_actualMultiplier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicDyadicHodgeJacobianBand solution t scale =
      finiteFourierSynthesis
        (fun frequency ↦
          (dyadicHodgeBandWeight scale frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) := by
  have hcurrent := openPeriodicDyadicHodgeJacobianLowPass_eq_nextAperture
    solution t scale
  rw [openPeriodicDyadicHodgeJacobianBand, hcurrent]
  change
    finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter (scale + 1)) frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) -
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter scale) frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) = _
  ext q component coordinate
  unfold finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, ContinuousMap.sub_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  unfold dyadicHodgeBandWeight
  push_cast
  ring

/-- The same exact band expressed on the vorticity side of Hodge ascent. -/
theorem openPeriodicDyadicHodgeJacobianBand_eq_hodgeMultiplier
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) :
    openPeriodicDyadicHodgeJacobianBand solution t scale =
      finiteFourierSynthesis
        (fun frequency ↦ dyadicHodgeJacobianMode scale frequency
          (openPeriodicVorticityFourierMode solution t frequency))
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) := by
  rw [openPeriodicDyadicHodgeJacobianBand_eq_actualMultiplier]
  congr 1
  funext frequency
  exact (dyadicHodgeJacobianMode_openPeriodicVorticityFourierMode
    solution t scale frequency).symm

/-- One scalar entry of the direct physical dyadic Hodge kernel. -/
def dyadicHodgeJacobianKernelEntry
    (scale : ℕ) (component coordinate input : Fin 3) : C(SpatialTorus, ℂ) :=
  finiteFourierSynthesis
    (fun frequency ↦
      (dyadicHodgeBandWeight scale frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input)
    (frequencyCube (dyadicHodgeOuterCutoff (scale + 1)))

/-- Every direct kernel entry has its intended multiplier coefficient at every lattice mode. -/
theorem mFourierCoeff_dyadicHodgeJacobianKernelEntry
    (scale : ℕ) (component coordinate input : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (dyadicHodgeJacobianKernelEntry scale component coordinate input)
        frequency =
      (dyadicHodgeBandWeight scale frequency : ℂ) *
        hodgeJacobianMultiplierEntry frequency component coordinate input := by
  rw [dyadicHodgeJacobianKernelEntry,
    mFourierCoeff_finiteFourierSynthesis]
  split_ifs with hfrequency
  · rfl
  · rw [dyadicHodgeBandWeight_eq_zero_of_not_mem_outer scale hfrequency]
    simp

/-- Physical convolution by the complete direct dyadic matrix kernel. -/
def dyadicHodgeJacobianKernelConvolution
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) : ComplexJacobianArray :=
  fun component coordinate ↦
    ∑ input : Fin 3,
      ∫ y : SpatialTorus,
        dyadicHodgeJacobianKernelEntry scale component coordinate input y *
          field (q - y) input

/-- **Exact physical/Fourier identity for a whole dyadic step.** -/
theorem dyadicHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) :
    dyadicHodgeJacobianKernelConvolution scale field q =
      finiteFourierSynthesis
        (fun frequency ↦ dyadicHodgeJacobianMode scale frequency
          (UnitAddTorus.mFourierCoeff field frequency))
        (frequencyCube (dyadicHodgeOuterCutoff (scale + 1))) q := by
  funext component coordinate
  unfold dyadicHodgeJacobianKernelConvolution
    dyadicHodgeJacobianKernelEntry finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let modes := frequencyCube (dyadicHodgeOuterCutoff (scale + 1))
  change
    (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        (∑ frequency ∈ modes,
          UnitAddTorus.mFourier frequency y *
            ((dyadicHodgeBandWeight scale frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          field (q - y) input) =
      ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency q *
          dyadicHodgeJacobianMode scale frequency
            (UnitAddTorus.mFourierCoeff field frequency) component coordinate
  calc
    (∑ input : Fin 3,
      ∫ y : SpatialTorus,
        (∑ frequency ∈ modes,
          UnitAddTorus.mFourier frequency y *
            ((dyadicHodgeBandWeight scale frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
          field (q - y) input) =
      ∑ input : Fin 3, ∑ frequency ∈ modes,
        ∫ y : SpatialTorus,
          (UnitAddTorus.mFourier frequency y *
            ((dyadicHodgeBandWeight scale frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                field (q - y) input := by
      apply Finset.sum_congr rfl
      intro input _hinput
      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum]
      intro frequency _hfrequency
      exact continuousMap_integrable_on_compact
        { toFun := fun y : SpatialTorus ↦
            (UnitAddTorus.mFourier frequency y *
              ((dyadicHodgeBandWeight scale frequency : ℂ) *
                hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                  field (q - y) input
          continuous_toFun := by fun_prop }
    _ = ∑ frequency ∈ modes, ∑ input : Fin 3,
        ∫ y : SpatialTorus,
          (UnitAddTorus.mFourier frequency y *
            ((dyadicHodgeBandWeight scale frequency : ℂ) *
              hodgeJacobianMultiplierEntry frequency component coordinate input)) *
                field (q - y) input := by
      rw [Finset.sum_comm]
    _ = ∑ frequency ∈ modes,
        UnitAddTorus.mFourier frequency q *
          dyadicHodgeJacobianMode scale frequency
            (UnitAddTorus.mFourierCoeff field frequency) component coordinate := by
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      unfold dyadicHodgeJacobianMode
      rw [Pi.smul_apply, Pi.smul_apply,
        hodgeJacobianMode_eq_sum_multiplierEntry]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro input _hinput
      have hcharacter := integral_mFourier_mul_sub_eq
        { toFun := fun y : SpatialTorus ↦ field y input
          continuous_toFun := by fun_prop }
        frequency q
      rw [mFourierCoeff_apply field frequency input]
      let coefficient : ℂ :=
        (dyadicHodgeBandWeight scale frequency : ℂ) *
          hodgeJacobianMultiplierEntry frequency component coordinate input
      calc
        ∫ y : SpatialTorus,
            UnitAddTorus.mFourier frequency y * coefficient *
              field (q - y) input =
            ∫ y : SpatialTorus,
              coefficient *
                (UnitAddTorus.mFourier frequency y * field (q - y) input) := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
        _ = coefficient *
              (∫ y : SpatialTorus,
                UnitAddTorus.mFourier frequency y * field (q - y) input) := by
          rw [integral_const_mul]
        _ = coefficient *
            (UnitAddTorus.mFourier frequency q *
              UnitAddTorus.mFourierCoeff
                (fun y : SpatialTorus ↦ field y input) frequency) := by
          congr 1
        _ = UnitAddTorus.mFourier frequency q *
            ((dyadicHodgeBandWeight scale frequency : ℂ) *
              (hodgeJacobianMultiplierEntry frequency component coordinate input *
                UnitAddTorus.mFourierCoeff
                  (fun y : SpatialTorus ↦ field y input) frequency)) := by
          dsimp [coefficient]
          ring

/-- The actual direct dyadic band is physical convolution by the direct dyadic kernel. -/
theorem openPeriodicDyadicHodgeJacobianBand_eq_kernelConvolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (q : SpatialTorus) :
    openPeriodicDyadicHodgeJacobianBand solution t scale q =
      dyadicHodgeJacobianKernelConvolution scale
        (complexTorusVorticitySlice solution t) q := by
  rw [dyadicHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis]
  simp_rw [← openPeriodicVorticityFourierMode_eq_mFourierCoeff solution t]
  exact congrArg (fun field : C(SpatialTorus, ComplexJacobianArray) ↦ field q)
    (openPeriodicDyadicHodgeJacobianBand_eq_hodgeMultiplier
      solution t scale)

/-- The exact total entrywise physical `L1` mass of one direct dyadic kernel. -/
def dyadicHodgeJacobianKernelL1 (scale : ℕ) : ℝ :=
  ∑ component : Fin 3, ∑ coordinate : Fin 3, ∑ input : Fin 3,
    ∫ y : SpatialTorus,
      ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖

/-- A direct dyadic matrix convolution is bounded by its exact physical `L1` receiver. -/
theorem norm_dyadicHodgeJacobianKernelConvolution_le
    (scale : ℕ) (field : C(SpatialTorus, ComplexVector))
    (q : SpatialTorus) :
    ‖dyadicHodgeJacobianKernelConvolution scale field q‖ ≤
      dyadicHodgeJacobianKernelL1 scale * ‖field‖ := by
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (by unfold dyadicHodgeJacobianKernelL1; positivity)
      (norm_nonneg field))]
  intro component
  rw [pi_norm_le_iff_of_nonneg
    (mul_nonneg (by unfold dyadicHodgeJacobianKernelL1; positivity)
      (norm_nonneg field))]
  intro coordinate
  unfold dyadicHodgeJacobianKernelConvolution
  calc
    ‖∑ input : Fin 3,
        ∫ y : SpatialTorus,
          dyadicHodgeJacobianKernelEntry scale component coordinate input y *
            field (q - y) input‖ ≤
        ∑ input : Fin 3,
          ‖∫ y : SpatialTorus,
            dyadicHodgeJacobianKernelEntry scale component coordinate input y *
              field (q - y) input‖ := norm_sum_le _ _
    _ ≤ ∑ input : Fin 3,
          (∫ y : SpatialTorus,
            ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) *
              ‖field‖ := by
      apply Finset.sum_le_sum
      intro input _hinput
      have hmajorant : Integrable
          (fun y : SpatialTorus ↦
            ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖ *
              ‖field‖) :=
        continuousMap_integrable_on_compact
          { toFun := fun y : SpatialTorus ↦
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖ *
                ‖field‖
            continuous_toFun := by fun_prop }
      calc
        ‖∫ y : SpatialTorus,
            dyadicHodgeJacobianKernelEntry scale component coordinate input y *
              field (q - y) input‖ ≤
            ∫ y : SpatialTorus,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖ *
                ‖field‖ := by
          apply norm_integral_le_of_norm_le hmajorant
          filter_upwards [] with y
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            ((norm_le_pi_norm (f := field (q - y)) input).trans
              (field.norm_coe_le_norm (q - y))) (norm_nonneg _)
        _ = (∫ y : SpatialTorus,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) *
                ‖field‖ := by rw [integral_mul_const]
    _ = (∑ input : Fin 3,
          ∫ y : SpatialTorus,
            ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) *
              ‖field‖ := by rw [Finset.sum_mul]
    _ ≤ dyadicHodgeJacobianKernelL1 scale * ‖field‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg field)
      unfold dyadicHodgeJacobianKernelL1
      calc
        (∑ input : Fin 3,
            ∫ y : SpatialTorus,
              ‖dyadicHodgeJacobianKernelEntry scale component coordinate input y‖) ≤
            ∑ coordinate' : Fin 3, ∑ input : Fin 3,
              ∫ y : SpatialTorus,
                ‖dyadicHodgeJacobianKernelEntry scale component coordinate' input y‖ := by
          apply Finset.single_le_sum
            (s := Finset.univ)
            (f := fun coordinate' : Fin 3 ↦ ∑ input : Fin 3,
              ∫ y : SpatialTorus,
                ‖dyadicHodgeJacobianKernelEntry scale component coordinate' input y‖)
          · intro coordinate' _hcoordinate'
            apply Finset.sum_nonneg
            intro input _hinput
            exact integral_nonneg fun y ↦ norm_nonneg _
          · exact Finset.mem_univ coordinate
        _ ≤ ∑ component' : Fin 3, ∑ coordinate' : Fin 3,
              ∑ input : Fin 3,
                ∫ y : SpatialTorus,
                  ‖dyadicHodgeJacobianKernelEntry scale component' coordinate' input y‖ := by
          apply Finset.single_le_sum
            (s := Finset.univ)
            (f := fun component' : Fin 3 ↦ ∑ coordinate' : Fin 3,
              ∑ input : Fin 3,
                ∫ y : SpatialTorus,
                  ‖dyadicHodgeJacobianKernelEntry scale component' coordinate' input y‖)
          · intro component' _hcomponent'
            apply Finset.sum_nonneg
            intro coordinate' _hcoordinate'
            apply Finset.sum_nonneg
            intro input _hinput
            exact integral_nonneg fun y ↦ norm_nonneg _
          · exact Finset.mem_univ component

/-- Honest actual-slice estimate.  No scale-uniform kernel constant is assumed. -/
theorem norm_openPeriodicDyadicHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (q : SpatialTorus) :
    ‖openPeriodicDyadicHodgeJacobianBand solution t scale q‖ ≤
      dyadicHodgeJacobianKernelL1 scale * criticalVorticityRate solution t.1 := by
  rw [openPeriodicDyadicHodgeJacobianBand_eq_kernelConvolution]
  refine (norm_dyadicHodgeJacobianKernelConvolution_le scale
    (complexTorusVorticitySlice solution t) q).trans ?_
  have hfield : ‖complexTorusVorticitySlice solution t‖ ≤
      criticalVorticityRate solution t.1 := by
    rw [criticalVorticityRate_eq solution t.2]
    apply (ContinuousMap.norm_le _
      (norm_nonneg (torusVorticityEvolution solution t))).mpr
    intro q'
    exact (norm_complexifySpace_le
      (torusVorticityEvolution solution t q')).trans
        ((torusVorticityEvolution solution t).norm_coe_le_norm q')
  have hL1 : 0 ≤ dyadicHodgeJacobianKernelL1 scale := by
    unfold dyadicHodgeJacobianKernelL1
    positivity
  exact mul_le_mul_of_nonneg_left hfield hL1

/-- The exact unresolved analytic statement: one number controls the direct physical dyadic
kernel `L1` mass at every scale.  This owner neither assumes nor proves its inhabitation. -/
def UniformDyadicHodgeJacobianKernelBound (constant : ℝ) : Prop :=
  0 ≤ constant ∧ ∀ scale : ℕ, dyadicHodgeJacobianKernelL1 scale ≤ constant

/-- Existential spelling of the one open uniform direct-kernel estimate. -/
def HasUniformDyadicHodgeJacobianKernelBound : Prop :=
  ∃ constant : ℝ, UniformDyadicHodgeJacobianKernelBound constant

/-- Conditional receiver consequence of the explicitly named uniform-kernel residual. -/
theorem norm_openPeriodicDyadicHodgeJacobianBand_le_of_uniformKernelBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {constant : ℝ}
    (hconstant : UniformDyadicHodgeJacobianKernelBound constant)
    (scale : ℕ) (q : SpatialTorus) :
    ‖openPeriodicDyadicHodgeJacobianBand solution t scale q‖ ≤
      constant * criticalVorticityRate solution t.1 := by
  exact (norm_openPeriodicDyadicHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
    solution t scale q).trans
      (mul_le_mul_of_nonneg_right (hconstant.2 scale)
        (criticalVorticityRate_nonneg solution t.1))

/-! ## The retained complete reconstruction fibre -/

/-- The exact reconstruction fibre at the dyadic low-pass endpoint. -/
def openPeriodicDyadicHodgeJacobianReconstructionFiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) : ComplexJacobianArray :=
  openPeriodicJacobianScaleReconstructionFiber solution t
    (dyadicHodgeParameter depth) q

/-- Exact complete-Jacobian decomposition at one dyadic endpoint. -/
theorem openPeriodicTorusJacobianArraySlice_eq_dyadicLowPass_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q =
      openPeriodicDyadicHodgeJacobianLowPass solution t depth q +
        openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q := by
  exact openPeriodicTorusJacobianArraySlice_eq_lowPass_add_scaleFiber
    solution t (dyadicHodgeParameter depth) q

/-- **Exact complete dyadic circulation.**  The fibre remains a separate addressed return. -/
theorem openPeriodicTorusJacobianArraySlice_eq_base_add_sum_dyadicBands_add_fiber
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    openPeriodicTorusJacobianArraySlice solution t q =
      openPeriodicDyadicHodgeJacobianLowPass solution t 0 q +
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicHodgeJacobianBand solution t scale q) +
        openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q := by
  have hdecomposition :=
    openPeriodicTorusJacobianArraySlice_eq_dyadicLowPass_add_fiber
      solution t depth q
  have hchain := congrArg
    (fun field : C(SpatialTorus, ComplexJacobianArray) ↦ field q)
    (openPeriodicDyadicHodgeJacobianLowPass_eq_base_add_sum_bands
      solution t depth)
  simp only [ContinuousMap.add_apply] at hchain
  have hsumEvaluation :
      (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicHodgeJacobianBand solution t scale) q =
        ∑ scale ∈ Finset.range depth,
          openPeriodicDyadicHodgeJacobianBand solution t scale q := by
    simp
  rw [hdecomposition, hchain, hsumEvaluation]

/-! ## Quantitative attachment at dyadic cutoffs -/

/-- The complete scale fibre is controlled by the coefficient population outside the exact
dyadic plateau cutoff `2^depth`. -/
theorem norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_two_mul_tailMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    ‖openPeriodicDyadicHodgeJacobianReconstructionFiber solution t depth q‖ ≤
      2 * openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (dyadicHodgeInnerCutoff depth)) := by
  simpa [openPeriodicDyadicHodgeJacobianReconstructionFiber,
    dyadicHodgeInnerCutoff, dyadicHodgeParameter_add_one] using
      norm_openPeriodicJacobianScaleReconstructionFiber_le_two_mul_tailMass
        solution t (dyadicHodgeParameter depth) q

/-- Unconditional pointwise dyadic BKM decomposition with every scale's exact physical kernel
mass and the complete coefficient tail retained. -/
theorem norm_openPeriodicTorusJacobianArraySlice_le_dyadicKernelSum_add_tail
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianArraySlice solution t q‖ ≤
      81 * criticalVorticityRate solution t.1 +
        (∑ scale ∈ Finset.range depth,
          dyadicHodgeJacobianKernelL1 scale *
            criticalVorticityRate solution t.1) +
        2 * openPeriodicJacobianCoefficientTailMass solution t
          (frequencyCube (dyadicHodgeInnerCutoff depth)) := by
  rw [openPeriodicTorusJacobianArraySlice_eq_base_add_sum_dyadicBands_add_fiber]
  refine (norm_add_le _ _).trans ?_
  apply add_le_add
  · refine (norm_add_le _ _).trans ?_
    apply add_le_add
    · rw [openPeriodicDyadicHodgeJacobianLowPass_zero]
      exact norm_openPeriodicSmoothHodgeJacobianLowPass_zero_apply_le
        solution t q
    · refine (norm_sum_le _ _).trans ?_
      apply Finset.sum_le_sum
      intro scale _hscale
      exact norm_openPeriodicDyadicHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
        solution t scale q
  · exact norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_two_mul_tailMass
      solution t depth q

/-- Under the one explicitly declared uniform physical-kernel receipt, the finite dyadic word
costs exactly `depth` copies of `constant * criticalVorticityRate`. -/
theorem norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {constant : ℝ}
    (hconstant : UniformDyadicHodgeJacobianKernelBound constant)
    (depth : ℕ) (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianArraySlice solution t q‖ ≤
      81 * criticalVorticityRate solution t.1 +
        depth * (constant * criticalVorticityRate solution t.1) +
        2 * openPeriodicJacobianCoefficientTailMass solution t
          (frequencyCube (dyadicHodgeInnerCutoff depth)) := by
  refine (norm_openPeriodicTorusJacobianArraySlice_le_dyadicKernelSum_add_tail
    solution t depth q).trans ?_
  have hsum :
    (∑ scale ∈ Finset.range depth,
        dyadicHodgeJacobianKernelL1 scale *
          criticalVorticityRate solution t.1) ≤
      depth * (constant * criticalVorticityRate solution t.1) := by
    calc
      (∑ scale ∈ Finset.range depth,
          dyadicHodgeJacobianKernelL1 scale *
            criticalVorticityRate solution t.1) ≤
        ∑ _scale ∈ Finset.range depth,
          constant * criticalVorticityRate solution t.1 := by
        apply Finset.sum_le_sum
        intro scale _hscale
        exact mul_le_mul_of_nonneg_right (hconstant.2 scale)
          (criticalVorticityRate_nonneg solution t.1)
      _ = depth * (constant * criticalVorticityRate solution t.1) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]
  exact add_le_add (add_le_add (le_refl _) hsum) (le_refl _)

/-- Continuous-field norm version of the same conditional dyadic estimate. -/
theorem norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound'
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) {constant : ℝ}
    (hconstant : UniformDyadicHodgeJacobianKernelBound constant)
    (depth : ℕ) :
    ‖openPeriodicTorusJacobianArraySlice solution t‖ ≤
      81 * criticalVorticityRate solution t.1 +
        depth * (constant * criticalVorticityRate solution t.1) +
        2 * openPeriodicJacobianCoefficientTailMass solution t
          (frequencyCube (dyadicHodgeInnerCutoff depth)) := by
  apply (ContinuousMap.norm_le _ (by
    have hcritical := criticalVorticityRate_nonneg solution t.1
    have htail : 0 ≤ openPeriodicJacobianCoefficientTailMass solution t
        (frequencyCube (dyadicHodgeInnerCutoff depth)) := norm_nonneg _
    have hdepth : 0 ≤ (depth : ℝ) := by positivity
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) hcritical)
        (mul_nonneg hdepth (mul_nonneg hconstant.1 hcritical)))
      (mul_nonneg (by norm_num) htail))).mpr
  intro q
  exact norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound
    solution t hconstant depth q

/-- Receiver projection of the direct dyadic estimate, with the exact matrix-to-operator factor
`9` retained. -/
theorem coordinateJacobianReceiver_le_of_uniformDyadicKernelBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {constant : ℝ}
    (hconstant : UniformDyadicHodgeJacobianKernelBound constant)
    (depth : ℕ) :
    coordinateJacobianReceiver solution t ≤
      9 * (81 * criticalVorticityRate solution t +
        depth * (constant * criticalVorticityRate solution t) +
        2 * openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
          (frequencyCube (dyadicHodgeInnerCutoff depth))) := by
  refine (coordinateJacobianReceiver_le_nine_mul_arraySliceNorm
    solution ht).trans ?_
  exact mul_le_mul_of_nonneg_left
    (norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound'
      solution ⟨t, ht⟩ hconstant depth) (by norm_num)

/-- Quantitative `H^3` decay at the literal outer support radius `2^(depth+1)-1`. -/
theorem openPeriodicJacobianCoefficientTailMass_dyadicOuterCutoff_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (depth : ℕ) :
    openPeriodicJacobianCoefficientTailMass solution ⟨t, ht⟩
        (frequencyCube (dyadicHodgeOuterCutoff depth)) ≤
      (2 * Real.pi) *
        Real.sqrt
          (jacobianTailScale (dyadicHodgeOuterCutoff depth) *
            jacobianTailLatticeMass) *
          Real.sqrt (240 * coordinateLogH3Receiver velocity t) := by
  exact openPeriodicJacobianCoefficientTailMass_frequencyCube_le_logReceiver
    solution ht (dyadicHodgeOuterCutoff depth)

/-- Quantitative decay of the full dyadic reconstruction fibre.  The cutoff is the exact inner
plateau radius because the fibre includes both the finite smooth/sharp transition and the
infinite exterior. -/
theorem norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_logReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (depth : ℕ) (q : SpatialTorus) :
    ‖openPeriodicDyadicHodgeJacobianReconstructionFiber solution ⟨t, ht⟩ depth q‖ ≤
      2 * ((2 * Real.pi) *
        Real.sqrt
          (jacobianTailScale (dyadicHodgeInnerCutoff depth) *
            jacobianTailLatticeMass) *
          Real.sqrt (240 * coordinateLogH3Receiver velocity t)) := by
  refine (norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_two_mul_tailMass
    solution ⟨t, ht⟩ depth q).trans ?_
  exact mul_le_mul_of_nonneg_left
    (openPeriodicJacobianCoefficientTailMass_frequencyCube_le_logReceiver
      solution ht (dyadicHodgeInnerCutoff depth)) (by norm_num)

/-! ## Exact alignment with the balanced sixfold dyadic depth -/

/-- The tail-balance radius is definitionally the inner cutoff of the corresponding dyadic Hodge
word.  There is no antitone or off-by-one passage. -/
theorem dyadicHodgeInnerCutoff_tailDyadicDepth
    (highOrder : ℝ) :
    dyadicHodgeInnerCutoff (jacobianTailDyadicDepth highOrder) =
      jacobianTailDyadicRadius highOrder := by
  rfl

/-- At the receiver-selected sixfold dyadic depth, the complete reconstruction fibre has the
fixed balanced tail bound. -/
theorem norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_balanced_le
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (q : SpatialTorus) :
    ‖openPeriodicDyadicHodgeJacobianReconstructionFiber solution ⟨t, ht⟩
        (jacobianTailDyadicDepth (coordinateLogH3Receiver velocity t)) q‖ ≤
      2 * ((2 * Real.pi) * Real.sqrt 240 *
        Real.sqrt jacobianTailLatticeMass) := by
  refine (norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_two_mul_tailMass
    solution ⟨t, ht⟩
      (jacobianTailDyadicDepth (coordinateLogH3Receiver velocity t)) q).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [dyadicHodgeInnerCutoff_tailDyadicDepth]
  exact openPeriodicJacobianCoefficientTailMass_balanced_le solution ht

/-- The complete pointwise dyadic squeeze at the balanced receiver-selected depth. -/
theorem norm_openPeriodicTorusJacobianArraySlice_balanced_le_of_uniformDyadicKernelBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) {constant : ℝ}
    (hconstant : UniformDyadicHodgeJacobianKernelBound constant)
    (q : SpatialTorus) :
    ‖openPeriodicTorusJacobianArraySlice solution ⟨t, ht⟩ q‖ ≤
      81 * criticalVorticityRate solution t +
        jacobianTailDyadicDepth (coordinateLogH3Receiver velocity t) *
          (constant * criticalVorticityRate solution t) +
        2 * ((2 * Real.pi) * Real.sqrt 240 *
          Real.sqrt jacobianTailLatticeMass) := by
  let depth := jacobianTailDyadicDepth (coordinateLogH3Receiver velocity t)
  refine (norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound
    solution ⟨t, ht⟩ hconstant depth q).trans ?_
  dsimp [depth]
  apply add_le_add (le_refl _)
  rw [dyadicHodgeInnerCutoff_tailDyadicDepth]
  exact mul_le_mul_of_nonneg_left
    (openPeriodicJacobianCoefficientTailMass_balanced_le solution ht)
    (by norm_num)

section Audit

#print axioms dyadicHodgeParameter_add_one
#print axioms dyadicHodgeOuterCutoff_eq
#print axioms openPeriodicDyadicHodgeJacobianLowPass_succ
#print axioms openPeriodicDyadicHodgeJacobianLowPass_eq_base_add_sum_bands
#print axioms mFourierCoeff_dyadicHodgeJacobianKernelEntry
#print axioms dyadicHodgeJacobianKernelConvolution_eq_finiteFourierSynthesis
#print axioms openPeriodicDyadicHodgeJacobianBand_eq_kernelConvolution
#print axioms norm_openPeriodicDyadicHodgeJacobianBand_le_kernelL1_mul_criticalVorticityRate
#print axioms openPeriodicTorusJacobianArraySlice_eq_base_add_sum_dyadicBands_add_fiber
#print axioms norm_openPeriodicTorusJacobianArraySlice_le_of_uniformDyadicKernelBound
#print axioms coordinateJacobianReceiver_le_of_uniformDyadicKernelBound
#print axioms norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_le_logReceiver
#print axioms norm_openPeriodicDyadicHodgeJacobianReconstructionFiber_balanced_le
#print axioms norm_openPeriodicTorusJacobianArraySlice_balanced_le_of_uniformDyadicKernelBound

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain

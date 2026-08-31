import ElementaryHolonics.Millennium.NavierStokesCofinalOutputReceiverClosure
import ElementaryHolonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
import ElementaryHolonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin

/-!
# Exact spatial Parseval join for the cofinal output receiver

**[proved-derived; formal-checked]**  This owner discharges the integrated Fourier/physical join
left explicit by `NavierStokesCofinalOutputReceiverClosure`.  It retains the complete output-parent
population and uses only the scalar torus Parseval identity, finite Hodge reconstruction, Fourier
reality, and absolutely summable smooth coefficient populations.

No pointwise output closure, compact-time passage, terminal estimate, or Navier--Stokes solution
claim is made.
-/

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAnnularHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverClosure
open Soma.Holonics.Millennium.NavierStokesCompleteTransportCofinalCancellation
open Soma.Holonics.Millennium.NavierStokesCompleteTransportReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesCompleteStretchingReceiverWorkJoin
open Soma.Holonics.Millennium.NavierStokesDeLaValleePoussin
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkDecomposition
open Soma.Holonics.Millennium.NavierStokesFiniteLinearWorkPhysicalJoin
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicBandEnergyEvolution
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicLinearPhaseBand
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleAssembly
open Soma.Holonics.Millennium.NavierStokesWeightedReality

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Small scalar Fourier passages -/

/-- Multiplication by one torus character translates the scalar Fourier coefficient exactly. -/
theorem mFourierCoeff_mFourier_mul
    (field : C(SpatialTorus, ℂ)) (shift output : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ UnitAddTorus.mFourier shift q * field q) output =
      UnitAddTorus.mFourierCoeff field (output - shift) := by
  unfold UnitAddTorus.mFourierCoeff
  apply integral_congr_ae
  filter_upwards [] with q
  simp only [smul_eq_mul]
  rw [← mul_assoc]
  rw [← UnitAddTorus.mFourier_add]
  congr 2
  abel

/-- Fourier coefficient of a finite synthesis times one continuous scalar field. -/
theorem mFourierCoeff_finiteFourierSynthesis_mul
    (coefficient : SpatialFrequency → ℂ) (modes : Finset SpatialFrequency)
    (field : C(SpatialTorus, ℂ)) (output : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ finiteFourierSynthesis coefficient modes q * field q)
        output =
      ∑ shift ∈ modes,
        coefficient shift * UnitAddTorus.mFourierCoeff field (output - shift) := by
  classical
  have hintegrable : ∀ shift ∈ modes, Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-output) q *
        ((UnitAddTorus.mFourier shift q * coefficient shift) * field q)) := by
    intro shift _hshift
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-output) q *
            ((UnitAddTorus.mFourier shift q * coefficient shift) * field q)
        continuous_toFun := by fun_prop }
  unfold UnitAddTorus.mFourierCoeff finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, smul_eq_mul, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ hintegrable]
  apply Finset.sum_congr rfl
  intro shift _hshift
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with q
  have hfrequency : -output + shift = -(output - shift) := by abel
  calc
    UnitAddTorus.mFourier (-output) q *
          ((UnitAddTorus.mFourier shift q * coefficient shift) * field q) =
      coefficient shift *
        ((UnitAddTorus.mFourier (-output) q * UnitAddTorus.mFourier shift q) *
          field q) := by ring
    _ = coefficient shift *
        (UnitAddTorus.mFourier (-(output - shift)) q * field q) := by
      rw [← UnitAddTorus.mFourier_add, hfrequency]

/-- Scalar Fourier coefficients commute with a finite sum of continuous fields. -/
theorem mFourierCoeff_finset_sum
    {ι : Type*} (indices : Finset ι) (field : ι → C(SpatialTorus, ℂ))
    (output : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ ∑ index ∈ indices, field index q) output =
      ∑ index ∈ indices,
        UnitAddTorus.mFourierCoeff (field index) output := by
  classical
  unfold UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum]
  intro index _hindex
  exact continuousMap_integrable_on_compact
    { toFun := fun q : SpatialTorus ↦
        UnitAddTorus.mFourier (-output) q * field index q
      continuous_toFun := by fun_prop }

/-- Scalar Parseval for two continuous torus fields, retaining the full coefficient population. -/
theorem tsum_conj_mFourierCoeff_mul_eq_integral
    (left right : C(SpatialTorus, ℂ)) :
    (∑' frequency : SpatialFrequency,
      conj (UnitAddTorus.mFourierCoeff left frequency) *
        UnitAddTorus.mFourierCoeff right frequency) =
      ∫ q : SpatialTorus, conj (left q) * right q := by
  have hparseval := UnitAddTorus.hasSum_prod_mFourierCoeff
    (left.toLp 2 volume ℂ) (right.toLp 2 volume ℂ)
  have hintegral :
      (∫ q : SpatialTorus,
        conj ((left.toLp 2 volume ℂ) q) * (right.toLp 2 volume ℂ) q) =
      ∫ q : SpatialTorus, conj (left q) * right q := by
    have hleft : ((left.toLp 2 volume ℂ : SpatialTorus → ℂ)) =ᵐ[volume] left :=
      left.coeFn_toLp volume
    have hright : ((right.toLp 2 volume ℂ : SpatialTorus → ℂ)) =ᵐ[volume] right :=
      right.coeFn_toLp volume
    apply integral_congr_ae
    filter_upwards [hleft, hright] with q hleftq hrightq
    rw [hleftq, hrightq]
  rw [← hintegral]
  simpa only [UnitAddTorus.mFourierCoeff_toLp] using hparseval.tsum_eq

/-! ## The cumulative finite Hodge word -/

/-- The first `depth` direct Hodge bands are exactly the one cumulative boundary multiplier
mounted in the common native depth aperture. -/
theorem sum_openPeriodicDyadicHodgeJacobianBand_eq_boundarySynthesis
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∑ scale ∈ Finset.range depth,
      openPeriodicDyadicHodgeJacobianBand solution t scale) =
      finiteFourierSynthesis
        (fun frequency ↦
          (finiteDepthBoundaryWeight depth frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (smoothDyadicBandNativeAperture depth) := by
  have hdepth := openPeriodicDyadicHodgeJacobianLowPass_eq_nextAperture
    solution t depth
  have hdepth' : openPeriodicDyadicHodgeJacobianLowPass solution t depth =
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (smoothDyadicBandNativeAperture depth) := by
    simpa only [smoothDyadicBandNativeAperture] using hdepth
  have hzeroBase := openPeriodicDyadicHodgeJacobianLowPass_eq_nextAperture
    solution t 0
  have hzeroSubset :
      frequencyCube (dyadicHodgeOuterCutoff (0 + 1)) ⊆
        smoothDyadicBandNativeAperture depth := by
    unfold smoothDyadicBandNativeAperture
    apply frequencyCube_mono
    rw [dyadicHodgeOuterCutoff_eq, dyadicHodgeOuterCutoff_eq]
    apply Nat.sub_le_sub_right
    unfold dyadicRadius
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzero : openPeriodicDyadicHodgeJacobianLowPass solution t 0 =
      finiteFourierSynthesis
        (fun frequency ↦
          (tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency : ℂ) •
            openPeriodicJacobianFourierMode solution t frequency)
        (smoothDyadicBandNativeAperture depth) := by
    rw [hzeroBase]
    apply finiteFourierSynthesis_eq_of_subset_of_eq_zero
    · exact hzeroSubset
    · intro frequency _houter hinner
      have hnotZero : frequency ∉ frequencyCube (dyadicHodgeOuterCutoff 0) := by
        intro hmem
        exact hinner (frequencyCube_mono (dyadicHodgeOuterCutoff_mono 0) hmem)
      rw [tensorValleePoussinWeight_eq_zero_of_not_mem_outer
        (dyadicHodgeParameter 0) (by
          simpa only [dyadicHodgeOuterCutoff] using hnotZero)]
      simp
  have hword := openPeriodicDyadicHodgeJacobianLowPass_eq_base_add_sum_bands
    solution t depth
  calc
    (∑ scale ∈ Finset.range depth,
        openPeriodicDyadicHodgeJacobianBand solution t scale) =
      openPeriodicDyadicHodgeJacobianLowPass solution t depth -
        openPeriodicDyadicHodgeJacobianLowPass solution t 0 := by
          rw [hword]
          abel
    _ = finiteFourierSynthesis
          (fun frequency ↦
            (tensorValleePoussinWeight (dyadicHodgeParameter depth) frequency : ℂ) •
              openPeriodicJacobianFourierMode solution t frequency)
          (smoothDyadicBandNativeAperture depth) -
        finiteFourierSynthesis
          (fun frequency ↦
            (tensorValleePoussinWeight (dyadicHodgeParameter 0) frequency : ℂ) •
              openPeriodicJacobianFourierMode solution t frequency)
          (smoothDyadicBandNativeAperture depth) := by rw [hdepth', hzero]
    _ = _ := by
      ext q component coordinate
      unfold finiteFourierSynthesis finiteDepthBoundaryWeight
      simp only [ContinuousMap.coe_mk, ContinuousMap.sub_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      simp only [Finset.sum_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro frequency _hfrequency
      push_cast
      ring

/-- The pointwise cumulative Jacobian source before the output-frequency receiver is applied. -/
def finiteDepthCofinalStrainField
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : C(SpatialTorus, ComplexVector) where
  toFun q output := ∑ coordinate : Fin 3,
    (∑ scale ∈ Finset.range depth,
      openPeriodicDyadicHodgeJacobianBand solution t scale q output coordinate) *
        openPeriodicComplexVorticityAt solution t q coordinate
  continuous_toFun := by
    apply continuous_pi
    intro output
    apply continuous_finsetSum
    intro coordinate _hcoordinate
    apply Continuous.mul
    · apply continuous_finsetSum
      intro scale _hscale
      exact (continuous_apply coordinate).comp
        ((continuous_apply output).comp
          (openPeriodicDyadicHodgeJacobianBand solution t scale).continuous)
    · exact (continuous_apply coordinate).comp
        (complexTorusVorticitySlice solution t).continuous

/-- One scalar component of the actual torus vorticity carrier. -/
def openPeriodicVorticityScalarField
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) : C(SpatialTorus, ℂ) where
  toFun q := complexTorusVorticitySlice solution t q component
  continuous_toFun := (continuous_apply component).comp
    (complexTorusVorticitySlice solution t).continuous

theorem mFourierCoeff_openPeriodicVorticityScalarField
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicVorticityScalarField solution t component) frequency =
      openPeriodicVorticityFourierMode solution t frequency component := by
  let projection : ComplexVector →L[ℂ] ℂ :=
    ContinuousLinearMap.proj component
  have hintegrable : Integrable (fun q : SpatialTorus ↦
      UnitAddTorus.mFourier (-frequency) q •
        complexTorusVorticitySlice solution t q) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          UnitAddTorus.mFourier (-frequency) q •
            complexTorusVorticitySlice solution t q
        continuous_toFun := by fun_prop }
  have hprojection := projection.integral_comp_comm hintegrable
  have hmode := congrFun
    (openPeriodicVorticityFourierMode_eq_mFourierCoeff solution t frequency) component
  unfold openPeriodicVorticityScalarField UnitAddTorus.mFourierCoeff
  change (∫ q : SpatialTorus,
      projection (UnitAddTorus.mFourier (-frequency) q •
        complexTorusVorticitySlice solution t q)) = _
  rw [hprojection]
  exact hmode.symm

/-- The cumulative physical source is a finite Jacobian synthesis multiplied by the complete
vorticity field. -/
theorem finiteDepthCofinalStrainField_apply_eq_finiteSynthesis
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (q : SpatialTorus) (output : Fin 3) :
    finiteDepthCofinalStrainField solution t depth q output =
      ∑ coordinate : Fin 3,
        finiteFourierSynthesis
          (fun frequency ↦
            (finiteDepthBoundaryWeight depth frequency : ℂ) *
              openPeriodicJacobianFourierMode solution t frequency output coordinate)
          (smoothDyadicBandNativeAperture depth) q *
            openPeriodicComplexVorticityAt solution t q coordinate := by
  change (∑ coordinate : Fin 3,
      (∑ scale ∈ Finset.range depth,
        openPeriodicDyadicHodgeJacobianBand solution t scale q output coordinate) *
          openPeriodicComplexVorticityAt solution t q coordinate) = _
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  have hentry := congrArg
    (fun field : C(SpatialTorus, ComplexJacobianArray) ↦ field q output coordinate)
    (sum_openPeriodicDyadicHodgeJacobianBand_eq_boundarySynthesis solution t depth)
  rw [show (∑ scale ∈ Finset.range depth,
      openPeriodicDyadicHodgeJacobianBand solution t scale q output coordinate) =
        (∑ scale ∈ Finset.range depth,
          openPeriodicDyadicHodgeJacobianBand solution t scale) q output coordinate by
      simp]
  rw [hentry]
  unfold finiteFourierSynthesis
  simp only [ContinuousMap.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Exact coefficient of the cumulative physical strain source before output truncation. -/
theorem mFourierCoeff_finiteDepthCofinalStrainField
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (⟨fun q : SpatialTorus ↦
            finiteDepthCofinalStrainField solution t depth q output,
          (continuous_apply output).comp
            (finiteDepthCofinalStrainField solution t depth).continuous⟩ :
          C(SpatialTorus, ℂ)) frequency =
      ∑ coordinate : Fin 3, ∑ shift ∈ smoothDyadicBandNativeAperture depth,
        ((finiteDepthBoundaryWeight depth shift : ℂ) *
          openPeriodicJacobianFourierMode solution t shift output coordinate) *
            openPeriodicVorticityFourierMode solution t
              (frequency - shift) coordinate := by
  let sourceComponent : C(SpatialTorus, ℂ) :=
    ⟨fun q : SpatialTorus ↦ finiteDepthCofinalStrainField solution t depth q output,
      (continuous_apply output).comp
        (finiteDepthCofinalStrainField solution t depth).continuous⟩
  let productField : Fin 3 → C(SpatialTorus, ℂ) := fun coordinate ↦
    ⟨fun q : SpatialTorus ↦
      finiteFourierSynthesis
        (fun shift ↦ (finiteDepthBoundaryWeight depth shift : ℂ) *
          openPeriodicJacobianFourierMode solution t shift output coordinate)
        (smoothDyadicBandNativeAperture depth) q *
          openPeriodicVorticityScalarField solution t coordinate q,
      by fun_prop⟩
  have hsource : sourceComponent = ∑ coordinate : Fin 3, productField coordinate := by
    ext q
    exact finiteDepthCofinalStrainField_apply_eq_finiteSynthesis
      solution t depth q output
  change UnitAddTorus.mFourierCoeff sourceComponent frequency = _
  rw [hsource]
  change UnitAddTorus.mFourierCoeff
      (fun q : SpatialTorus ↦ ∑ coordinate : Fin 3, productField coordinate q)
      frequency = _
  rw [mFourierCoeff_finset_sum]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  change UnitAddTorus.mFourierCoeff
      (fun q : SpatialTorus ↦
        finiteFourierSynthesis
          (fun shift ↦ (finiteDepthBoundaryWeight depth shift : ℂ) *
            openPeriodicJacobianFourierMode solution t shift output coordinate)
          (smoothDyadicBandNativeAperture depth) q *
            openPeriodicVorticityScalarField solution t coordinate q) frequency = _
  rw [mFourierCoeff_finiteFourierSynthesis_mul]
  apply Finset.sum_congr rfl
  intro shift _hshift
  rw [mFourierCoeff_openPeriodicVorticityScalarField]

/-! ## Exact finite support of the transported strain multiplier -/

/-- The finite parent population obtained by translating the native transported-frequency
aperture through one fixed output. -/
def finiteDepthStrainParentAperture (depth : ℕ) (output : SpatialFrequency) :
    Finset SpatialFrequency :=
  (smoothDyadicBandNativeAperture depth).image fun shift ↦ output - shift

theorem mem_finiteDepthStrainParentAperture_iff
    (depth : ℕ) (output parent : SpatialFrequency) :
    parent ∈ finiteDepthStrainParentAperture depth output ↔
      output - parent ∈ smoothDyadicBandNativeAperture depth := by
  classical
  constructor
  · intro hparent
    obtain ⟨shift, hshift, haddress⟩ := Finset.mem_image.mp hparent
    have : output - parent = shift := by rw [← haddress]; abel
    simpa only [this] using hshift
  · intro hshift
    apply Finset.mem_image.mpr
    refine ⟨output - parent, hshift, ?_⟩
    abel

/-- The nominally cofinal strain source is actually finite at every fixed depth: the real
transported multiplier restricts its parent population to the translated native aperture. -/
theorem cofinalStrainFilteredSource_eq_finiteAdvectiveCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) :
    cofinalStrainFilteredSource solution t depth output =
      finiteAdvectiveCoefficient (finiteDepthStrainParentAperture depth output)
        (openPeriodicVorticityFourierMode solution t)
        (multiplierFilter
          (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
          (openPeriodicVelocityFourierMode solution t)) output := by
  unfold cofinalStrainFilteredSource finiteAdvectiveCoefficient
  rw [tsum_eq_sum (s := finiteDepthStrainParentAperture depth output)]
  intro parent hparent
  have htransported : transportedFrequencyAt output parent ∉
      smoothDyadicBandNativeAperture depth := by
    simpa only [transportedFrequencyAt] using
      (not_congr (mem_finiteDepthStrainParentAperture_iff depth output parent)).mp hparent
  have hweight := finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture
    depth htransported
  simp [multiplierFilter, hweight, complexAdvectiveInteraction]

/-- Pairing the complete vorticity receiver with the finite-depth cofinal source is exactly the
complete parent fibre already owned by the stretching receiver chart. -/
theorem complexVectorSymmetricPhasePairing_cofinalStrainFilteredSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) :
    complexVectorSymmetricPhasePairing
        (openPeriodicVorticityFourierMode solution t output)
        (cofinalStrainFilteredSource solution t depth output) =
      completeStrainFilteredStretchingPhaseAtOutput solution t depth output := by
  rw [cofinalStrainFilteredSource_eq_finiteAdvectiveCoefficient]
  rw [complexVectorSymmetricPhasePairing_finiteStrainFilteredCoefficient_eq_faceSum]
  unfold completeStrainFilteredStretchingPhaseAtOutput
  rw [tsum_eq_sum (s := finiteDepthStrainParentAperture depth output)]
  intro parent hparent
  have htransported : output - parent ∉ smoothDyadicBandNativeAperture depth :=
    (not_congr (mem_finiteDepthStrainParentAperture_iff depth output parent)).mp hparent
  have hweight := finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture
    depth htransported
  simp [hweight]

/-- The unsymmetrized complete first phase at one output. -/
def completeStrainFilteredFirstPhaseAtOutput
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) : ℂ :=
  ∑' parent : SpatialFrequency,
    (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
      (∑ component : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component (output, parent))

theorem complexVectorHermitianPairing_finsetSum_right
    (left : ComplexVector) (population : SpatialFrequency → ComplexVector)
    (aperture : Finset SpatialFrequency) :
    complexVectorHermitianPairing left
        (∑ parent ∈ aperture, population parent) =
      ∑ parent ∈ aperture,
        complexVectorHermitianPairing left (population parent) := by
  classical
  unfold complexVectorHermitianPairing
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem complexVectorHermitianPairing_weightedStretchingInteraction_eq_firstPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output parent : SpatialFrequency) :
    complexVectorHermitianPairing
        (openPeriodicVorticityFourierMode solution t output)
        (complexAdvectiveInteraction parent (output - parent)
          (openPeriodicVorticityFourierMode solution t parent)
          (multiplierFilter
            (fun frequency ↦ (finiteDepthBoundaryWeight depth frequency : ℂ))
            (openPeriodicVelocityFourierMode solution t) (output - parent))) =
      (finiteDepthBoundaryWeight depth (output - parent) : ℂ) *
        (∑ component : Fin 3, ∑ coordinate : Fin 3,
          completeOpenVorticityStretchingCoordinateFace
            solution t coordinate component (output, parent)) := by
  rw [sum_completeOpenVorticityStretchingCoordinateFace_eq_hermitian]
  unfold complexVectorHermitianPairing complexAdvectiveInteraction multiplierFilter
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  ring

theorem complexVectorHermitianPairing_cofinalStrainFilteredSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (output : SpatialFrequency) :
    complexVectorHermitianPairing
        (openPeriodicVorticityFourierMode solution t output)
        (cofinalStrainFilteredSource solution t depth output) =
      completeStrainFilteredFirstPhaseAtOutput solution t depth output := by
  rw [cofinalStrainFilteredSource_eq_finiteAdvectiveCoefficient]
  unfold finiteAdvectiveCoefficient
  rw [complexVectorHermitianPairing_finsetSum_right]
  apply Eq.trans (Finset.sum_congr rfl fun parent _hparent ↦
    complexVectorHermitianPairing_weightedStretchingInteraction_eq_firstPhase
      solution t depth output parent)
  unfold completeStrainFilteredFirstPhaseAtOutput
  rw [tsum_eq_sum (s := finiteDepthStrainParentAperture depth output)]
  intro parent hparent
  have htransported : output - parent ∉ smoothDyadicBandNativeAperture depth :=
    (not_congr (mem_finiteDepthStrainParentAperture_iff depth output parent)).mp hparent
  have hweight := finiteDepthBoundaryWeight_eq_zero_of_not_mem_nativeAperture
    depth htransported
  simp [hweight]

/-- Finite Parseval identifies the interaction-complete truncated physical receiver with the
complete output-compatible stretching population. -/
theorem integral_cofinalReceiverTruncatedStrainReading_eq_outputCompatible
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∫ q : SpatialTorus,
      cofinalReceiverTruncatedStrainReading solution t depth q) =
      completeOutputCompatibleStrainFilteredStretchingWork solution t depth := by
  unfold cofinalReceiverTruncatedStrainReading
  rw [integral_complexVectorSymmetricPhasePairing_finiteFourierSynthesis]
  unfold completeOutputCompatibleStrainFilteredStretchingWork
  apply Finset.sum_congr rfl
  intro output _houtput
  exact complexVectorSymmetricPhasePairing_cofinalStrainFilteredSource
    solution t depth output

/-- The coefficient of the cumulative physical Hodge source is the exact cofinal convolution
source at the same output. -/
theorem mFourierCoeff_finiteDepthCofinalStrainField_eq_cofinalSource
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (component : Fin 3)
    (frequency : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (⟨fun q : SpatialTorus ↦
            finiteDepthCofinalStrainField solution t depth q component,
          (continuous_apply component).comp
            (finiteDepthCofinalStrainField solution t depth).continuous⟩ :
          C(SpatialTorus, ℂ)) frequency =
      cofinalStrainFilteredSource solution t depth frequency component := by
  classical
  rw [mFourierCoeff_finiteDepthCofinalStrainField]
  rw [cofinalStrainFilteredSource_eq_finiteAdvectiveCoefficient]
  unfold finiteAdvectiveCoefficient finiteDepthStrainParentAperture
  change (∑ coordinate : Fin 3,
      ∑ shift ∈ smoothDyadicBandNativeAperture depth,
        ((finiteDepthBoundaryWeight depth shift : ℂ) *
          openPeriodicJacobianFourierMode solution t shift component coordinate) *
            openPeriodicVorticityFourierMode solution t
              (frequency - shift) coordinate) =
    (∑ parent ∈ (smoothDyadicBandNativeAperture depth).image
        (fun shift ↦ frequency - shift),
      complexAdvectiveInteraction parent (transportedFrequencyAt frequency parent)
        (openPeriodicVorticityFourierMode solution t parent)
        (multiplierFilter
          (fun mode ↦ (finiteDepthBoundaryWeight depth mode : ℂ))
          (openPeriodicVelocityFourierMode solution t)
          (transportedFrequencyAt frequency parent))) component
  rw [Finset.sum_image]
  · simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro shift _hshift
    rw [openPeriodicJacobianFourierMode_eq_fourierJacobianMode]
    unfold fourierJacobianMode complexAdvectiveInteraction multiplierFilter
      transportedFrequencyAt complexDot dotProduct
    simp only [Pi.smul_apply, smul_eq_mul, complexFrequencyVector]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro coordinate _hcoordinate
    have htransport : frequency - (frequency - shift) = shift := by abel
    rw [htransport]
    ring
  · intro first _hfirst second _hsecond heq
    exact sub_right_injective heq

/-- The finite-depth Hodge reading is its literal bilinear receiver/source pairing. -/
theorem finiteDepthDyadicHodgeStrainReading_eq_complexDot_source
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (q : SpatialTorus) (depth : ℕ) :
    finiteDepthDyadicHodgeStrainReading solution t q depth =
      complexDot (openPeriodicComplexVorticityAt solution t q)
        (finiteDepthCofinalStrainField solution t depth q) := by
  let receiver := openPeriodicComplexVorticityAt solution t q
  let bands : ℕ → ComplexMatrix3 := fun scale ↦ Matrix.of fun component coordinate ↦
    openPeriodicDyadicHodgeJacobianBand solution t scale q component coordinate
  have hreading : finiteDepthDyadicHodgeStrainReading solution t q depth =
      ∑ scale ∈ Finset.range depth,
        complexStretchingReading receiver
          (symmetricComplexJacobianPart (bands scale)) := by
    rfl
  rw [hreading]
  simp_rw [complexStretchingReading_symmetricComplexJacobianPart]
  unfold complexStretchingReading complexDot complexMatrixAction Matrix.mulVec dotProduct
  change (∑ scale ∈ Finset.range depth,
      ∑ output : Fin 3, receiver output *
        (∑ coordinate : Fin 3,
          bands scale output coordinate * receiver coordinate)) =
    ∑ output : Fin 3, receiver output *
      (∑ coordinate : Fin 3,
        (∑ scale ∈ Finset.range depth,
          bands scale output coordinate) * receiver coordinate)
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _houtput
  rw [Finset.sum_comm]

/-! ## Complete scalar Parseval assembly -/

/-- Infinite scalar Parseval applied componentwise to the actual vorticity and the cumulative
finite Hodge source.  The finite coordinate sum remains outside the complete output population. -/
theorem integral_finiteDepthDyadicHodgeStrainReading_eq_component_tsum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∫ q : SpatialTorus,
      finiteDepthDyadicHodgeStrainReading solution t q depth) =
      ∑ component : Fin 3, ∑' frequency : SpatialFrequency,
        conj (openPeriodicVorticityFourierMode solution t frequency component) *
          cofinalStrainFilteredSource solution t depth frequency component := by
  have hreading : (∫ q : SpatialTorus,
      finiteDepthDyadicHodgeStrainReading solution t q depth) =
      ∫ q : SpatialTorus,
        complexDot (openPeriodicComplexVorticityAt solution t q)
          (finiteDepthCofinalStrainField solution t depth q) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q ↦
      finiteDepthDyadicHodgeStrainReading_eq_complexDot_source
        solution t q depth
  rw [hreading]
  unfold complexDot dotProduct
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro component _hcomponent
    let left := openPeriodicVorticityScalarField solution t component
    let right : C(SpatialTorus, ℂ) :=
      ⟨fun q : SpatialTorus ↦
          finiteDepthCofinalStrainField solution t depth q component,
        (continuous_apply component).comp
          (finiteDepthCofinalStrainField solution t depth).continuous⟩
    have hparseval := tsum_conj_mFourierCoeff_mul_eq_integral left right
    have hleft (q : SpatialTorus) : conj (left q) = left q := by
      simp [left, openPeriodicVorticityScalarField,
        complexTorusVorticitySlice, complexifySpace]
    calc
      (∫ q : SpatialTorus,
          openPeriodicComplexVorticityAt solution t q component *
            finiteDepthCofinalStrainField solution t depth q component) =
        ∫ q : SpatialTorus, conj (left q) * right q := by
          apply integral_congr_ae
          filter_upwards [] with q
          rw [hleft]
          rfl
      _ = ∑' frequency : SpatialFrequency,
          conj (openPeriodicVorticityFourierMode solution t frequency component) *
            cofinalStrainFilteredSource solution t depth frequency component := by
        rw [← hparseval]
        apply tsum_congr
        intro frequency
        rw [mFourierCoeff_openPeriodicVorticityScalarField]
        rw [mFourierCoeff_finiteDepthCofinalStrainField_eq_cofinalSource]
  · intro component _hcomponent
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          openPeriodicComplexVorticityAt solution t q component *
            finiteDepthCofinalStrainField solution t depth q component
        continuous_toFun := by
          apply Continuous.mul
          · exact (continuous_apply component).comp
              (complexTorusVorticitySlice solution t).continuous
          · exact (continuous_apply component).comp
              (finiteDepthCofinalStrainField solution t depth).continuous }

/-- The complete unsymmetrized first-phase population before the real receiver quotient. -/
def completeStrainFilteredFirstPhaseWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) : ℂ :=
  ∑' address : CompleteStretchingAddress,
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      (∑ component : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component address)

theorem summable_completeStrainFilteredFirstPhasePopulation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    Summable fun address : CompleteStretchingAddress ↦
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        (∑ component : Fin 3, ∑ coordinate : Fin 3,
          completeOpenVorticityStretchingCoordinateFace
            solution t coordinate component address) := by
  have hcoordinates : Summable fun address : CompleteStretchingAddress ↦
      ∑ component : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component address‖ := by
    apply summable_sum
    intro component _hcomponent
    apply summable_sum
    intro coordinate _hcoordinate
    exact summable_norm_completeOpenVorticityStretchingCoordinateFace
      solution t coordinate component
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun address ↦ ?_)
    hcoordinates
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |finiteDepthBoundaryWeight depth (address.1 - address.2)| *
          ‖∑ component : Fin 3, ∑ coordinate : Fin 3,
            completeOpenVorticityStretchingCoordinateFace
              solution t coordinate component address‖ ≤
        ‖∑ component : Fin 3, ∑ coordinate : Fin 3,
          completeOpenVorticityStretchingCoordinateFace
            solution t coordinate component address‖ :=
      mul_le_of_le_one_left (norm_nonneg _)
        (abs_finiteDepthBoundaryWeight_le_one depth (address.1 - address.2))
    _ ≤ ∑ component : Fin 3, ∑ coordinate : Fin 3,
        ‖completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component address‖ :=
      (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun component _hcomponent ↦ norm_sum_le _ _)

theorem completeStrainFilteredFirstPhaseWork_eq_tsum_output
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    completeStrainFilteredFirstPhaseWork solution t depth =
      ∑' output : SpatialFrequency,
        completeStrainFilteredFirstPhaseAtOutput solution t depth output := by
  let population : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      (∑ component : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component address)
  have hpopulation : Summable population :=
    summable_completeStrainFilteredFirstPhasePopulation solution t depth
  have hfiber (output : SpatialFrequency) : Summable fun parent ↦
      population (output, parent) := hpopulation.prod_factor output
  have hprod := hpopulation.tsum_prod' hfiber
  unfold completeStrainFilteredFirstPhaseWork
    completeStrainFilteredFirstPhaseAtOutput
  exact hprod

theorem summable_hermitianCofinalSource_component
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) (component : Fin 3) :
    Summable fun frequency : SpatialFrequency ↦
      conj (openPeriodicVorticityFourierMode solution t frequency component) *
        cofinalStrainFilteredSource solution t depth frequency component := by
  let left := openPeriodicVorticityScalarField solution t component
  let right : C(SpatialTorus, ℂ) :=
    ⟨fun q : SpatialTorus ↦
        finiteDepthCofinalStrainField solution t depth q component,
      (continuous_apply component).comp
        (finiteDepthCofinalStrainField solution t depth).continuous⟩
  have hparseval := (UnitAddTorus.hasSum_prod_mFourierCoeff
    (left.toLp 2 volume ℂ) (right.toLp 2 volume ℂ)).summable
  refine hparseval.congr (fun frequency ↦ ?_)
  simp only [UnitAddTorus.mFourierCoeff_toLp]
  rw [mFourierCoeff_openPeriodicVorticityScalarField]
  rw [mFourierCoeff_finiteDepthCofinalStrainField_eq_cofinalSource]

/-- The physical Hodge integral is the complete unsymmetrized output-parent first phase. -/
theorem integral_finiteDepthDyadicHodgeStrainReading_eq_firstPhaseWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∫ q : SpatialTorus,
      finiteDepthDyadicHodgeStrainReading solution t q depth) =
      completeStrainFilteredFirstPhaseWork solution t depth := by
  rw [integral_finiteDepthDyadicHodgeStrainReading_eq_component_tsum]
  have hcomponents : ∀ component ∈ (Finset.univ : Finset (Fin 3)),
      Summable fun frequency : SpatialFrequency ↦
        conj (openPeriodicVorticityFourierMode solution t frequency component) *
          cofinalStrainFilteredSource solution t depth frequency component := by
    intro component _hcomponent
    exact summable_hermitianCofinalSource_component solution t depth component
  rw [← Summable.tsum_finsetSum hcomponents]
  rw [completeStrainFilteredFirstPhaseWork_eq_tsum_output]
  apply tsum_congr
  intro output
  rw [← complexVectorHermitianPairing_cofinalStrainFilteredSource]
  rfl

/-! ## Negation reality and the symmetric phase quotient -/

theorem openPeriodicVelocityFourierMode_neg_eq_conj
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (frequency : SpatialFrequency) :
    openPeriodicVelocityFourierMode solution t (-frequency) =
      fun component ↦ conj
        (openPeriodicVelocityFourierMode solution t frequency component) := by
  funext component
  unfold openPeriodicVelocityFourierMode
  exact vectorSpatialFourierCoeff_neg_eq_conj
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2).continuous
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    frequency component

theorem openVelocityDirectionalDerivativeH3State_neg_eq_conj
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate component : Fin 3)
    (frequency : SpatialFrequency) :
    (openVelocityDirectionalDerivativeH3State
      solution t coordinate component).1 (-frequency) =
      conj ((openVelocityDirectionalDerivativeH3State
        solution t coordinate component).1 frequency) := by
  rw [openVelocityDirectionalDerivativeH3State_apply_eq_derivative,
    openVelocityDirectionalDerivativeH3State_apply_eq_derivative]
  rw [periodicSobolevThreeDerivative_apply, periodicSobolevThreeDerivative_apply]
  rw [openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode,
    openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode]
  rw [openPeriodicVelocityFourierMode_neg_eq_conj]
  rw [derivativeSymbol_neg_eq_conj frequency coordinate, map_mul]
  simp only [map_mul]

theorem completeOpenVorticityStretchingCoordinateFace_neg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (coordinate component : Fin 3)
    (address : CompleteStretchingAddress) :
    completeOpenVorticityStretchingCoordinateFace solution t coordinate component
        (-address.1, -address.2) =
      conj (completeOpenVorticityStretchingCoordinateFace
        solution t coordinate component address) := by
  have hdifference : -address.1 - -address.2 = -(address.1 - address.2) := by abel
  unfold completeOpenVorticityStretchingCoordinateFace
  rw [openPeriodicVorticityFourierMode_neg_eq_conj,
    openPeriodicVorticityFourierMode_neg_eq_conj, hdifference,
    openVelocityDirectionalDerivativeH3State_neg_eq_conj]
  simp only [map_mul, starRingEnd_self_apply]

theorem completeStretchingFirstPhase_neg
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (address : CompleteStretchingAddress) :
    (∑ component : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate component (-address.1, -address.2)) =
      conj (∑ component : Fin 3, ∑ coordinate : Fin 3,
        completeOpenVorticityStretchingCoordinateFace
          solution t coordinate component address) := by
  simp_rw [completeOpenVorticityStretchingCoordinateFace_neg]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  rw [map_sum]

/-- Simultaneous frequency negation on the complete output-parent address. -/
def completeStretchingNegEquiv : CompleteStretchingAddress ≃ CompleteStretchingAddress :=
  Equiv.prodCongr (Equiv.neg SpatialFrequency) (Equiv.neg SpatialFrequency)

/-- Summing over all output-parent addresses makes the conjugate first phase equal the first
phase itself: simultaneous frequency negation is the exact reconstruction fibre. -/
theorem tsum_completeStrainFiltered_conjFirstPhase_eq_firstPhase
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∑' address : CompleteStretchingAddress,
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        conj (∑ component : Fin 3, ∑ coordinate : Fin 3,
          completeOpenVorticityStretchingCoordinateFace
            solution t coordinate component address)) =
      completeStrainFilteredFirstPhaseWork solution t depth := by
  let first : CompleteStretchingAddress → ℂ := fun address ↦
    ∑ component : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate component address
  let reverse : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      conj (first address)
  let forward : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      first address
  have hreindex :
      (∑' address : CompleteStretchingAddress,
        reverse (completeStretchingNegEquiv address)) =
      ∑' address : CompleteStretchingAddress, reverse address :=
    completeStretchingNegEquiv.tsum_eq reverse
  have hpoint (address : CompleteStretchingAddress) :
      reverse (completeStretchingNegEquiv address) = forward address := by
    change
      (finiteDepthBoundaryWeight depth (-address.1 - -address.2) : ℂ) *
          conj (first (-address.1, -address.2)) =
        (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
          first address
    have hdifference : -address.1 - -address.2 = -(address.1 - address.2) := by abel
    rw [hdifference, finiteDepthBoundaryWeight_neg]
    rw [show first (-address.1, -address.2) = conj (first address) by
      exact completeStretchingFirstPhase_neg solution t address]
    simp
  change (∑' address : CompleteStretchingAddress, reverse address) =
    ∑' address : CompleteStretchingAddress, forward address
  rw [← hreindex]
  exact tsum_congr hpoint

/-- The complete first phase and the symmetric receiver phase have the same global value. -/
theorem completeStrainFilteredFirstPhaseWork_eq_symmetricWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    completeStrainFilteredFirstPhaseWork solution t depth =
      completeStrainFilteredStretchingWork solution t depth := by
  let first : CompleteStretchingAddress → ℂ := fun address ↦
    ∑ component : Fin 3, ∑ coordinate : Fin 3,
      completeOpenVorticityStretchingCoordinateFace
        solution t coordinate component address
  let forward : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      first address
  let reverse : CompleteStretchingAddress → ℂ := fun address ↦
    (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
      conj (first address)
  have hforward : Summable forward :=
    summable_completeStrainFilteredFirstPhasePopulation solution t depth
  have hreverse : Summable reverse := by
    apply Summable.of_norm
    exact hforward.norm.congr (fun address ↦ by
      simp only [forward, reverse, norm_mul, starRingEnd_apply, norm_star])
  have hreverseEq : (∑' address, reverse address) =
      ∑' address, forward address := by
    simpa only [first, reverse, forward,
      completeStrainFilteredFirstPhaseWork] using
      tsum_completeStrainFiltered_conjFirstPhase_eq_firstPhase
        solution t depth
  change (∑' address, forward address) =
    ∑' address : CompleteStretchingAddress,
      (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
        completeOpenVorticityStretchingFace solution t address
  calc
    (∑' address, forward address) =
        (1 / 2 : ℂ) *
          ((∑' address, forward address) + ∑' address, reverse address) := by
      rw [hreverseEq]
      ring
    _ = ∑' address : CompleteStretchingAddress,
        (1 / 2 : ℂ) * (forward address + reverse address) := by
      rw [← hforward.tsum_add hreverse, tsum_mul_left]
    _ = ∑' address : CompleteStretchingAddress,
        (finiteDepthBoundaryWeight depth (address.1 - address.2) : ℂ) *
          completeOpenVorticityStretchingFace solution t address := by
      apply tsum_congr
      intro address
      unfold completeOpenVorticityStretchingFace
      simp only [forward, reverse, first]
      ring

/-- **Exact complete spatial Parseval join.**  The finite Hodge physical reading is the complete
strain-filtered stretching population before output truncation. -/
theorem integral_finiteDepthDyadicHodgeStrainReading_eq_completeStrainFilteredWork
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (depth : ℕ) :
    (∫ q : SpatialTorus,
      finiteDepthDyadicHodgeStrainReading solution t q depth) =
      completeStrainFilteredStretchingWork solution t depth := by
  rw [integral_finiteDepthDyadicHodgeStrainReading_eq_firstPhaseWork,
    completeStrainFilteredFirstPhaseWork_eq_symmetricWork]

/-- **Unconditional receiver-level cofinal closure.**  Spatial integration of the exact physical
output defect is precisely the complete high-output population at every depth. -/
theorem spatialIntegratedCofinalOutputReceiverJoin
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) :
    SpatialIntegratedCofinalOutputReceiverJoin solution t := by
  let _ : MeasureSpace UnitAddCircle := AddCircle.measureSpace 1
  intro depth
  have hvorticityContinuous : Continuous (fun q : SpatialTorus ↦
      openPeriodicComplexVorticityAt solution t q) :=
    (complexTorusVorticitySlice solution t).continuous
  have hfull : Integrable (fun q : SpatialTorus ↦
      finiteDepthDyadicHodgeStrainReading solution t q depth) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          finiteDepthDyadicHodgeStrainReading solution t q depth
        continuous_toFun := by
          unfold finiteDepthDyadicHodgeStrainReading
            complexStretchingReading symmetricComplexJacobianPart
            complexMatrixAction complexDot dotProduct Matrix.mulVec
            openPeriodicDyadicHodgeJacobianBand
          fun_prop }
  have htruncated : Integrable (fun q : SpatialTorus ↦
      cofinalReceiverTruncatedStrainReading solution t depth q) :=
    continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          cofinalReceiverTruncatedStrainReading solution t depth q
        continuous_toFun := by
          unfold cofinalReceiverTruncatedStrainReading
            complexVectorSymmetricPhasePairing complexVectorHermitianPairing
          fun_prop }
  have hvolume :
      @volume SpatialTorus
          (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
            (fun _ ↦
              Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin.instMeasureSpaceUnitAddCircle_elementaryHolonics)) =
        @volume SpatialTorus
          (@MeasureSpace.pi (Fin 3) (Fin.fintype 3) (fun _ ↦ UnitAddCircle)
            (fun _ ↦ AddCircle.measureSpace 1)) := by
    simp only [MeasureTheory.volume_pi]
    congr 1
    funext coordinate
    change AddCircle.haarAddCircle =
      @volume UnitAddCircle (AddCircle.measureSpace 1)
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  have hfullJoin :
      (∫ q : SpatialTorus,
        finiteDepthDyadicHodgeStrainReading solution t q depth) =
        completeStrainFilteredStretchingWork solution t depth := by
    rw [← hvolume]
    exact integral_finiteDepthDyadicHodgeStrainReading_eq_completeStrainFilteredWork
      solution t depth
  have htruncatedJoin :
      (∫ q : SpatialTorus,
        cofinalReceiverTruncatedStrainReading solution t depth q) =
        completeOutputCompatibleStrainFilteredStretchingWork solution t depth := by
    rw [← hvolume]
    exact integral_cofinalReceiverTruncatedStrainReading_eq_outputCompatible
      solution t depth
  unfold finiteDepthCofinalOutputReceiverDefect
  calc
    (∫ q : SpatialTorus,
        finiteDepthDyadicHodgeStrainReading solution t q depth -
          cofinalReceiverTruncatedStrainReading solution t depth q) =
      (∫ q : SpatialTorus,
        finiteDepthDyadicHodgeStrainReading solution t q depth) -
        ∫ q : SpatialTorus,
          cofinalReceiverTruncatedStrainReading solution t depth q :=
      integral_sub hfull htruncated
    _ = completeStrainFilteredStretchingWork solution t depth -
        completeOutputCompatibleStrainFilteredStretchingWork solution t depth := by
      rw [hfullJoin, htruncatedJoin]
    _ = cofinalStrainHighOutputPopulation solution t depth := by
      rw [completeStrainFilteredStretchingWork_eq_outputCompatible_add_highOutput]
      ring

section Audit

#print axioms sum_openPeriodicDyadicHodgeJacobianBand_eq_boundarySynthesis
#print axioms finiteDepthDyadicHodgeStrainReading_eq_complexDot_source
#print axioms integral_finiteDepthDyadicHodgeStrainReading_eq_completeStrainFilteredWork
#print axioms spatialIntegratedCofinalOutputReceiverJoin

end Audit

end Soma.Holonics.Millennium.NavierStokesCofinalOutputReceiverParsevalJoin

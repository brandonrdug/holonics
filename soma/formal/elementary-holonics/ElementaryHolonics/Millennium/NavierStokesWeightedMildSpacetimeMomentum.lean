import ElementaryHolonics.Millennium.NavierStokesWeightedMildInvariantRestart
import ElementaryHolonics.Millennium.NavierStokesWeightedPressureReconstruction
import ElementaryHolonics.Millennium.NavierStokesWeightedSpacetimeReconstruction

/-!
# The honest spacetime momentum return of the weighted mild restart

**[proved-derived]** This owner composes the cap-selected Fourier-real, incompressible mild fixed
path with its complete unprojected quadratic `H²` source, the real `C¹` velocity reconstruction,
and the zero-gauge real `C¹` pressure reconstruction.

The unprojected divergence convolution is first bundled as the missing bounded bilinear passage
`H³ × H³ → H²`.  Consequently its quadratic path and the native pressure path are continuous in
time.  Bounded inverse Fourier passages then return jointly continuous velocity, pressure, and
pressure-gradient fields.  The momentum law itself is retained at its presently justified exact
level: every spatial Fourier coefficient satisfies the full unprojected interior-time ODE.

No pointwise Laplacian or classical spacetime Navier--Stokes equation is asserted.  Such an upgrade
still requires an actual second-spatial-derivative passage for the velocity and a jointly returned
physical realization of the quadratic `H²` source.
-/

noncomputable section

open Function Set
open scoped BigOperators ComplexConjugate ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3Bilinear
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3DivergenceBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinearNorm
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedMildInvariantRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureCoefficient
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction

/-! ## The complete unprojected native quadratic source -/

/-- Weight every output of the complete unprojected divergence convolution into the native
vector `H²` carrier. -/
def weightedUnprojectedDivergenceConvolution
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 2 :=
  fun output ↦ coefficientWeightedRealization 2
    (h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree transported) output)

/-- Unweighting the native source recovers every coefficient of the actual complete convolution. -/
theorem weightedUnprojectedDivergenceConvolution_coefficient
    (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (weightedSobolevCoefficients 2
      (weightedUnprojectedDivergenceConvolution advecting transported output)).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  rw [weightedUnprojectedDivergenceConvolution,
    weightedSobolevCoefficients_coefficientWeightedRealization]

/-- Quantitative native bound for the complete unprojected quadratic source. -/
theorem norm_weightedUnprojectedDivergenceConvolution_le
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    ‖weightedUnprojectedDivergenceConvolution advecting transported‖ ≤
      (1296 * periodicH3EmbeddingConstant) * ‖advecting‖ * ‖transported‖ := by
  let oldAdvecting : PeriodicVectorSobolevThree :=
    fun component ↦ weightedSobolevCoefficients 3 (advecting component)
  let oldTransported : PeriodicVectorSobolevThree :=
    fun component ↦ weightedSobolevCoefficients 3 (transported component)
  have hbase := periodicVectorH2CoefficientNorm_h3DivergenceConvolution_le
    oldAdvecting oldTransported
  have hu := periodicVectorH3CoefficientNorm_unweighted_le advecting
  have hv := periodicVectorH3CoefficientNorm_unweighted_le transported
  have hC := periodicH3EmbeddingConstant_nonneg
  have hu0 := norm_nonneg advecting
  have hv0 := norm_nonneg transported
  have holdU0 := periodicVectorH3CoefficientNorm_nonneg oldAdvecting
  have holdV0 := periodicVectorH3CoefficientNorm_nonneg oldTransported
  calc
    ‖weightedUnprojectedDivergenceConvolution advecting transported‖ ≤
        periodicVectorH2CoefficientNorm
          (h3DivergenceConvolution oldAdvecting oldTransported) :=
      norm_weightedVectorRealization_le_periodicVectorH2CoefficientNorm _
    _ ≤ 144 * periodicH3EmbeddingConstant *
        periodicVectorH3CoefficientNorm oldAdvecting *
          periodicVectorH3CoefficientNorm oldTransported := hbase
    _ ≤ 144 * periodicH3EmbeddingConstant * (3 * ‖advecting‖) *
        (3 * ‖transported‖) := by
      gcongr
    _ = (1296 * periodicH3EmbeddingConstant) * ‖advecting‖ * ‖transported‖ := by
      ring

private theorem summable_unprojectedScalarConvolutionTerms
    (left right : PeriodicSobolevCoefficients 3) (k : SpatialFrequency) :
    Summable fun p ↦ left.1 p * right.1 (k - p) := by
  apply Summable.of_norm
  have hleft := summable_norm_periodicSobolevThreeCoefficient left
  have hbound : Summable fun p ↦ ‖left.1 p‖ * ‖right.1‖ :=
    hleft.mul_right ‖right.1‖
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_) hbound
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) right.1 (k - p))
    (norm_nonneg _)

private theorem unprojected_raw_add_left
    (first second transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree (first + second))
      (unweightedVectorThree transported) output).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree first) (unweightedVectorThree transported) output).1 k +
      (h3DivergenceConvolution
        (unweightedVectorThree second) (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    h3DivergenceConvolution_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  let right := unweightedVectorThree transported output
  let leftFirst := unweightedVectorThree first coordinate
  let leftSecond := unweightedVectorThree second coordinate
  have hfirst := summable_unprojectedScalarConvolutionTerms leftFirst right k
  have hsecond := summable_unprojectedScalarConvolutionTerms leftSecond right k
  have hinner :
      (∑' p, (unweightedVectorThree (first + second) coordinate).1 p *
        (unweightedVectorThree transported output).1 (k - p)) =
        (∑' p, (unweightedVectorThree first coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p)) +
        ∑' p, (unweightedVectorThree second coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.add_apply, lp.coeFn_add]
    dsimp [leftFirst, leftSecond, right]
    ring
  rw [hinner]
  ring

private theorem unprojected_raw_add_right
    (advecting first second : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree (first + second)) output).1 k =
      (h3DivergenceConvolution
        (unweightedVectorThree advecting) (unweightedVectorThree first) output).1 k +
      (h3DivergenceConvolution
        (unweightedVectorThree advecting) (unweightedVectorThree second) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    h3DivergenceConvolution_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := unweightedVectorThree advecting coordinate
  let rightFirst := unweightedVectorThree first output
  let rightSecond := unweightedVectorThree second output
  have hfirst := summable_unprojectedScalarConvolutionTerms left rightFirst k
  have hsecond := summable_unprojectedScalarConvolutionTerms left rightSecond k
  have hinner :
      (∑' p, (unweightedVectorThree advecting coordinate).1 p *
        (unweightedVectorThree (first + second) output).1 (k - p)) =
        (∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree first output).1 (k - p)) +
        ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree second output).1 (k - p) := by
    rw [← hfirst.tsum_add hsecond]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.add_apply, lp.coeFn_add]
    dsimp [left, rightFirst, rightSecond]
    ring
  rw [hinner]
  ring

private theorem unprojected_raw_smul_left
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree (c • advecting))
      (unweightedVectorThree transported) output).1 k =
      c * (h3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := unweightedVectorThree advecting coordinate
  let right := unweightedVectorThree transported output
  have hterms := summable_unprojectedScalarConvolutionTerms left right k
  have hinner :
      (∑' p, (unweightedVectorThree (c • advecting) coordinate).1 p *
        (unweightedVectorThree transported output).1 (k - p)) =
        c * ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.smul_apply, lp.coeFn_smul,
      smul_eq_mul]
    dsimp [left, right]
    ring
  rw [hinner]
  ring

private theorem unprojected_raw_smul_right
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3)
    (output : Fin 3) (k : SpatialFrequency) :
    (h3DivergenceConvolution
      (unweightedVectorThree advecting)
      (unweightedVectorThree (c • transported)) output).1 k =
      c * (h3DivergenceConvolution
        (unweightedVectorThree advecting)
        (unweightedVectorThree transported) output).1 k := by
  rw [h3DivergenceConvolution_apply, h3DivergenceConvolution_apply,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  let left := unweightedVectorThree advecting coordinate
  let right := unweightedVectorThree transported output
  have hterms := summable_unprojectedScalarConvolutionTerms left right k
  have hinner :
      (∑' p, (unweightedVectorThree advecting coordinate).1 p *
        (unweightedVectorThree (c • transported) output).1 (k - p)) =
        c * ∑' p, (unweightedVectorThree advecting coordinate).1 p *
          (unweightedVectorThree transported output).1 (k - p) := by
    rw [← hterms.tsum_mul_left c]
    apply tsum_congr
    intro p
    simp only [unweightedVectorThree_coefficient, Pi.smul_apply, lp.coeFn_smul,
      smul_eq_mul]
    dsimp [left, right]
    ring
  rw [hinner]
  ring

theorem weightedUnprojectedDivergenceConvolution_add_left
    (first second transported : PeriodicVectorWeightedSobolev 3) :
    weightedUnprojectedDivergenceConvolution (first + second) transported =
      weightedUnprojectedDivergenceConvolution first transported +
        weightedUnprojectedDivergenceConvolution second transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [weightedUnprojectedDivergenceConvolution,
    coefficientWeightedRealization_apply, lp.coeFn_add, Pi.add_apply]
  rw [unprojected_raw_add_left]
  ring

theorem weightedUnprojectedDivergenceConvolution_add_right
    (advecting first second : PeriodicVectorWeightedSobolev 3) :
    weightedUnprojectedDivergenceConvolution advecting (first + second) =
      weightedUnprojectedDivergenceConvolution advecting first +
        weightedUnprojectedDivergenceConvolution advecting second := by
  funext output
  apply Subtype.ext
  funext k
  simp only [weightedUnprojectedDivergenceConvolution,
    coefficientWeightedRealization_apply, lp.coeFn_add, Pi.add_apply]
  rw [unprojected_raw_add_right]
  ring

theorem weightedUnprojectedDivergenceConvolution_smul_left
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedUnprojectedDivergenceConvolution (c • advecting) transported =
      c • weightedUnprojectedDivergenceConvolution advecting transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [weightedUnprojectedDivergenceConvolution,
    coefficientWeightedRealization_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [unprojected_raw_smul_left]
  ring

theorem weightedUnprojectedDivergenceConvolution_smul_right
    (c : ℂ) (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedUnprojectedDivergenceConvolution advecting (c • transported) =
      c • weightedUnprojectedDivergenceConvolution advecting transported := by
  funext output
  apply Subtype.ext
  funext k
  simp only [weightedUnprojectedDivergenceConvolution,
    coefficientWeightedRealization_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [unprojected_raw_smul_right]
  ring

/-- The complete unprojected `H³ × H³ → H²` source as a bounded bilinear passage. -/
def weightedUnprojectedDivergenceConvolutionContinuous :
    PeriodicVectorWeightedSobolev 3 →L[ℂ]
      PeriodicVectorWeightedSobolev 3 →L[ℂ]
        PeriodicVectorWeightedSobolev 2 :=
  (LinearMap.mk₂ ℂ weightedUnprojectedDivergenceConvolution
    weightedUnprojectedDivergenceConvolution_add_left
    weightedUnprojectedDivergenceConvolution_smul_left
    weightedUnprojectedDivergenceConvolution_add_right
    weightedUnprojectedDivergenceConvolution_smul_right).mkContinuous₂
      (1296 * periodicH3EmbeddingConstant)
      norm_weightedUnprojectedDivergenceConvolution_le

@[simp]
theorem weightedUnprojectedDivergenceConvolutionContinuous_apply
    (advecting transported : PeriodicVectorWeightedSobolev 3) :
    weightedUnprojectedDivergenceConvolutionContinuous advecting transported =
      weightedUnprojectedDivergenceConvolution advecting transported :=
  rfl

/-- The diagonal of the bounded bilinear source. -/
def weightedUnprojectedQuadratic
    (state : PeriodicVectorWeightedSobolev 3) :
    PeriodicVectorWeightedSobolev 2 :=
  weightedUnprojectedDivergenceConvolutionContinuous state state

theorem continuous_weightedUnprojectedQuadratic :
    Continuous weightedUnprojectedQuadratic := by
  exact weightedUnprojectedDivergenceConvolutionContinuous.continuous.clm_apply
    continuous_id

/-- The source used by the pressure owner is exactly the new bounded quadratic passage. -/
theorem weightedUnprojectedDivergenceState_eq_quadratic
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    weightedUnprojectedDivergenceState hT path t =
      weightedUnprojectedQuadratic (weightedPathExtension hT path t) :=
  rfl

/-! ## Continuous source and pressure paths -/

/-- The actual complete quadratic `H²` source along a native path. -/
def weightedUnprojectedQuadraticPath
    {T : ℝ} (path : WeightedH3Path T) :
    C(Icc (0 : ℝ) T, PeriodicVectorWeightedSobolev 2) where
  toFun t := weightedUnprojectedQuadratic (path t)
  continuous_toFun := continuous_weightedUnprojectedQuadratic.comp path.continuous

@[simp]
theorem weightedUnprojectedQuadraticPath_apply
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : Icc (0 : ℝ) T) :
    weightedUnprojectedQuadraticPath path t =
      weightedUnprojectedDivergenceState hT path t.1 := by
  change weightedUnprojectedQuadratic (path t) =
    weightedUnprojectedQuadratic (weightedPathExtension hT path t.1)
  rw [weightedPathExtension_of_mem hT path t.2]

/-- The native scalar `H³` pressure is a continuous path, not merely a collection of slices. -/
def weightedNativePressurePath
    {T : ℝ} (path : WeightedH3Path T) :
    C(Icc (0 : ℝ) T, PeriodicWeightedSobolev 3) where
  toFun t := nativePressureFromH2 (weightedUnprojectedQuadraticPath path t)
  continuous_toFun := nativePressureFromH2.continuous.comp
    (weightedUnprojectedQuadraticPath path).continuous

@[simp]
theorem weightedNativePressurePath_apply
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : Icc (0 : ℝ) T) :
    weightedNativePressurePath path t = weightedNativePressure hT path t.1 := by
  change nativePressureFromH2 (weightedUnprojectedQuadraticPath path t) =
    nativePressureFromH2 (weightedUnprojectedDivergenceState hT path t.1)
  rw [weightedUnprojectedQuadraticPath_apply hT]

/-- Repeat the scalar pressure state in three addressed components so the existing joint vector
reconstruction passage can be reused without discarding the scalar lineage. -/
def weightedNativePressureDiagonalPath
    {T : ℝ} (path : WeightedH3Path T) : WeightedH3Path T where
  toFun t := scalarNativeDiagonalVector (weightedNativePressurePath path t)
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro component
    simpa only [scalarNativeDiagonalVector] using
      (weightedNativePressurePath path).continuous

@[simp]
theorem weightedNativePressureDiagonalPath_apply
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (t : Icc (0 : ℝ) T) :
    weightedNativePressureDiagonalPath path t =
      scalarNativeDiagonalVector (weightedNativePressure hT path t.1) := by
  change scalarNativeDiagonalVector (weightedNativePressurePath path t) = _
  rw [weightedNativePressurePath_apply]

/-- The actual real pressure is jointly continuous in space and addressed restart time. -/
theorem continuous_joint_weightedReconstructedPressure
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      weightedReconstructedPressure hT path z.2.1 z.1) := by
  have hjoint := continuous_joint_reconstructedVelocity
    (weightedNativePressureDiagonalPath path)
  have hcomponent : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      reconstructedVelocity
        (weightedNativePressureDiagonalPath path z.2) z.1 (0 : Fin 3)) :=
    (EuclideanSpace.proj (0 : Fin 3)).continuous.comp hjoint
  convert hcomponent using 1
  funext z
  rw [weightedNativePressureDiagonalPath_apply]
  rfl

/-! ## Bounded first-derivative reconstruction and joint pressure-gradient continuity -/

/-- The fixed `H³ → C⁰` constant for one addressed spatial derivative. -/
def scalarPressureGradientUniformConstant (coordinate : Fin 3) : ℝ :=
  2 * Real.pi * ‖coordinateReciprocalSobolevThreeSqrt coordinate‖

theorem scalarPressureGradientUniformConstant_nonneg (coordinate : Fin 3) :
    0 ≤ scalarPressureGradientUniformConstant coordinate := by
  unfold scalarPressureGradientUniformConstant
  positivity

private theorem weightedSobolevThreeCoefficient_weightedCoefficients
    (state : PeriodicWeightedSobolev 3) :
    weightedSobolevThreeCoefficient (weightedSobolevCoefficients 3 state) = state := by
  change coefficientWeightedRealization 3
    (weightedSobolevCoefficients 3 state) = state
  exact coefficientWeightedRealization_weightedSobolevCoefficients 3 state

private theorem coordinateReciprocal_mul_weighted_eq
    (coeff : PeriodicSobolevCoefficients 3) (coordinate : Fin 3)
    (k : SpatialFrequency) :
    ‖coordinateReciprocalSobolevThreeSqrt coordinate k‖ *
        ‖weightedSobolevThreeCoefficient coeff k‖ =
      |(k coordinate : ℝ)| * ‖coeff.1 k‖ := by
  have hweightPos : 0 < periodicSobolevWeight 3 k :=
    periodicSobolevWeight_pos 3 k
  have hsqrtPos : 0 < Real.sqrt (periodicSobolevWeight 3 k) :=
    Real.sqrt_pos.2 hweightPos
  simp only [coordinateReciprocalSobolevThreeSqrt,
    weightedSobolevThreeCoefficient, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_div, abs_of_nonneg (abs_nonneg _),
    abs_of_pos hsqrtPos]
  field_simp

private theorem norm_scalarPressureGradientPassage_eq
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (k : SpatialFrequency) :
    ‖scalarPressureGradientCoefficient state coordinate k •
        UnitAddTorus.mFourier k‖ =
      (2 * Real.pi) *
        (‖coordinateReciprocalSobolevThreeSqrt coordinate k‖ *
          ‖weightedSobolevThreeCoefficient
            (weightedSobolevCoefficients 3 state) k‖) := by
  rw [coordinateReciprocal_mul_weighted_eq]
  simp only [norm_smul, UnitAddTorus.mFourier_norm, mul_one,
    scalarPressureGradientCoefficient, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, Complex.norm_intCast]
  ring

/-- Quantitative uniform first-derivative synthesis bound. -/
theorem norm_reconstructedScalarTorusGradient_le
    (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    ‖reconstructedScalarTorusGradient state coordinate‖ ≤
      scalarPressureGradientUniformConstant coordinate * ‖state‖ := by
  have hholder :
      (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal := by
    simpa only [ENNReal.toReal_ofNat] using Real.HolderConjugate.two_two
  let reciprocal := coordinateReciprocalSobolevThreeSqrt coordinate
  let weighted := weightedSobolevThreeCoefficient
    (weightedSobolevCoefficients 3 state)
  have hproduct : Summable fun k : SpatialFrequency ↦
      ‖reciprocal k‖ * ‖weighted k‖ :=
    lp.summable_mul hholder reciprocal weighted
  have hcs : (∑' k : SpatialFrequency, ‖reciprocal k‖ * ‖weighted k‖) ≤
      ‖reciprocal‖ * ‖weighted‖ :=
    lp.tsum_mul_le_mul_norm' hholder reciprocal weighted
  have hpassageNorm : Summable fun k : SpatialFrequency ↦
      ‖scalarPressureGradientCoefficient state coordinate k •
        UnitAddTorus.mFourier k‖ := by
    have hscaled := hproduct.mul_left (2 * Real.pi)
    exact hscaled.congr (fun k ↦
      (norm_scalarPressureGradientPassage_eq state coordinate k).symm)
  calc
    ‖reconstructedScalarTorusGradient state coordinate‖ ≤
        ∑' k : SpatialFrequency,
          ‖scalarPressureGradientCoefficient state coordinate k •
            UnitAddTorus.mFourier k‖ :=
      norm_tsum_le_tsum_norm
        hpassageNorm
    _ = ∑' k : SpatialFrequency,
        (2 * Real.pi) * (‖reciprocal k‖ * ‖weighted k‖) := by
      apply tsum_congr
      intro k
      exact norm_scalarPressureGradientPassage_eq state coordinate k
    _ = (2 * Real.pi) *
        ∑' k : SpatialFrequency, ‖reciprocal k‖ * ‖weighted k‖ := by
      rw [hproduct.tsum_mul_left]
    _ ≤ (2 * Real.pi) * (‖reciprocal‖ * ‖weighted‖) := by
      exact mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = scalarPressureGradientUniformConstant coordinate * ‖state‖ := by
      rw [show weighted = state by
        exact weightedSobolevThreeCoefficient_weightedCoefficients state]
      simp only [scalarPressureGradientUniformConstant, reciprocal]
      ring

@[simp]
theorem scalarPressureGradientCoefficient_add
    (left right : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (k : SpatialFrequency) :
    scalarPressureGradientCoefficient (left + right) coordinate k =
      scalarPressureGradientCoefficient left coordinate k +
        scalarPressureGradientCoefficient right coordinate k := by
  simp [scalarPressureGradientCoefficient, weightedSobolevCoefficients,
    weightedSobolevRawCoefficients, mul_add]

@[simp]
theorem scalarPressureGradientCoefficient_smul
    (c : ℂ) (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3)
    (k : SpatialFrequency) :
    scalarPressureGradientCoefficient (c • state) coordinate k =
      c * scalarPressureGradientCoefficient state coordinate k := by
  simp [scalarPressureGradientCoefficient, weightedSobolevCoefficients,
    weightedSobolevRawCoefficients]
  ring

theorem reconstructedScalarTorusGradient_add
    (left right : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    reconstructedScalarTorusGradient (left + right) coordinate =
      reconstructedScalarTorusGradient left coordinate +
        reconstructedScalarTorusGradient right coordinate := by
  rw [reconstructedScalarTorusGradient, reconstructedScalarTorusGradient,
    reconstructedScalarTorusGradient,
    ← (summable_scalarPressureGradientPassages left coordinate).tsum_add
      (summable_scalarPressureGradientPassages right coordinate)]
  apply tsum_congr
  intro k
  rw [scalarPressureGradientCoefficient_add]
  exact add_smul
    (scalarPressureGradientCoefficient left coordinate k : ℂ)
    (scalarPressureGradientCoefficient right coordinate k : ℂ)
    (UnitAddTorus.mFourier k : C(SpatialTorus, ℂ))

theorem reconstructedScalarTorusGradient_smul
    (c : ℂ) (state : PeriodicWeightedSobolev 3) (coordinate : Fin 3) :
    reconstructedScalarTorusGradient (c • state) coordinate =
      c • reconstructedScalarTorusGradient state coordinate := by
  rw [reconstructedScalarTorusGradient, reconstructedScalarTorusGradient,
    ← (summable_scalarPressureGradientPassages state coordinate).tsum_const_smul c]
  apply tsum_congr
  intro k
  rw [scalarPressureGradientCoefficient_smul, mul_smul]

/-- Bounded reconstruction of one addressed pressure-gradient component. -/
def scalarPressureGradientReconstructionCLM (coordinate : Fin 3) :
    PeriodicWeightedSobolev 3 →L[ℂ] C(SpatialTorus, ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun state ↦ reconstructedScalarTorusGradient state coordinate
      map_add' := fun left right ↦
        reconstructedScalarTorusGradient_add left right coordinate
      map_smul' := fun c state ↦
        reconstructedScalarTorusGradient_smul c state coordinate }
    (scalarPressureGradientUniformConstant coordinate)
    (fun state ↦ norm_reconstructedScalarTorusGradient_le state coordinate)

@[simp]
theorem scalarPressureGradientReconstructionCLM_apply
    (coordinate : Fin 3) (state : PeriodicWeightedSobolev 3) :
    scalarPressureGradientReconstructionCLM coordinate state =
      reconstructedScalarTorusGradient state coordinate :=
  rfl

/-- The complex torus pressure gradient along the complete native pressure path. -/
def weightedPressureGradientTorusPath
    {T : ℝ} (path : WeightedH3Path T) (coordinate : Fin 3) :
    C(Icc (0 : ℝ) T, C(SpatialTorus, ℂ)) where
  toFun t := scalarPressureGradientReconstructionCLM coordinate
    (weightedNativePressurePath path t)
  continuous_toFun :=
    (scalarPressureGradientReconstructionCLM coordinate).continuous.comp
      (weightedNativePressurePath path).continuous

@[simp]
theorem weightedPressureGradientTorusPath_apply
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (coordinate : Fin 3) (t : Icc (0 : ℝ) T) :
    weightedPressureGradientTorusPath path coordinate t =
      reconstructedScalarTorusGradient
        (weightedNativePressure hT path t.1) coordinate := by
  change scalarPressureGradientReconstructionCLM coordinate
      (weightedNativePressurePath path t) = _
  rw [weightedNativePressurePath_apply]
  rfl

/-- The complex pressure-gradient synthesis is jointly continuous on time and the genuine torus. -/
theorem continuous_joint_weightedPressureGradientTorus
    {T : ℝ} (path : WeightedH3Path T) (coordinate : Fin 3) :
    Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
      reconstructedScalarTorusGradient
        (weightedNativePressurePath path z.1) coordinate z.2) := by
  change Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
    weightedPressureGradientTorusPath path coordinate z.1 z.2)
  exact ((weightedPressureGradientTorusPath path coordinate).continuous.comp
    continuous_fst).eval continuous_snd

/-- Every addressed component of the actual real pressure gradient is jointly continuous in
space and restart time. -/
theorem continuous_joint_weightedReconstructedPressureGradient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (coordinate : Fin 3) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      weightedReconstructedPressureGradient hT path z.2.1 coordinate z.1) := by
  have hrebase : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      (z.2, euclideanToSpatialTorus z.1)) :=
    continuous_snd.prodMk
      (euclideanToSpatialTorus_isOpenQuotientMap.continuous.comp continuous_fst)
  have hcomplex := (continuous_joint_weightedPressureGradientTorus path coordinate).comp
    hrebase
  have hreal := Complex.continuous_re.comp hcomplex
  convert hreal using 1
  funext z
  simp only [Function.comp_apply]
  change
    (reconstructedScalarTorusGradient
      (weightedNativePressure hT path z.2.1) coordinate
        (euclideanToSpatialTorus z.1)).re =
    (reconstructedScalarTorusGradient
      (weightedNativePressurePath path z.2) coordinate
        (euclideanToSpatialTorus z.1)).re
  rw [weightedNativePressurePath_apply hT]

/-! ## The reconstructed velocity and exact full modal momentum equation -/

/-- The actual real velocity reconstructed from the endpoint-totalized native path. -/
def weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    InitialVelocity :=
  reconstructedVelocity (weightedPathExtension hT path t)

theorem continuous_weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    Continuous (weightedReconstructedVelocity hT path t) :=
  continuous_reconstructedVelocity _

theorem contDiff_one_weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    ContDiff ℝ 1 (weightedReconstructedVelocity hT path t) :=
  contDiff_one_reconstructedVelocity _

theorem isOnePeriodic_weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) (t : ℝ) :
    IsOnePeriodic (weightedReconstructedVelocity hT path t) :=
  isOnePeriodic_reconstructedVelocity _

/-- The actual real velocity is jointly continuous in space and addressed restart time. -/
theorem continuous_joint_weightedReconstructedVelocity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      weightedReconstructedVelocity hT path z.2.1 z.1) := by
  have hjoint :=
    Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction.continuous_joint_reconstructedVelocity
      path
  convert hjoint using 1
  funext z
  change reconstructedVelocity (weightedPathExtension hT path z.2.1) z.1 =
    reconstructedVelocity (path z.2) z.1
  rw [weightedPathExtension_of_mem hT path z.2.2]

/-- One actual spatial Fourier coefficient of the reconstructed velocity field. -/
def weightedReconstructedVelocityCoefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (component : Fin 3) (k : SpatialFrequency) (t : ℝ) : ℂ :=
  vectorSpatialFourierCoeff (weightedReconstructedVelocity hT path t)
    (continuous_weightedReconstructedVelocity hT path t)
    (isOnePeriodic_weightedReconstructedVelocity hT path t) k component

/-- Fourier reality makes the actual field coefficient exactly the native unweighted path
coefficient, including on the endpoint extension. -/
theorem weightedReconstructedVelocityCoefficient_eq_native
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path)
    (component : Fin 3) (k : SpatialFrequency) (t : ℝ) :
    weightedReconstructedVelocityCoefficient hT path component k t =
      (weightedSobolevCoefficients 3
        (weightedPathExtension hT path t component)).1 k := by
  exact vectorSpatialFourierCoeff_reconstructedVelocity_eq_unweighted
    (hpath.extension hT t) k component

/-- The reconstructed real velocity retains exact modewise incompressibility. -/
theorem reconstructedVelocityCoefficient_divergence_eq_zero
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath path)
    (hdivergence : IsWeightedDivergenceFreePath path)
    (k : SpatialFrequency) (t : ℝ) :
    ∑ component : Fin 3,
        complexFrequencyVector k component *
          weightedReconstructedVelocityCoefficient hT path component k t = 0 := by
  have hnative := hdivergence.extension hT t k
  have hnativeSum :
      (∑ component : Fin 3,
        complexFrequencyVector k component *
          weightedPathExtension hT path t component k) = 0 := by
    simpa [complexDot, dotProduct, vectorCoefficientAt] using hnative
  simp_rw [weightedReconstructedVelocityCoefficient_eq_native hT hreal]
  change ∑ component : Fin 3,
      complexFrequencyVector k component *
        ((((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ) *
          weightedPathExtension hT path t component k) = 0
  let C : ℂ := (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ)
  calc
    (∑ component : Fin 3,
        complexFrequencyVector k component *
          (C * weightedPathExtension hT path t component k)) =
        C * ∑ component : Fin 3,
          complexFrequencyVector k component *
            weightedPathExtension hT path t component k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ = 0 := by
      rw [hnativeSum, mul_zero]

/-- One actual Fourier coefficient of the reconstructed real pressure-gradient component. -/
def weightedReconstructedPressureGradientCoefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (coordinate : Fin 3) (k : SpatialFrequency) (t : ℝ) : ℂ :=
  scalarSpatialFourierCoeff
    (fun x ↦
      (weightedReconstructedPressureGradient hT path t coordinate x : ℂ))
    (Complex.continuous_ofReal.comp
      (continuous_weightedReconstructedPressureGradient
        hT path t coordinate))
    (fun x shiftedCoordinate ↦ congrArg (fun r : ℝ ↦ (r : ℂ))
      (isOnePeriodic_weightedReconstructedPressureGradient
        hT path t coordinate x shiftedCoordinate)) k

/-- The actual reconstructed pressure-gradient coefficient is exactly the multiplier used in the
unprojected modal momentum theorem. -/
theorem weightedReconstructedPressureGradientCoefficient_eq_frequencyGradient
    {T : ℝ} (hT : 0 ≤ T) {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path)
    (coordinate : Fin 3) (k : SpatialFrequency) (t : ℝ) :
    weightedReconstructedPressureGradientCoefficient
        hT path coordinate k t =
      pressureFrequencyGradient k
        (weightedPressureCoefficient hT path t k) coordinate := by
  have hactual :=
    scalarSpatialFourierCoeff_weightedReconstructedPressureGradient
      hT hpath t coordinate k
  have hmodal := congrFun
    (pressureFrequencyGradient_weightedPressureCoefficient hT path t k)
    coordinate
  exact hactual.trans hmodal.symm

/-- The native `H²` quadratic source coefficient is exactly the complete unprojected convolution
mode; no physical source is hidden behind the Leray projection. -/
theorem weightedUnprojectedDivergenceState_coefficient
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T)
    (component : Fin 3) (k : SpatialFrequency) (t : ℝ) :
    (weightedSobolevCoefficients 2
      (weightedUnprojectedDivergenceState hT path t component)).1 k =
      weightedUnprojectedDivergenceMode hT path t k component := by
  exact congrFun
    (physicalH2Mode_weightedUnprojectedDivergenceState hT path t k)
    component

/-- **Exact reconstructed full modal momentum equation.**  Every coefficient of the actual real
velocity field has the viscous decay, complete unprojected quadratic `H²` source coefficient, and
actual reconstructed pressure-gradient coefficient at every interior restart time. -/
theorem fixedPoint_weightedMildMap_reconstructedMomentum_hasDerivAt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (initial : PeriodicVectorWeightedSobolev 3) {path : WeightedH3Path T}
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) path)
    (hreal : IsWeightedFourierRealPath path)
    (component : Fin 3) (k : SpatialFrequency) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau : ℝ ↦
        weightedReconstructedVelocityCoefficient hT path component k tau)
      (((-((nu : ℝ) * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient hT path component k t -
        (weightedSobolevCoefficients 2
          (weightedUnprojectedDivergenceState hT path t component)).1 k -
        weightedReconstructedPressureGradientCoefficient
          hT path component k t) t := by
  have hnative := fixedPoint_weightedMildMap_unprojectedMomentum_hasDerivAt
    nu hnu hT initial path hfixed component k ht
  have hfunction :
      (fun tau : ℝ ↦
        weightedReconstructedVelocityCoefficient hT path component k tau) =
      (fun tau : ℝ ↦
        (weightedSobolevCoefficients 3
          (weightedPathExtension hT path tau component)).1 k) := by
    funext tau
    exact weightedReconstructedVelocityCoefficient_eq_native
      hT hreal component k tau
  rw [hfunction,
    weightedReconstructedVelocityCoefficient_eq_native hT hreal,
    weightedUnprojectedDivergenceState_coefficient,
    weightedReconstructedPressureGradientCoefficient_eq_frequencyGradient
      hT hreal]
  exact hnative

/-! ## The cap-selected spacetime return and the explicit classical-upgrade aperture -/

/-- The genuinely additional regularity required before the modal return could be promoted to a
pointwise velocity equation: two spatial derivatives of every velocity slice and a strong
interior time derivative of the reconstructed field.  The present `H³` mild construction proves
neither clause, and this predicate is not assumed by the modal theorem below. -/
def HasClassicalMomentumUpgradeRegularity
    {T : ℝ} (hT : 0 ≤ T) (path : WeightedH3Path T) : Prop :=
  (∀ t ∈ Ioo (0 : ℝ) T,
      ContDiff ℝ 2 (weightedReconstructedVelocity hT path t)) ∧
    (∀ x : Space,
      DifferentiableOn ℝ
        (fun t : ℝ ↦ weightedReconstructedVelocity hT path t x)
        (Ioo (0 : ℝ) T))

/-- The complete honest return carried by one cap-selected mild restart.  Its momentum field is
exact coefficientwise; its spatial velocity, pressure, and pressure-gradient faces are actual
jointly continuous real periodic fields. -/
structure WeightedMildSpacetimeMomentumReturn
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) where
  path : WeightedH3Path (weightedRestartTimeFromCap nu cap)
  norm_le : ‖path‖ ≤ weightedRestartRadiusFromCap cap
  fixed : IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) path
  initialFace :
    path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial
  fourierReal : IsWeightedFourierRealPath path
  divergenceFree : IsWeightedDivergenceFreePath path
  spatialVelocityC1 : ∀ t : ℝ,
    ContDiff ℝ 1 (weightedReconstructedVelocity
      (weightedRestartTimeFromCap_pos hnu hcap).le path t)
  spatialVelocityPeriodic : ∀ t : ℝ,
    IsOnePeriodic (weightedReconstructedVelocity
      (weightedRestartTimeFromCap_pos hnu hcap).le path t)
  spatialPressureC1 : ∀ t : ℝ,
    ContDiff ℝ 1 (weightedReconstructedPressure
      (weightedRestartTimeFromCap_pos hnu hcap).le path t)
  spatialPressurePeriodic : ∀ t : ℝ,
    IsOnePeriodic (weightedReconstructedPressure
      (weightedRestartTimeFromCap_pos hnu hcap).le path t)
  jointVelocity :
    Continuous (fun z : Space ×
        Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap) ↦
      weightedReconstructedVelocity
        (weightedRestartTimeFromCap_pos hnu hcap).le path z.2.1 z.1)
  jointPressure :
    Continuous (fun z : Space ×
        Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap) ↦
      weightedReconstructedPressure
        (weightedRestartTimeFromCap_pos hnu hcap).le path z.2.1 z.1)
  jointPressureGradient : ∀ coordinate : Fin 3,
    Continuous (fun z : Space ×
        Icc (0 : ℝ) (weightedRestartTimeFromCap nu cap) ↦
      weightedReconstructedPressureGradient
        (weightedRestartTimeFromCap_pos hnu hcap).le
        path z.2.1 coordinate z.1)
  reconstructedModalDivergence : ∀ (k : SpatialFrequency) (t : ℝ),
    ∑ component : Fin 3,
        complexFrequencyVector k component *
          weightedReconstructedVelocityCoefficient
            (weightedRestartTimeFromCap_pos hnu hcap).le
            path component k t = 0
  modalMomentum : ∀ (component : Fin 3) (k : SpatialFrequency)
      {t : ℝ}, t ∈ Ioo (0 : ℝ) (weightedRestartTimeFromCap nu cap) →
    HasDerivAt
      (fun tau : ℝ ↦ weightedReconstructedVelocityCoefficient
        (weightedRestartTimeFromCap_pos hnu hcap).le
        path component k tau)
      (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) *
          weightedReconstructedVelocityCoefficient
            (weightedRestartTimeFromCap_pos hnu hcap).le
            path component k t -
        (weightedSobolevCoefficients 2
          (weightedUnprojectedDivergenceState
            (weightedRestartTimeFromCap_pos hnu hcap).le
            path t component)).1 k -
        weightedReconstructedPressureGradientCoefficient
          (weightedRestartTimeFromCap_pos hnu hcap).le
          path component k t) t

/-- **Cap-selected spacetime momentum return.**  Real, modewise incompressible initial data below
the declared cap return one actual fixed mild path together with its continuous quadratic source
and pressure paths, jointly continuous real velocity/pressure/gradient fields, and exact full
unprojected modal momentum equation. -/
theorem exists_weightedMildSpacetimeMomentumReturn
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) (hinitialNorm : ‖initial‖ ≤ cap)
    (hinitialReal : IsWeightedFourierReal 3 initial)
    (hinitialDivergenceFree : IsModewiseDivergenceFree initial) :
    Nonempty (WeightedMildSpacetimeMomentumReturn hnu hcap initial) := by
  obtain ⟨path, hnorm, hfixed, hinitialFace, hreal, hdivergenceFree⟩ :=
    exists_weightedMildInvariantRestart_fixedPoint hnu hcap initial hinitialNorm
      hinitialReal hinitialDivergenceFree
  let htime : 0 ≤ weightedRestartTimeFromCap nu cap :=
    (weightedRestartTimeFromCap_pos hnu hcap).le
  refine ⟨{
    path := path
    norm_le := hnorm
    fixed := hfixed
    initialFace := hinitialFace
    fourierReal := hreal
    divergenceFree := hdivergenceFree
    spatialVelocityC1 := fun t ↦
      contDiff_one_weightedReconstructedVelocity htime path t
    spatialVelocityPeriodic := fun t ↦
      isOnePeriodic_weightedReconstructedVelocity htime path t
    spatialPressureC1 := fun t ↦
      contDiff_one_weightedReconstructedPressure htime path t
    spatialPressurePeriodic := fun t ↦
      isOnePeriodic_weightedReconstructedPressure htime path t
    jointVelocity := continuous_joint_weightedReconstructedVelocity htime path
    jointPressure := continuous_joint_weightedReconstructedPressure htime path
    jointPressureGradient := fun coordinate ↦
      continuous_joint_weightedReconstructedPressureGradient htime path coordinate
    reconstructedModalDivergence := fun k t ↦
      reconstructedVelocityCoefficient_divergence_eq_zero
        htime hreal hdivergenceFree k t
    modalMomentum := ?_ }⟩
  intro component k t ht
  have hmodal := fixedPoint_weightedMildMap_reconstructedMomentum_hasDerivAt
    (Real.toNNReal nu) (real_toNNReal_pos hnu) htime initial hfixed hreal
    component k ht
  simpa only [Real.coe_toNNReal _ hnu.le] using hmodal

section Audit

#print axioms weightedUnprojectedDivergenceConvolutionContinuous
#print axioms continuous_weightedUnprojectedQuadratic
#print axioms weightedNativePressurePath
#print axioms continuous_joint_weightedReconstructedPressure
#print axioms scalarPressureGradientReconstructionCLM
#print axioms continuous_joint_weightedReconstructedPressureGradient
#print axioms continuous_joint_weightedReconstructedVelocity
#print axioms reconstructedVelocityCoefficient_divergence_eq_zero
#print axioms fixedPoint_weightedMildMap_reconstructedMomentum_hasDerivAt
#print axioms exists_weightedMildSpacetimeMomentumReturn

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum

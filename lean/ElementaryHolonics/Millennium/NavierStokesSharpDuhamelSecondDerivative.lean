import ElementaryHolonics.Millennium.NavierStokesSharpNonlinearSource
import ElementaryHolonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
import ElementaryHolonics.Millennium.NavierStokesWeightedReconstructionContinuity

/-!
# The sharp physical second-derivative Duhamel chart

**[proved-derived]** For a continuous native weighted `H3` path, every interior source time
returns the genuine reconstructed coordinate second derivative of the heat-smoothed exact
Leray--divergence source.  The resulting compact spatial chart is Bochner integrable in time and
is controlled by the sharp `(nu * (t - s))^(-3/4)` kernel.  Compactness of the path aperture then
gives the corresponding supremum-norm corollary.

The chart is identified coefficientwise with the established weighted mild Duhamel return.  The
remaining physical seam is differentiation of the already reconstructed `H3` Bochner return
twice under its time integral; this module records the exact equality needed for that passage
without identifying a general open solution with a mild fixed point.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesSharpDuhamelSecondDerivative

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesH3LerayBilinear
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivativeReconstruction
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelBound
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelMeasurability
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderDuhamelLift
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildCoefficientEquation
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The compact radius-three receiver used by the canonical spatial chart. -/
abbrev SharpSecondDerivativeChart := C(Metric.closedBall (0 : Space) 3, ℝ)

/-- Pull a continuous complex torus field back to the compact Euclidean receiver and retain its
physical real component. -/
def compactRealPartPullbackCLM :
    C(SpatialTorus, ℂ) →L[ℝ] SharpSecondDerivativeChart :=
  LinearMap.mkContinuous
    { toFun := fun field ↦
        ⟨fun x ↦ (field (euclideanToSpatialTorus x.1)).re,
          Complex.continuous_re.comp
            (field.continuous.comp
              (euclideanToSpatialTorus_isOpenQuotientMap.continuous.comp
                continuous_subtype_val))⟩
      map_add' := by
        intro left right
        ext x
        simp
      map_smul' := by
        intro scalar field
        ext x
        simp }
    1 (fun field ↦ by
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg field)).2
      intro x
      exact (Complex.abs_re_le_norm _).trans (field.norm_coe_le_norm _))

/-- Reconstruction after spending the addressed pair of spatial derivatives is a bounded real
linear map from native weighted `H5` to the compact physical chart. -/
def reconstructedSecondDerivativeChartCLM
    (component first second : Fin 3) :
    PeriodicVectorWeightedSobolev 5 →L[ℝ] SharpSecondDerivativeChart :=
  compactRealPartPullbackCLM.comp
    (((reconstructedTorusComplexComponentCLM component).restrictScalars ℝ).comp
      ((finiteOrderVectorDerivativeToThree 2 2 (by omega)
        (secondCoordinateWord first second)).restrictScalars ℝ))

@[simp]
theorem reconstructedSecondDerivativeChartCLM_apply
    (state : PeriodicVectorWeightedSobolev 5)
    (component first second : Fin 3) :
    reconstructedSecondDerivativeChartCLM component first second state =
      ⟨fun x ↦ reconstructedFiniteOrderRealComponent 2 2 (by omega)
          (secondCoordinateWord first second) state component x.1,
        ((contDiff_one_reconstructedFiniteOrderRealComponent 2 2 (by omega)
          (secondCoordinateWord first second) state component).continuous.comp
            continuous_subtype_val)⟩ := by
  ext x
  rfl

/-- Divide a strictly positive elapsed time by three while retaining positivity. -/
def thirdPositiveElapsed (tau : PositiveElapsedTime) : PositiveElapsedTime :=
  ⟨tau.1 / 3, by
    change 0 < (tau.1 : ℝ) / 3
    exact div_pos tau.2 (by norm_num)⟩

theorem continuous_thirdPositiveElapsed : Continuous thirdPositiveElapsed := by
  apply continuous_induced_rng.2
  exact continuous_subtype_val.div_const 3

/-- The three adjacent positive-time scale crossings used by the exact `H2 -> H5` heat
reconstruction, exposed as one jointly continuous map of elapsed time and source. -/
def vectorHeatH2ToH5Joint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2) :
    PeriodicVectorWeightedSobolev 5 :=
  higherOrderHeatLiftJoint 4 nu hnu
    ⟨thirdPositiveElapsed pair.1,
      higherOrderHeatLiftJoint 3 nu hnu
        ⟨thirdPositiveElapsed pair.1,
          higherOrderHeatLiftJoint 2 nu hnu
            ⟨thirdPositiveElapsed pair.1, pair.2⟩⟩⟩

theorem continuous_vectorHeatH2ToH5Joint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) :
    Continuous (vectorHeatH2ToH5Joint nu hnu) := by
  have htime : Continuous
      (fun pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2 ↦
        thirdPositiveElapsed pair.1) :=
    continuous_thirdPositiveElapsed.comp continuous_fst
  have hfirst : Continuous
      (fun pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2 ↦
        higherOrderHeatLiftJoint 2 nu hnu
          ⟨thirdPositiveElapsed pair.1, pair.2⟩) :=
    (continuous_higherOrderHeatLiftJoint 2 nu hnu).comp
      (htime.prodMk continuous_snd)
  have hsecond : Continuous
      (fun pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2 ↦
        higherOrderHeatLiftJoint 3 nu hnu
          ⟨thirdPositiveElapsed pair.1,
            higherOrderHeatLiftJoint 2 nu hnu
              ⟨thirdPositiveElapsed pair.1, pair.2⟩⟩) :=
    (continuous_higherOrderHeatLiftJoint 3 nu hnu).comp
      (htime.prodMk hfirst)
  exact (continuous_higherOrderHeatLiftJoint 4 nu hnu).comp
    (htime.prodMk hsecond)

theorem vectorHeatH2ToH5Joint_apply
    (nu dt : ℝ≥0) (hnu : 0 < (nu : ℝ)) (hdt : 0 < (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2) :
    vectorHeatH2ToH5Joint nu hnu ⟨⟨dt, hdt⟩, source⟩ =
      vectorHeatH2ToH5 nu dt (mul_pos hnu hdt) source := by
  funext component
  rfl

/-- Jointly continuous compact physical second-derivative reconstruction of one heat-smoothed
`H2` source. -/
def sharpHeatSecondDerivativeChartJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (component first second : Fin 3)
    (pair : PositiveElapsedTime × PeriodicVectorWeightedSobolev 2) :
    SharpSecondDerivativeChart :=
  reconstructedSecondDerivativeChartCLM component first second
    (vectorHeatH2ToH5Joint nu hnu pair)

theorem continuous_sharpHeatSecondDerivativeChartJoint
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (component first second : Fin 3) :
    Continuous (sharpHeatSecondDerivativeChartJoint nu hnu component first second) :=
  (reconstructedSecondDerivativeChartCLM component first second).continuous.comp
    (continuous_vectorHeatH2ToH5Joint nu hnu)

/-- Endpoint-totalized physical `D2` chart of the exact nonlinear Duhamel integrand. -/
def sharpDuhamelSecondDerivativeIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (s : ℝ) :
    SharpSecondDerivativeChart :=
  if hs : s < t then
    sharpHeatSecondDerivativeChartJoint nu hnu component first second
      ⟨⟨positiveElapsed t s hs, by
          simpa only [coe_positiveElapsed] using sub_pos.mpr hs⟩,
        sharpNonlinearSource (path s)⟩
  else
    0

theorem sharpDuhamelSecondDerivativeIntegrand_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) {s : ℝ} (hs : s < t) :
    sharpDuhamelSecondDerivativeIntegrand nu hnu t path component first second s =
      reconstructedHeatH2SecondDerivativeChart nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s))
        component first second := by
  rw [sharpDuhamelSecondDerivativeIntegrand, dif_pos hs,
    sharpHeatSecondDerivativeChartJoint]
  have hdt : 0 < ((positiveElapsed t s hs : ℝ≥0) : ℝ) := by
    simpa only [coe_positiveElapsed] using sub_pos.mpr hs
  rw [vectorHeatH2ToH5Joint_apply nu (positiveElapsed t s hs) hnu hdt]
  ext x
  rfl

@[simp]
theorem sharpDuhamelSecondDerivativeIntegrand_of_not_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) {s : ℝ} (hs : ¬ s < t) :
    sharpDuhamelSecondDerivativeIntegrand nu hnu t path component first second s = 0 := by
  simp [sharpDuhamelSecondDerivativeIntegrand, hs]

/-- The fixed sharp constant after absorbing the harmless factor `2^(-3/4)`. -/
def sharpDuhamelSecondDerivativeConstant : ℝ :=
  sharpHeatSecondDerivativeH2Constant * (2 : ℝ) ^ (-3 / 4 : ℝ) *
    (23328 * periodicH3EmbeddingConstant)

theorem sharpDuhamelSecondDerivativeConstant_nonneg :
    0 ≤ sharpDuhamelSecondDerivativeConstant := by
  unfold sharpDuhamelSecondDerivativeConstant
  exact mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (by norm_num) _))
    (mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg)

/-- Pointwise sharp physical chart estimate with the exact time-varying quadratic source. -/
theorem norm_sharpDuhamelSecondDerivativeIntegrand_le
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t s : ℝ) (hs : s < t)
    (hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) :
    ‖sharpDuhamelSecondDerivativeIntegrand nu hnu t path
        component first second s‖ ≤
      sharpDuhamelSecondDerivativeConstant *
        ((nu : ℝ) * (t - s)) ^ (-3 / 4 : ℝ) * ‖path s‖ ^ 2 := by
  rw [sharpDuhamelSecondDerivativeIntegrand_of_lt nu hnu t path
    component first second hs]
  have hbound := norm_reconstructedSharpNonlinearSourceSecondDerivativeChart_le
    nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
      (by simpa only [coe_positiveElapsed] using hlocal)
      (path s) component first second
  have htime : 0 ≤ (nu : ℝ) * (t - s) :=
    mul_nonneg hnu.le (sub_pos.mpr hs).le
  calc
    _ ≤ sharpHeatSecondDerivativeH2Constant *
        (2 * ((nu : ℝ) * (t - s))) ^ (-3 / 4 : ℝ) *
          ((23328 * periodicH3EmbeddingConstant) * ‖path s‖ ^ 2) := by
      simpa only [coe_positiveElapsed] using hbound
    _ = sharpDuhamelSecondDerivativeConstant *
        ((nu : ℝ) * (t - s)) ^ (-3 / 4 : ℝ) * ‖path s‖ ^ 2 := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) htime]
      unfold sharpDuhamelSecondDerivativeConstant
      ring

/-- The actual physical scalar heat slice whose addressed second derivative supplies the
integrand chart. -/
def reconstructedHeatH2Component
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2) (component : Fin 3) : Space → ℝ :=
  reconstructedFiniteOrderRealComponent 2 0 (by omega) (fun i ↦ Fin.elim0 i)
    (vectorHeatH2ToH5 nu dt h source) component

/-- The reconstructed `H2` heat chart is literally the iterated spatial derivative of its
physical scalar heat slice. -/
theorem iterated_fderiv_reconstructedHeatH2Component
    (nu dt : ℝ≥0) (h : 0 < (nu : ℝ) * (dt : ℝ))
    (source : PeriodicVectorWeightedSobolev 2)
    (component first second : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space ↦
      fderiv ℝ (reconstructedHeatH2Component nu dt h source component) y
        (EuclideanSpace.single first 1)) x
        (EuclideanSpace.single second 1) =
      reconstructedHeatH2SecondDerivative nu dt h source
        component first second x := by
  rw [show (fun y : Space ↦
      fderiv ℝ (reconstructedHeatH2Component nu dt h source component) y
        (EuclideanSpace.single first 1)) =
      reconstructedFiniteOrderRealComponent 2 1 (by omega) (![first])
        (vectorHeatH2ToH5 nu dt h source) component by
    funext y
    exact fderiv_reconstructedFiniteOrderRealComponent_apply_single
      2 0 (by omega) (fun i ↦ Fin.elim0 i)
        (vectorHeatH2ToH5 nu dt h source) component first y]
  rw [fderiv_reconstructedFiniteOrderRealComponent_apply_single]
  rfl

/-- At every interior source time, evaluating the compact Duhamel integrand is exactly evaluating
the genuine iterated second derivative of the corresponding heat-smoothed nonlinear slice. -/
theorem sharpDuhamelSecondDerivativeIntegrand_apply_eq_iterated_fderiv_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) {s : ℝ} (hs : s < t)
    (x : Metric.closedBall (0 : Space) 3) :
    sharpDuhamelSecondDerivativeIntegrand nu hnu t path
        component first second s x =
      fderiv ℝ (fun y : Space ↦
        fderiv ℝ
          (reconstructedHeatH2Component nu (positiveElapsed t s hs)
            (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s)) component) y
          (EuclideanSpace.single first 1)) x.1
          (EuclideanSpace.single second 1) := by
  rw [sharpDuhamelSecondDerivativeIntegrand_of_lt
    nu hnu t path component first second hs]
  exact (iterated_fderiv_reconstructedHeatH2Component
    nu (positiveElapsed t s hs) (mul_pos hnu (sub_pos.mpr hs))
      (sharpNonlinearSource (path s)) component first second x.1).symm

/-! ## Interior continuity and the honest chart-valued time integral -/

/-- For a continuous native path, the compact physical `D2` integrand is continuous at every
strictly interior source time. -/
theorem continuousOn_sharpDuhamelSecondDerivativeIntegrand_Ioo
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component first second : Fin 3) :
    ContinuousOn
      (sharpDuhamelSecondDerivativeIntegrand nu hnu t path component first second)
      (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_restrict]
  have helapsed : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t)) :=
    (continuous_positiveElapsedBefore t).comp
      (continuous_subtype_val.subtype_mk _)
  have hsource : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ sharpNonlinearSource (path s.1)) := by
    change Continuous (fun s : Ioo (0 : ℝ) t ↦ weightedLerayQuadratic (path s.1))
    exact continuous_weightedLerayQuadratic.comp
      (hpath.comp continuous_subtype_val)
  have hmodel : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        sharpHeatSecondDerivativeChartJoint nu hnu component first second
          ⟨positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t),
            sharpNonlinearSource (path s.1)⟩) :=
    (continuous_sharpHeatSecondDerivativeChartJoint
      nu hnu component first second).comp (helapsed.prodMk hsource)
  apply hmodel.congr
  intro s
  have hdt : 0 < ((positiveElapsed t s.1 s.2.2 : ℝ≥0) : ℝ) := by
    simpa only [coe_positiveElapsed] using sub_pos.mpr s.2.2
  have helapsedEq : positiveElapsedBefore t (⟨s.1, s.2.2⟩ : Iio t) =
      (⟨positiveElapsed t s.1 s.2.2, hdt⟩ : PositiveElapsedTime) := by
    apply Subtype.ext
    change Real.toNNReal (t - s.1) = positiveElapsed t s.1 s.2.2
    apply NNReal.eq
    rw [Real.coe_toNNReal (t - s.1) (sub_nonneg.mpr s.2.2.le),
      coe_positiveElapsed]
  change _ = sharpDuhamelSecondDerivativeIntegrand
    nu hnu t path component first second s.1
  rw [helapsedEq,
    sharpDuhamelSecondDerivativeIntegrand_of_lt
      nu hnu t path component first second s.2.2,
    sharpHeatSecondDerivativeChartJoint,
    vectorHeatH2ToH5Joint_apply nu (positiveElapsed t s.1 s.2.2) hnu hdt]
  ext x
  rfl

/-- Interior continuity supplies the exact strong-measurability port for the compact chart-valued
Bochner integral. -/
theorem aestronglyMeasurable_sharpDuhamelSecondDerivativeIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path)
    (component first second : Fin 3) :
    AEStronglyMeasurable
      (sharpDuhamelSecondDerivativeIntegrand nu hnu t path component first second)
      (volume.restrict (Ioc (0 : ℝ) t)) := by
  letI : SecondCountableTopologyEither ℝ SharpSecondDerivativeChart :=
    ⟨Or.inl (by infer_instance)⟩
  rw [← restrict_Ioo_eq_restrict_Ioc]
  exact (continuousOn_sharpDuhamelSecondDerivativeIntegrand_Ioo
    nu hnu path hpath component first second).aestronglyMeasurable measurableSet_Ioo

/-- The exact scalar majorant requested by the sharp `D2` Duhamel edge. -/
def sharpDuhamelSecondDerivativeMajorant
    (nu : ℝ≥0) (t : ℝ) (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (s : ℝ) : ℝ :=
  sharpDuhamelSecondDerivativeConstant *
    ((nu : ℝ) * (t - s)) ^ (-3 / 4 : ℝ) * ‖path s‖ ^ 2

private theorem continuousOn_sharpDuhamelSecondDerivativeMajorant_Ioo
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {t : ℝ}
    (path : ℝ → PeriodicVectorWeightedSobolev 3) (hpath : Continuous path) :
    ContinuousOn (sharpDuhamelSecondDerivativeMajorant nu t path) (Ioo (0 : ℝ) t) := by
  rw [continuousOn_iff_continuous_restrict]
  have hbase : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ (nu : ℝ) * (t - s.1)) := by
    fun_prop
  have hpower : Continuous
      (fun s : Ioo (0 : ℝ) t ↦
        ((nu : ℝ) * (t - s.1)) ^ (-3 / 4 : ℝ)) :=
    hbase.rpow_const (fun s ↦ Or.inl (by
      exact (mul_pos hnu (sub_pos.mpr s.2.2)).ne'))
  have hnorm : Continuous
      (fun s : Ioo (0 : ℝ) t ↦ ‖path s.1‖ ^ 2) :=
    ((hpath.comp continuous_subtype_val).norm).pow 2
  exact continuous_const.mul hpower |>.mul hnorm

/-- Compactness of the path aperture closes interval integrability of the exact time-varying
`(nu * (t-s))^(-3/4) * ‖path s‖^2` majorant. -/
theorem intervalIntegrable_sharpDuhamelSecondDerivativeMajorant
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t) :
    IntervalIntegrable
      (sharpDuhamelSecondDerivativeMajorant nu t (weightedPathExtension hT path))
      volume 0 t := by
  let p : ℝ := -3 / 4
  have hrpow : IntervalIntegrable (fun tau : ℝ ↦ tau ^ p) volume 0 t := by
    exact intervalIntegral.intervalIntegrable_rpow' (by dsimp [p]; norm_num)
  have hreflected : IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ p) volume 0 t := by
    simpa using (hrpow.comp_sub_left t).symm
  let C : ℝ := sharpDuhamelSecondDerivativeConstant *
    (nu : ℝ) ^ p * ‖path‖ ^ 2
  have huniform : IntervalIntegrable (fun s : ℝ ↦ C * (t - s) ^ p) volume 0 t :=
    hreflected.const_mul C
  have hmeas : AEStronglyMeasurable
      (sharpDuhamelSecondDerivativeMajorant nu t (weightedPathExtension hT path))
      (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [uIoc_of_le htpos.le, ← restrict_Ioo_eq_restrict_Ioc]
    exact (continuousOn_sharpDuhamelSecondDerivativeMajorant_Ioo
      nu hnu (weightedPathExtension hT path)
        (weightedPathExtension hT path).continuous).aestronglyMeasurable measurableSet_Ioo
  apply huniform.mono_fun' hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le htpos.le] at hs
  have hst : 0 ≤ t - s := sub_nonneg.mpr hs.2
  have hkernel : 0 ≤ (t - s) ^ p := Real.rpow_nonneg hst p
  have hnuPower : 0 ≤ (nu : ℝ) ^ p := Real.rpow_nonneg hnu.le p
  have hpathBound := norm_weightedPathExtension_le hT path s
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold sharpDuhamelSecondDerivativeMajorant
    exact mul_nonneg
      (mul_nonneg sharpDuhamelSecondDerivativeConstant_nonneg
        (Real.rpow_nonneg (mul_nonneg hnu.le hst) _))
      (sq_nonneg _))]
  unfold sharpDuhamelSecondDerivativeMajorant
  rw [show ((nu : ℝ) * (t - s)) ^ p =
      (nu : ℝ) ^ p * (t - s) ^ p by
    exact Real.mul_rpow hnu.le hst]
  change sharpDuhamelSecondDerivativeConstant *
      ((nu : ℝ) ^ p * (t - s) ^ p) *
        ‖weightedPathExtension hT path s‖ ^ 2 ≤
    C * (t - s) ^ p
  dsimp [C]
  have hsq : ‖weightedPathExtension hT path s‖ ^ 2 ≤ ‖path‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hpathBound
  calc
    sharpDuhamelSecondDerivativeConstant *
        ((nu : ℝ) ^ p * (t - s) ^ p) *
          ‖weightedPathExtension hT path s‖ ^ 2 =
        (sharpDuhamelSecondDerivativeConstant * (nu : ℝ) ^ p *
          (t - s) ^ p) * ‖weightedPathExtension hT path s‖ ^ 2 := by ring
    _ ≤ (sharpDuhamelSecondDerivativeConstant * (nu : ℝ) ^ p *
          (t - s) ^ p) * ‖path‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq
        (mul_nonneg
          (mul_nonneg sharpDuhamelSecondDerivativeConstant_nonneg hnuPower)
          hkernel)
    _ = sharpDuhamelSecondDerivativeConstant * (nu : ℝ) ^ p *
          ‖path‖ ^ 2 * (t - s) ^ p := by ring

/-- The physical compact `D2` Duhamel chart, defined as the honest Bochner integral of the exact
reconstructed nonlinear source charts. -/
def sharpDuhamelSecondDerivativeChart
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : ℝ)
    (component first second : Fin 3) : SharpSecondDerivativeChart :=
  ∫ s in (0 : ℝ)..t,
    sharpDuhamelSecondDerivativeIntegrand nu hnu t
      (weightedPathExtension hT path) component first second s

/-- A continuous weighted `H3` path produces an honestly interval-integrable compact physical
second-derivative chart. -/
theorem intervalIntegrable_sharpDuhamelSecondDerivativeIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3) :
    IntervalIntegrable
      (sharpDuhamelSecondDerivativeIntegrand nu hnu t
        (weightedPathExtension hT path) component first second) volume 0 t := by
  have hmajorant := intervalIntegrable_sharpDuhamelSecondDerivativeMajorant
    nu hnu hT path ht htpos
  have hmeas : AEStronglyMeasurable
      (sharpDuhamelSecondDerivativeIntegrand nu hnu t
        (weightedPathExtension hT path) component first second)
      (volume.restrict (Ι (0 : ℝ) t)) := by
    rw [uIoc_of_le htpos.le]
    exact aestronglyMeasurable_sharpDuhamelSecondDerivativeIntegrand
      nu hnu (weightedPathExtension hT path)
        (weightedPathExtension hT path).continuous component first second
  apply hmajorant.mono_fun' hmeas
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  rw [uIoc_of_le htpos.le] at hs
  by_cases hst : s < t
  · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
      have hsub : t - s ≤ t := by linarith [hs.1]
      have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
        mul_le_mul_of_nonneg_left hsub hnu.le
      calc
        2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 2 * (nu : ℝ) * t := by ring
        _ ≤ 1 := hsmall
    exact norm_sharpDuhamelSecondDerivativeIntegrand_le
      nu hnu t s hst hlocal (weightedPathExtension hT path)
        component first second
  · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
    subst s
    simp [sharpDuhamelSecondDerivativeMajorant,
      sharpDuhamelSecondDerivativeIntegrand_of_not_lt]

/-- Exact sharp physical chart bound with the requested time-varying quadratic integrand. -/
theorem norm_sharpDuhamelSecondDerivativeChart_le_integral
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3) :
    ‖sharpDuhamelSecondDerivativeChart nu hnu hT path t
        component first second‖ ≤
      ∫ s in (0 : ℝ)..t,
        sharpDuhamelSecondDerivativeConstant *
          ((nu : ℝ) * (t - s)) ^ (-3 / 4 : ℝ) *
            ‖weightedPathExtension hT path s‖ ^ 2 := by
  unfold sharpDuhamelSecondDerivativeChart
  apply intervalIntegral.norm_integral_le_of_norm_le htpos.le
  · filter_upwards with s
    intro hs
    by_cases hst : s < t
    · have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
        have hsub : t - s ≤ t := by linarith [hs.1]
        have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
          mul_le_mul_of_nonneg_left hsub hnu.le
        calc
          2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
            mul_le_mul_of_nonneg_left hmul (by norm_num)
          _ = 2 * (nu : ℝ) * t := by ring
          _ ≤ 1 := hsmall
      exact norm_sharpDuhamelSecondDerivativeIntegrand_le
        nu hnu t s hst hlocal (weightedPathExtension hT path)
          component first second
    · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp [sharpDuhamelSecondDerivativeIntegrand_of_not_lt]
  · exact intervalIntegrable_sharpDuhamelSecondDerivativeMajorant
      nu hnu hT path ht htpos

private theorem intervalIntegral_rpow_neg_three_quarters
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ tau in (0 : ℝ)..t, tau ^ (-3 / 4 : ℝ)) =
      4 * t ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (a := 0) (b := t)
    (r := (-3 / 4 : ℝ)) (Or.inl (by norm_num))]
  rw [show (-3 / 4 : ℝ) + 1 = 1 / 4 by ring,
    Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), sub_zero]
  ring

/-- Compact-path supremum corollary with the singular time kernel integrated exactly. -/
theorem norm_sharpDuhamelSecondDerivativeChart_le_path_norm
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T t : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (ht : t ∈ Icc (0 : ℝ) T) (htpos : 0 < t)
    (hsmall : 2 * (nu : ℝ) * t ≤ 1)
    (component first second : Fin 3) :
    ‖sharpDuhamelSecondDerivativeChart nu hnu hT path t
        component first second‖ ≤
      4 * sharpDuhamelSecondDerivativeConstant *
        (nu : ℝ) ^ (-3 / 4 : ℝ) * t ^ (1 / 4 : ℝ) * ‖path‖ ^ 2 := by
  let p : ℝ := -3 / 4
  let C : ℝ := sharpDuhamelSecondDerivativeConstant *
    (nu : ℝ) ^ p * ‖path‖ ^ 2
  have hrpow : IntervalIntegrable (fun tau : ℝ ↦ tau ^ p) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by dsimp [p]; norm_num)
  have hreflected : IntervalIntegrable (fun s : ℝ ↦ (t - s) ^ p) volume 0 t := by
    simpa using (hrpow.comp_sub_left t).symm
  have huniform : IntervalIntegrable (fun s : ℝ ↦ C * (t - s) ^ p) volume 0 t :=
    hreflected.const_mul C
  have hnorm : ‖sharpDuhamelSecondDerivativeChart nu hnu hT path t
        component first second‖ ≤
      ∫ s in (0 : ℝ)..t, C * (t - s) ^ p := by
    unfold sharpDuhamelSecondDerivativeChart
    apply intervalIntegral.norm_integral_le_of_norm_le htpos.le
    · filter_upwards with s
      intro hs
      by_cases hst : s < t
      · have hsub : t - s ≤ t := by linarith [hs.1]
        have hmul : (nu : ℝ) * (t - s) ≤ (nu : ℝ) * t :=
          mul_le_mul_of_nonneg_left hsub hnu.le
        have hlocal : 2 * ((nu : ℝ) * (t - s)) ≤ 1 := by
          calc
            2 * ((nu : ℝ) * (t - s)) ≤ 2 * ((nu : ℝ) * t) :=
              mul_le_mul_of_nonneg_left hmul (by norm_num)
            _ = 2 * (nu : ℝ) * t := by ring
            _ ≤ 1 := hsmall
        have hpoint := norm_sharpDuhamelSecondDerivativeIntegrand_le
          nu hnu t s hst hlocal (weightedPathExtension hT path)
            component first second
        have hst0 : 0 ≤ t - s := (sub_pos.mpr hst).le
        have hkernel : 0 ≤ (t - s) ^ p := Real.rpow_nonneg hst0 p
        have hnuPower : 0 ≤ (nu : ℝ) ^ p := Real.rpow_nonneg hnu.le p
        have hpathBound := norm_weightedPathExtension_le hT path s
        have hsq : ‖weightedPathExtension hT path s‖ ^ 2 ≤ ‖path‖ ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hpathBound
        calc
          _ ≤ sharpDuhamelSecondDerivativeConstant *
              ((nu : ℝ) * (t - s)) ^ p *
                ‖weightedPathExtension hT path s‖ ^ 2 := by
            simpa only [p] using hpoint
          _ = (sharpDuhamelSecondDerivativeConstant * (nu : ℝ) ^ p *
                (t - s) ^ p) *
                ‖weightedPathExtension hT path s‖ ^ 2 := by
            rw [Real.mul_rpow hnu.le hst0]
            ring
          _ ≤ (sharpDuhamelSecondDerivativeConstant * (nu : ℝ) ^ p *
                (t - s) ^ p) * ‖path‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hsq
              (mul_nonneg
                (mul_nonneg sharpDuhamelSecondDerivativeConstant_nonneg hnuPower)
                hkernel)
          _ = C * (t - s) ^ p := by
            dsimp [C]
            ring
      · have hseq : s = t := le_antisymm hs.2 (le_of_not_gt hst)
        subst s
        rw [sharpDuhamelSecondDerivativeIntegrand_of_not_lt
          nu hnu t (weightedPathExtension hT path) component first second (lt_irrefl t),
          norm_zero]
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg sharpDuhamelSecondDerivativeConstant_nonneg
              (Real.rpow_nonneg hnu.le p)) (sq_nonneg _))
          (Real.rpow_nonneg (by norm_num) p)
    · exact huniform
  calc
    _ ≤ ∫ s in (0 : ℝ)..t, C * (t - s) ^ p := hnorm
    _ = C * ∫ s in (0 : ℝ)..t, (t - s) ^ p := by
      rw [intervalIntegral.integral_const_mul]
    _ = C * ∫ tau in (0 : ℝ)..t, tau ^ p := by
      congr 1
      simpa using
        (intervalIntegral.integral_comp_sub_left
          (fun tau : ℝ ↦ tau ^ p) t (a := 0) (b := t))
    _ = C * (4 * t ^ (1 / 4 : ℝ)) := by
      rw [show p = (-3 / 4 : ℝ) by rfl,
        intervalIntegral_rpow_neg_three_quarters htpos.le]
    _ = 4 * sharpDuhamelSecondDerivativeConstant *
        (nu : ℝ) ^ (-3 / 4 : ℝ) * t ^ (1 / 4 : ℝ) * ‖path‖ ^ 2 := by
      dsimp [C, p]
      ring

/-! ## Exact comparison with the standing mild Duhamel coefficient return -/

/-- Full complex torus population underlying the real compact chart at one source time. -/
def sharpDuhamelSecondDerivativeTorusIntegrand
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (s : ℝ) : C(SpatialTorus, ℂ) :=
  if hs : s < t then
    reconstructedFiniteOrderTorusComplexComponent 2 2 (by omega)
      (secondCoordinateWord first second)
      (vectorHeatH2ToH5 nu (positiveElapsed t s hs)
        (mul_pos hnu (sub_pos.mpr hs)) (sharpNonlinearSource (path s))) component
  else
    0

/-- The compact real chart is exactly the pullback/real receiver of the full complex torus
population, rather than an unrelated norm surrogate. -/
theorem sharpDuhamelSecondDerivativeIntegrand_eq_compactRealPart
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (s : ℝ) :
    sharpDuhamelSecondDerivativeIntegrand nu hnu t path component first second s =
      compactRealPartPullbackCLM
        (sharpDuhamelSecondDerivativeTorusIntegrand nu hnu t path
          component first second s) := by
  by_cases hs : s < t
  · rw [sharpDuhamelSecondDerivativeIntegrand_of_lt
      nu hnu t path component first second hs,
      sharpDuhamelSecondDerivativeTorusIntegrand, dif_pos hs]
    ext x
    rfl
  · rw [sharpDuhamelSecondDerivativeIntegrand_of_not_lt
      nu hnu t path component first second hs,
      sharpDuhamelSecondDerivativeTorusIntegrand, dif_neg hs]
    exact (compactRealPartPullbackCLM.map_zero).symm

/-- Unweighting the exact sharp nonlinear source returns the same Leray--divergence coefficient
population used by the standing mild equation. -/
theorem weightedPhysicalCoefficient_sharpNonlinearSource
    (u : PeriodicVectorWeightedSobolev 3) (component : Fin 3)
    (k : SpatialFrequency) :
    weightedPhysicalCoefficient 2 component k (sharpNonlinearSource u) =
      (lerayProjectedH3DivergenceConvolution
        (unweightedVectorThree u) (unweightedVectorThree u) component).1 k := by
  rw [weightedPhysicalCoefficient_apply]
  exact unweighted_weightedLerayDivergenceConvolution_apply u u component k

/-- Every interior torus chart mode is exactly the ordered second-derivative multiplier times the
heat multiplier times the standing nonlinear source coefficient. -/
theorem torusSpatialFourierCoeff_sharpDuhamelSecondDerivativeTorusIntegrand_of_lt
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (t : ℝ)
    (path : ℝ → PeriodicVectorWeightedSobolev 3)
    (component first second : Fin 3) (k : SpatialFrequency)
    {s : ℝ} (hs : s < t) :
    torusSpatialFourierCoeff
        (sharpDuhamelSecondDerivativeTorusIntegrand nu hnu t path
          component first second s) k =
      orderedDerivativeMultiplier 2 (secondCoordinateWord first second) k *
        (heatStokesMultiplier (nu : ℝ) (t - s) k : ℂ) *
          (lerayProjectedH3DivergenceConvolution
            (unweightedVectorThree (path s))
            (unweightedVectorThree (path s)) component).1 k := by
  rw [sharpDuhamelSecondDerivativeTorusIntegrand, dif_pos hs,
    torusSpatialFourierCoeff_reconstructedFiniteOrderTorusComplexComponent,
    weightedCoefficients_vectorHeatH2ToH5, coe_positiveElapsed,
    ← weightedPhysicalCoefficient_apply,
    weightedPhysicalCoefficient_sharpNonlinearSource]
  ring

/-- Exact comparison: applying the ordered `D2` Fourier symbol to the repository's actual
weighted `H3` Duhamel return gives the interval integral of precisely the torus coefficient
population underlying the sharp compact chart. -/
theorem weightedDuhamelReturn_secondDerivativeMode_eq_sharpPopulation
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (component first second : Fin 3)
    (k : SpatialFrequency) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    orderedDerivativeMultiplier 2 (secondCoordinateWord first second) k *
        weightedPhysicalCoefficient 3 component k
          (weightedDuhamelReturn nu hnu hT path t) =
      ∫ s in (0 : ℝ)..t,
        torusSpatialFourierCoeff
          (sharpDuhamelSecondDerivativeTorusIntegrand nu hnu t
            (weightedPathExtension hT path) component first second s) k := by
  rw [weightedPhysicalCoefficient_weightedDuhamelReturn
    nu hnu hT path component k ht]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  rw [torusSpatialFourierCoeff_sharpDuhamelSecondDerivativeTorusIntegrand_of_lt
    nu hnu t (weightedPathExtension hT path) component first second k hs.2]
  ring

/-- The sole remaining physical identification is differentiation twice under the already
established reconstructed `H3` Duhamel return.  All Fourier modes of this equality are proved by
`weightedDuhamelReturn_secondDerivativeMode_eq_sharpPopulation`; no open-solution identity is
assumed here. -/
def HasSharpDuhamelSecondDerivativeIdentification
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) (t : ℝ)
    (component first second : Fin 3) : Prop :=
  ∀ x : Metric.closedBall (0 : Space) 3,
    fderiv ℝ (fun y : Space ↦
      fderiv ℝ (fun z : Space ↦
        reconstructedVelocity (weightedDuhamelReturn nu hnu hT path t) z component) y
          (EuclideanSpace.single first 1)) x.1
          (EuclideanSpace.single second 1) =
      sharpDuhamelSecondDerivativeChart nu hnu hT path t
        component first second x

/-! ## Axiom audit -/

#print axioms norm_sharpDuhamelSecondDerivativeIntegrand_le
#print axioms intervalIntegrable_sharpDuhamelSecondDerivativeIntegrand
#print axioms norm_sharpDuhamelSecondDerivativeChart_le_integral
#print axioms norm_sharpDuhamelSecondDerivativeChart_le_path_norm
#print axioms weightedDuhamelReturn_secondDerivativeMode_eq_sharpPopulation

end Soma.Holonics.Millennium.NavierStokesSharpDuhamelSecondDerivative

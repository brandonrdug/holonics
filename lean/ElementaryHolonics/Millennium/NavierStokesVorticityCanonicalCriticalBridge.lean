import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalTime
import ElementaryHolonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# From the canonical vorticity derivative to the critical receiver

**[proved-derived]** The critical torus sup-vorticity receiver factors through the canonical
compact-chart derivative norm.  The first passage retains an anchor, making explicit the fixed
mode invisible to differences.  The source-specific curl law then proves that the zero Fourier
mode of periodic vorticity vanishes.  Haar reconstruction and centered torus transport therefore
remove the anchor and prove

`criticalVorticityRate ≤ (3/2) · canonicalVorticityDerivativeRate`.

Terminal integrability of this derivative population supplies the exact critical-vorticity
integral consumed by the completed continuation passage.  The remaining open edge is precisely
that terminal derivative-rate integral; strict-interior smoothness alone does not furnish it.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval NNReal

namespace Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

/- `mFourierCoeff` uses probability Haar measure on the genuine spatial torus. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## The curl law removes the fixed mode -/

/-- The source-specific curl multiplier kills the zero Fourier mode of every admitted periodic
vorticity slice. -/
theorem openPeriodicVorticityFourierMode_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    openPeriodicVorticityFourierMode solution t 0 = 0 := by
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier]
  exact frequencyCurlMultiplier_zero _

/-- The zero mode is exactly the Haar mean of the descended complex vorticity field. -/
theorem integral_complexTorusVorticitySlice_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    (∫ q : SpatialTorus, complexTorusVorticitySlice solution t q) = 0 := by
  have hzero := openPeriodicVorticityFourierMode_zero solution t
  rw [openPeriodicVorticityFourierMode_eq_mFourierCoeff] at hzero
  simpa [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero] using hzero

/-- The real Euclidean receiver is bounded by the complex coordinate-sup receiver with the exact
finite-dimensional comparison constant. -/
theorem norm_space_le_sqrt_three_mul_norm_complexifySpace (v : Space) :
    ‖v‖ ≤ Real.sqrt 3 * ‖complexifySpace v‖ := by
  calc
    ‖v‖ ≤ Real.sqrt (Fintype.card (Fin 3)) *
        ⨆ coordinate : Fin 3, ‖v coordinate‖ := by
      simpa only [Fintype.card_fin, EuclideanSpace.basisFun_inner] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).norm_le_card_mul_iSup_norm_inner v
    _ = Real.sqrt 3 * ⨆ coordinate : Fin 3, ‖v coordinate‖ := by
      norm_num [EuclideanSpace.basisFun_inner]
    _ ≤ Real.sqrt 3 * ‖complexifySpace v‖ := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 3)
      apply ciSup_le
      intro coordinate
      simpa [complexifySpace] using
        (norm_le_pi_norm (complexifySpace v) coordinate)

/-- Since complexification is coordinatewise faithful, the zero complex Fourier mode returns the
exact zero Haar mean in the original Euclidean vorticity carrier. -/
theorem integral_torusVorticityEvolution_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    (∫ q : SpatialTorus, torusVorticityEvolution solution t q) = 0 := by
  have hrealIntegrable : Integrable (torusVorticityEvolution solution t) :=
    continuousMap_integrable_on_compact (torusVorticityEvolution solution t)
  have hcomplexIntegrable : Integrable (complexTorusVorticitySlice solution t) :=
    continuousMap_integrable_on_compact (complexTorusVorticitySlice solution t)
  have hcomplex := integral_complexTorusVorticitySlice_eq_zero solution t
  apply PiLp.ext
  intro coordinate
  rw [MeasureTheory.eval_integral_piLp hrealIntegrable.eval_piLp coordinate]
  have hcoordinate := congrFun hcomplex coordinate
  rw [MeasureTheory.eval_integral hcomplexIntegrable.eval coordinate] at hcoordinate
  change (∫ q : SpatialTorus,
      (((torusVorticityEvolution solution t q) coordinate : ℝ) : ℂ)) = 0 at hcoordinate
  rw [integral_complex_ofReal] at hcoordinate
  simpa using Complex.ofReal_injective hcoordinate

/-- Every pair of torus occurrences admits an addressed centered displacement of norm at most
`3/2`, while both the source and its translated endpoint remain in the canonical radius-three
chart.  The canonical derivative norm therefore bounds every returned vorticity difference. -/
theorem norm_torusVorticityEvolution_sub_le_three_halves_mul_canonical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) (q y : SpatialTorus) :
    ‖torusVorticityEvolution solution t q -
        torusVorticityEvolution solution t y‖ ≤
      (3 / 2 : ℝ) *
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
  let source : Space := centeredEuclideanRepresentative q
  let displacement : Space := centeredEuclideanRepresentative (y - q)
  let target : Space := source + displacement
  have hsourceProjection : euclideanToSpatialTorus source = q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative q
  have hdisplacementProjection :
      euclideanToSpatialTorus displacement = y - q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative (y - q)
  have hprojectionAdd (left right : Space) :
      euclideanToSpatialTorus (left + right) =
        euclideanToSpatialTorus left + euclideanToSpatialTorus right := by
    ext coordinate
    rfl
  have htargetProjection : euclideanToSpatialTorus target = y := by
    rw [show target = source + displacement from rfl, hprojectionAdd,
      hsourceProjection, hdisplacementProjection]
    abel
  have hsourceNorm : ‖source‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves q
  have hdisplacementNorm : ‖displacement‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves (y - q)
  have htargetNorm : ‖target‖ ≤ 3 := by
    calc
      ‖target‖ = ‖source + displacement‖ := rfl
      _ ≤ ‖source‖ + ‖displacement‖ := norm_add_le _ _
      _ ≤ (3 : ℝ) / 2 + 3 / 2 := add_le_add hsourceNorm hdisplacementNorm
      _ = 3 := by norm_num
  have hsourceMem : source ∈ Metric.closedBall (0 : Space) 3 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hsourceNorm.trans (by norm_num)
  have htargetMem : target ∈ Metric.closedBall (0 : Space) 3 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using htargetNorm
  have hlipschitz :=
    (openPeriodicCanonicalVorticityLipschitzOn_closedBall solution t).dist_le_mul
      source hsourceMem target htargetMem
  have hdistance : dist source target ≤ (3 : ℝ) / 2 := by
    calc
      dist source target = ‖displacement‖ := by
        simp [target, dist_eq_norm]
      _ ≤ (3 : ℝ) / 2 := hdisplacementNorm
  rw [← hsourceProjection, ← htargetProjection,
    torusVorticityEvolution_projection, torusVorticityEvolution_projection]
  calc
    ‖vorticityField velocity source t.1 - vorticityField velocity target t.1‖ =
        dist (vorticityField velocity source t.1)
          (vorticityField velocity target t.1) := by rw [dist_eq_norm]
    _ ≤ (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
          dist source target := hlipschitz
    _ ≤ (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
          ((3 : ℝ) / 2) := by
      exact mul_le_mul_of_nonneg_left hdistance (NNReal.coe_nonneg _)
    _ = (3 / 2 : ℝ) *
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by ring

/-- Zero curl mode plus the exact addressed displacement bound removes the anchor completely:
the whole spatial vorticity receiver is controlled by the canonical derivative norm. -/
theorem norm_torusVorticityEvolution_le_three_halves_mul_canonical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) (q : SpatialTorus) :
    ‖torusVorticityEvolution solution t q‖ ≤
      (3 / 2 : ℝ) *
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
  have hintegrable : Integrable (torusVorticityEvolution solution t) :=
    continuousMap_integrable_on_compact (torusVorticityEvolution solution t)
  have hmean := integral_torusVorticityEvolution_eq_zero solution t
  have hidentity :
      (∫ y : SpatialTorus,
          torusVorticityEvolution solution t q -
            torusVorticityEvolution solution t y) =
        torusVorticityEvolution solution t q := by
    rw [integral_sub (integrable_const _) hintegrable, integral_const,
      probReal_univ, one_smul, hmean, sub_zero]
  calc
    ‖torusVorticityEvolution solution t q‖ =
        ‖∫ y : SpatialTorus,
          torusVorticityEvolution solution t q -
            torusVorticityEvolution solution t y‖ := by rw [hidentity]
    _ ≤ (3 / 2 : ℝ) *
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
      simpa [probReal_univ] using
        (norm_integral_le_of_norm_le_const
          (f := fun y : SpatialTorus ↦
            torusVorticityEvolution solution t q -
              torusVorticityEvolution solution t y)
          (C := (3 / 2 : ℝ) *
            (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ))
          (μ := (volume : Measure SpatialTorus))
          (Filter.Eventually.of_forall fun y : SpatialTorus ↦
            norm_torusVorticityEvolution_sub_le_three_halves_mul_canonical
              solution t q y))

/-- The exact compact-map norm inherits the anchor-free canonical derivative bound. -/
theorem norm_torusVorticityEvolution_map_le_three_halves_mul_canonical
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    ‖torusVorticityEvolution solution t‖ ≤
      (3 / 2 : ℝ) *
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
  exact (ContinuousMap.norm_le _ (by positivity)).mpr
    (norm_torusVorticityEvolution_le_three_halves_mul_canonical solution t)

/-- Totalized real-time presentation of the canonical spatial derivative receiver. -/
def openPeriodicCanonicalVorticityDerivativeRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo 0 T then
    (openPeriodicCanonicalVorticityLipschitzConstant solution ⟨s, hs⟩ : ℝ)
  else 0

@[simp]
theorem openPeriodicCanonicalVorticityDerivativeRate_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    openPeriodicCanonicalVorticityDerivativeRate solution s =
      (openPeriodicCanonicalVorticityLipschitzConstant solution ⟨s, hs⟩ : ℝ) := by
  simp [openPeriodicCanonicalVorticityDerivativeRate, hs]

theorem openPeriodicCanonicalVorticityDerivativeRate_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    0 ≤ openPeriodicCanonicalVorticityDerivativeRate solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [openPeriodicCanonicalVorticityDerivativeRate_eq solution hs]
    exact NNReal.coe_nonneg _
  · simp [openPeriodicCanonicalVorticityDerivativeRate, hs]

/-- **[proved-derived; formal-checked]** The actual critical vorticity receiver factors through
the canonical derivative population alone.  The curl zero-mode law supplies the missing
normalization, so no arbitrary anchor survives. -/
theorem criticalVorticityRate_le_three_halves_mul_canonicalDerivativeRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    criticalVorticityRate solution s ≤
      (3 / 2 : ℝ) * openPeriodicCanonicalVorticityDerivativeRate solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [criticalVorticityRate_eq solution hs,
      openPeriodicCanonicalVorticityDerivativeRate_eq solution hs]
    exact norm_torusVorticityEvolution_map_le_three_halves_mul_canonical
      solution ⟨s, hs⟩
  · simp [criticalVorticityRate, openPeriodicCanonicalVorticityDerivativeRate, hs]

/-- The anchored vorticity face at the zero torus occurrence. -/
def openPeriodicVorticityAnchorRateOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) : ℝ :=
  ‖torusVorticityEvolution solution t
    (euclideanToSpatialTorus (0 : Space))‖

/-- The exact geometric majorant: anchored value plus the derivative cost across the centered
radius-three-halves chart. -/
def openPeriodicCanonicalCriticalMajorantOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) : ℝ :=
  openPeriodicVorticityAnchorRateOn solution t +
    (3 / 2 : ℝ) * (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ)

/-- The anchor varies continuously on the strict-interior lifespan. -/
theorem openPeriodicVorticityAnchorRateOn_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (openPeriodicVorticityAnchorRateOn solution) := by
  have hvalue : Continuous (fun t : Set.Ioo (0 : ℝ) T ↦
      torusVorticityEvolution solution t
        (euclideanToSpatialTorus (0 : Space))) := by
    apply ((torusVorticityWorldTube solution).continuous.comp
      (continuous_id.prodMk continuous_const)).congr
    intro t
    rfl
  exact continuous_norm.comp hvalue

/-- The complete geometric majorant is continuous on the strict-interior lifespan. -/
theorem openPeriodicCanonicalCriticalMajorantOn_continuous
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (openPeriodicCanonicalCriticalMajorantOn solution) := by
  unfold openPeriodicCanonicalCriticalMajorantOn
  exact (openPeriodicVorticityAnchorRateOn_continuous solution).add
    (continuous_const.mul
      (NNReal.continuous_coe.comp
        (openPeriodicCanonicalVorticityLipschitzConstant_continuous solution)))

theorem openPeriodicCanonicalCriticalMajorantOn_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    0 ≤ openPeriodicCanonicalCriticalMajorantOn solution t := by
  unfold openPeriodicCanonicalCriticalMajorantOn openPeriodicVorticityAnchorRateOn
  positivity

/-- Every torus vorticity occurrence is controlled by the anchored value plus the exact cost of
transporting across its centered Euclidean representative. -/
theorem criticalVorticityRate_le_canonicalCriticalMajorantOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo (0 : ℝ) T) :
    criticalVorticityRate solution t.1 ≤
      openPeriodicCanonicalCriticalMajorantOn solution t := by
  rw [criticalVorticityRate_le_iff solution t.2]
  intro x
  let q : SpatialTorus := euclideanToSpatialTorus x
  let representative : Space := centeredEuclideanRepresentative q
  have hrepresentativeProjection :
      euclideanToSpatialTorus representative = q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative q
  have hxProjection : euclideanToSpatialTorus x = q := rfl
  have hfieldEq :
      vorticityField velocity x t.1 =
        vorticityField velocity representative t.1 :=
    isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun y ↦ vorticityField velocity y t.1)
      (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
      (hxProjection.trans hrepresentativeProjection.symm)
  have hrepresentativeNorm : ‖representative‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves q
  have hrepresentativeMem : representative ∈ Metric.closedBall (0 : Space) 3 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hrepresentativeNorm.trans (by norm_num)
  have hzeroMem : (0 : Space) ∈ Metric.closedBall (0 : Space) 3 := by
    simp
  have hlipschitz :=
    (openPeriodicCanonicalVorticityLipschitzOn_closedBall solution t).dist_le_mul
      representative hrepresentativeMem 0 hzeroMem
  have hdifference :
      ‖vorticityField velocity representative t.1 - vorticityField velocity 0 t.1‖ ≤
        (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
          ‖representative‖ := by
    simpa [dist_eq_norm] using hlipschitz
  have htransport :
      ‖vorticityField velocity representative t.1 - vorticityField velocity 0 t.1‖ ≤
        (3 / 2 : ℝ) *
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by
    calc
      ‖vorticityField velocity representative t.1 - vorticityField velocity 0 t.1‖ ≤
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
            ‖representative‖ := hdifference
      _ ≤ (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) *
            ((3 : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_left hrepresentativeNorm (NNReal.coe_nonneg _)
      _ = (3 / 2 : ℝ) *
            (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) := by ring
  rw [hfieldEq]
  calc
    ‖vorticityField velocity representative t.1‖ =
        ‖(vorticityField velocity representative t.1 -
            vorticityField velocity 0 t.1) + vorticityField velocity 0 t.1‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖vorticityField velocity representative t.1 -
          vorticityField velocity 0 t.1‖ +
        ‖vorticityField velocity 0 t.1‖ := norm_add_le _ _
    _ ≤ (3 / 2 : ℝ) *
          (openPeriodicCanonicalVorticityLipschitzConstant solution t : ℝ) +
        ‖vorticityField velocity 0 t.1‖ := add_le_add htransport le_rfl
    _ = openPeriodicCanonicalCriticalMajorantOn solution t := by
      unfold openPeriodicCanonicalCriticalMajorantOn openPeriodicVorticityAnchorRateOn
      rw [torusVorticityEvolution_projection]
      ring

/-- Totalized real-time presentation of the geometric majorant. -/
def openPeriodicCanonicalCriticalMajorant
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) : ℝ :=
  if hs : s ∈ Set.Ioo 0 T then
    openPeriodicCanonicalCriticalMajorantOn solution ⟨s, hs⟩
  else 0

@[simp]
theorem openPeriodicCanonicalCriticalMajorant_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    openPeriodicCanonicalCriticalMajorant solution s =
      openPeriodicCanonicalCriticalMajorantOn solution ⟨s, hs⟩ := by
  simp [openPeriodicCanonicalCriticalMajorant, hs]

theorem openPeriodicCanonicalCriticalMajorant_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    0 ≤ openPeriodicCanonicalCriticalMajorant solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [openPeriodicCanonicalCriticalMajorant_eq solution hs]
    exact openPeriodicCanonicalCriticalMajorantOn_nonneg solution ⟨s, hs⟩
  · simp [openPeriodicCanonicalCriticalMajorant, hs]

/-- The totalized critical receiver is bounded by the totalized geometric majorant at every real
time, including their common zero exterior. -/
theorem criticalVorticityRate_le_canonicalCriticalMajorant
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (s : ℝ) :
    criticalVorticityRate solution s ≤
      openPeriodicCanonicalCriticalMajorant solution s := by
  by_cases hs : s ∈ Set.Ioo 0 T
  · rw [openPeriodicCanonicalCriticalMajorant_eq solution hs]
    exact criticalVorticityRate_le_canonicalCriticalMajorantOn solution ⟨s, hs⟩
  · simp [criticalVorticityRate, openPeriodicCanonicalCriticalMajorant, hs]

/-- The totalized critical receiver is measurable; the exterior zero face is glued to the native
continuous interior section through a measurable dependent piece. -/
theorem criticalVorticityRate_measurable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Measurable (criticalVorticityRate solution) := by
  unfold criticalVorticityRate
  exact (continuous_criticalVorticityRateOn solution).measurable.dite
    measurable_const measurableSet_Ioo

/-- Terminal integrability of the canonical derivative population now supplies the exact BKM
critical-vorticity integral, with no separately retained anchor population. -/
theorem intervalIntegrable_criticalVorticityRate_of_canonicalDerivativeRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hderivative : IntervalIntegrable
      (openPeriodicCanonicalVorticityDerivativeRate solution) volume 0 T) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T := by
  have hscaled : IntervalIntegrable
      (fun s ↦ (3 / 2 : ℝ) *
        openPeriodicCanonicalVorticityDerivativeRate solution s) volume 0 T :=
    hderivative.const_mul (3 / 2 : ℝ)
  apply hscaled.mono_fun'
    (criticalVorticityRate_measurable solution).aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg (criticalVorticityRate_nonneg solution s)]
  exact criticalVorticityRate_le_three_halves_mul_canonicalDerivativeRate solution s

/-- Integrability of the retained anchor-plus-transport majorant constructs the exact critical
vorticity integral required by the BKM continuation passage. -/
theorem intervalIntegrable_criticalVorticityRate_of_canonicalCriticalMajorant
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hmajorant : IntervalIntegrable
      (openPeriodicCanonicalCriticalMajorant solution) volume 0 T) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T := by
  apply hmajorant.mono_fun'
    (criticalVorticityRate_measurable solution).aestronglyMeasurable
  filter_upwards with s
  rw [Real.norm_eq_abs, abs_of_nonneg (criticalVorticityRate_nonneg solution s)]
  exact criticalVorticityRate_le_canonicalCriticalMajorant solution s

/-- **[proved-derived, conditional; formal-checked]** The completed Hodge/restart continuation
owner now accepts the source-geometric anchor-plus-derivative majorant in place of a separately
postulated critical-vorticity integral. -/
def compatibleOpenPeriodicExtension_of_integrableCanonicalCriticalMajorant
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu)
    (hmajorant : IntervalIntegrable
      (openPeriodicCanonicalCriticalMajorant solution) volume 0 T) :
    CompatibleOpenPeriodicExtension solution :=
  compatibleOpenPeriodicExtension_of_integrableCriticalVorticity
    solution hnu
      (intervalIntegrable_criticalVorticityRate_of_canonicalCriticalMajorant
        solution hmajorant)

/-- **[proved-derived, conditional; formal-checked]** The completed Hodge/restart continuation
owner accepts terminal integrability of the canonical spatial derivative population itself.  The
zero curl mode and centered torus transport reconstruct the critical receiver exactly enough for
the official continuation carrier. -/
def compatibleOpenPeriodicExtension_of_integrableCanonicalDerivativeRate
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu)
    (hderivative : IntervalIntegrable
      (openPeriodicCanonicalVorticityDerivativeRate solution) volume 0 T) :
    CompatibleOpenPeriodicExtension solution :=
  compatibleOpenPeriodicExtension_of_integrableCriticalVorticity
    solution hnu
      (intervalIntegrable_criticalVorticityRate_of_canonicalDerivativeRate
        solution hderivative)

section Audit

#print axioms openPeriodicVorticityFourierMode_zero
#print axioms integral_complexTorusVorticitySlice_eq_zero
#print axioms norm_space_le_sqrt_three_mul_norm_complexifySpace
#print axioms integral_torusVorticityEvolution_eq_zero
#print axioms norm_torusVorticityEvolution_sub_le_three_halves_mul_canonical
#print axioms norm_torusVorticityEvolution_le_three_halves_mul_canonical
#print axioms norm_torusVorticityEvolution_map_le_three_halves_mul_canonical
#print axioms openPeriodicCanonicalVorticityDerivativeRate_nonneg
#print axioms criticalVorticityRate_le_three_halves_mul_canonicalDerivativeRate
#print axioms openPeriodicVorticityAnchorRateOn_continuous
#print axioms openPeriodicCanonicalCriticalMajorantOn_continuous
#print axioms openPeriodicCanonicalCriticalMajorantOn_nonneg
#print axioms criticalVorticityRate_le_canonicalCriticalMajorantOn
#print axioms openPeriodicCanonicalCriticalMajorant_nonneg
#print axioms criticalVorticityRate_le_canonicalCriticalMajorant
#print axioms criticalVorticityRate_measurable
#print axioms intervalIntegrable_criticalVorticityRate_of_canonicalDerivativeRate
#print axioms intervalIntegrable_criticalVorticityRate_of_canonicalCriticalMajorant
#print axioms compatibleOpenPeriodicExtension_of_integrableCanonicalDerivativeRate
#print axioms compatibleOpenPeriodicExtension_of_integrableCanonicalCriticalMajorant

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge

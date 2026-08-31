import ElementaryHolonics.Millennium.NavierStokesOpenFourierSpatialSymbols
import ElementaryHolonics.Millennium.NavierStokesTerminalFourier
import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Compact-interior nonlinear mode continuity and exact mild identity

All time intervals in this module are compact subsets of the strict open lifespan.  No value or
regularity at the terminal face is used.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate Laplacian Interval

namespace Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesTerminalFourier
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierSpatialSymbols

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual advective vector field of one spatial velocity slice. -/
def advectionField (u : InitialVelocity) : InitialVelocity :=
  fun x ↦ fderiv ℝ u x (u x)

theorem advectionField_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (advectionField u) := by
  exact (hu.fderiv_right (by simp)).clm_apply hu

theorem advectionField_isOnePeriodic
    {u : InitialVelocity} (hperiodic : IsOnePeriodic u) :
    IsOnePeriodic (advectionField u) := by
  intro x i
  change fderiv ℝ u (x + EuclideanSpace.single i 1)
      (u (x + EuclideanSpace.single i 1)) =
    fderiv ℝ u x (u x)
  rw [fderiv_isOnePeriodic u hperiodic x i, hperiodic x i]

/-- The actual advective field descended jointly to strict-interior time and the genuine torus. -/
def torusAdvectionWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    C((Ioo 0 T) × SpatialTorus, Space) where
  toFun := fun z ↦
    advectionField (fun x ↦ velocity x z.1.1) (euclideanRepresentative z.2)
  continuous_toFun := by
    have hsourceJoint : Continuous
        (fun z : (Ioo 0 T) × Space ↦
          ((fderiv ℝ (Function.uncurry velocity) (z.2, z.1.1)).comp
            spatialInclusion) (velocity z.2 z.1.1)) := by
      have hderivative : Continuous
          (fun z : (Ioo 0 T) × Space ↦
            (fderiv ℝ (Function.uncurry velocity) (z.2, z.1.1)).comp
              spatialInclusion) := by
        exact
          (openPeriodicSolutionOn_jointSpatialVelocityDerivative_continuousOn solution)
            |>.comp_continuous
              (continuous_snd.prodMk
                (continuous_subtype_val.comp continuous_fst))
              (fun z ↦ ⟨Set.mem_univ z.2, z.1.2⟩)
      have hvelocity : Continuous
          (fun z : (Ioo 0 T) × Space ↦ velocity z.2 z.1.1) := by
        rw [continuous_iff_continuousAt]
        intro z
        have hdomain : openSpaceTimeSlab T ∈ 𝓝 (z.2, z.1.1) := by
          apply Filter.mem_of_superset
            (prod_mem_nhds Filter.univ_mem
              (Ioo_mem_nhds z.1.2.1 z.1.2.2))
          rintro ⟨y, τ⟩ ⟨_hy, hτ⟩
          exact ⟨Set.mem_univ y, hτ.1.le, hτ.2⟩
        exact (solution.velocitySmooth.contDiffAt hdomain).continuousAt.comp_of_eq
          (continuousAt_snd.prodMk
            (continuousAt_subtype_val.comp continuousAt_fst)) rfl
      exact hderivative.clm_apply hvelocity
    have hsource : Continuous
        (fun z : (Ioo 0 T) × Space ↦
          advectionField (fun x ↦ velocity x z.1.1) z.2) := by
      apply hsourceJoint.congr
      intro z
      rw [advectionField,
        openPeriodicSolutionOn_fderiv_velocitySlice_eq_jointSpatialDerivative
          solution z.2 z.1]
    letI : LocallyCompactSpace (Ioo 0 T) := isOpen_Ioo.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (advectionField (fun x ↦ velocity x z.1.1))
      (advectionField_isOnePeriodic
        (solution.velocityPeriodic z.1.1 ⟨z.1.2.1.le, z.1.2.2⟩))
    exact (euclideanToSpatialTorus_representative _).symm

/-- Continuous path of actual advective torus fields. -/
def torusAdvectionEvolution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    C(Ioo 0 T, C(SpatialTorus, Space)) :=
  ContinuousMap.curry (torusAdvectionWorldTube solution)

/-- Genuine-torus coefficient of the actual advective field. -/
def openAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  vectorSpatialFourierCoeff
    (advectionField (fun x ↦ velocity x t.1))
    (advectionField_contDiff
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2)).continuous
    (advectionField_isOnePeriodic
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)) k

/-- The quotient-continuous receiver equals the actual Euclidean-slice coefficient. -/
theorem continuousTorusVectorFourierCoeff_torusAdvectionEvolution_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    continuousTorusVectorFourierCoeff (torusAdvectionEvolution solution t) k =
      openAdvectionMode solution t k := by
  ext component
  rw [continuousTorusVectorFourierCoeff, openAdvectionMode,
    vectorSpatialFourierCoeff_apply]
  unfold complexTorusVelocityComponent
  apply congrArg (fun field : SpatialTorus → ℂ ↦
    torusSpatialFourierCoeff field k)
  funext q
  rfl

/-- The actual nonlinear advective mode is continuous throughout the strict open lifespan. -/
theorem continuous_openAdvectionMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (k : SpatialFrequency) :
    Continuous (fun t : Ioo 0 T ↦ openAdvectionMode solution t k) := by
  have hcontinuous :=
    (continuous_continuousTorusVectorFourierCoeff k).comp
      (torusAdvectionEvolution solution).continuous
  apply hcontinuous.congr
  intro t
  exact continuousTorusVectorFourierCoeff_torusAdvectionEvolution_eq solution t k

/-- Restoring the pressure coefficient in the strong momentum return leaves exactly viscosity
minus the actual advective coefficient. -/
theorem pressureFreeMomentumMode_eq_viscous_sub_advection
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    pressureFreeMomentumMode solution t k =
      (nu : ℂ) • openVelocityLaplacianMode solution t k -
        openAdvectionMode solution t k := by
  ext component
  let u : InitialVelocity := fun x ↦ velocity x t.1
  let p : Space → ℝ := fun x ↦ pressure x t.1
  let A : InitialVelocity := advectionField u
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution t.2
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution t.2
  have huPeriodic : IsOnePeriodic u :=
    solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  have hpPeriodic : IsOnePeriodic p :=
    solution.pressurePeriodic t.1 ⟨t.2.1.le, t.2.2⟩
  let lapLift : C(SpatialTorus, ℂ) := periodicTorusLift
    (complexVelocityComponent (Δ u) component)
    (continuous_complexVelocityComponent (laplacian_contDiff hu).continuous component)
    (isOnePeriodic_complexVelocityComponent
      (laplacian_isOnePeriodic
        (hu.of_le (WithTop.coe_le_coe.mpr le_top)) huPeriodic) component)
  let pressureLift : C(SpatialTorus, ℂ) := periodicTorusLift
    (complexVelocityComponent (gradient p) component)
    (continuous_complexVelocityComponent (gradient_contDiff hp).continuous component)
    (isOnePeriodic_complexVelocityComponent
      (gradient_isOnePeriodic p hpPeriodic) component)
  let advectionLift : C(SpatialTorus, ℂ) := periodicTorusLift
    (complexVelocityComponent A component)
    (continuous_complexVelocityComponent (advectionField_contDiff hu).continuous component)
    (isOnePeriodic_complexVelocityComponent
      (advectionField_isOnePeriodic huPeriodic) component)
  have hLint : Integrable
      (fun q : SpatialTorus ↦ UnitAddTorus.mFourier (-k) q * lapLift q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * lapLift)
  have hPint : Integrable
      (fun q : SpatialTorus ↦ UnitAddTorus.mFourier (-k) q * pressureLift q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * pressureLift)
  have hAint : Integrable
      (fun q : SpatialTorus ↦ UnitAddTorus.mFourier (-k) q * advectionLift q) :=
    continuousMap_integrable_on_compact (UnitAddTorus.mFourier (-k) * advectionLift)
  simp only [pressureFreeMomentumMode, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  rw [openPressureGradientMode, openVelocityLaplacianMode, openAdvectionMode]
  rw [vectorSpatialFourierCoeff_apply, vectorSpatialFourierCoeff_apply,
    vectorSpatialFourierCoeff_apply]
  change
    (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q *
      (((nu • Δ u (euclideanRepresentative q) -
        gradient p (euclideanRepresentative q) -
        A (euclideanRepresentative q)) component : ℝ) : ℂ)) +
      (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q * pressureLift q) =
    (nu : ℂ) •
      (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q * lapLift q) -
      (∫ q : SpatialTorus, UnitAddTorus.mFourier (-k) q * advectionLift q)
  have hintegrand :
      (fun q : SpatialTorus ↦ UnitAddTorus.mFourier (-k) q *
        (((nu • Δ u (euclideanRepresentative q) -
          gradient p (euclideanRepresentative q) -
          A (euclideanRepresentative q)) component : ℝ) : ℂ)) =
      fun q ↦ (nu : ℂ) *
          (UnitAddTorus.mFourier (-k) q * lapLift q) -
        (UnitAddTorus.mFourier (-k) q * pressureLift q) -
        (UnitAddTorus.mFourier (-k) q * advectionLift q) := by
    funext q
    change UnitAddTorus.mFourier (-k) q *
        ((nu * (Δ u (euclideanRepresentative q)) component -
          (gradient p (euclideanRepresentative q)) component -
          (A (euclideanRepresentative q)) component : ℝ) : ℂ) =
      (nu : ℂ) * (UnitAddTorus.mFourier (-k) q *
        (((Δ u) (euclideanRepresentative q) component : ℝ) : ℂ)) -
      (UnitAddTorus.mFourier (-k) q *
        ((gradient p (euclideanRepresentative q) component : ℝ) : ℂ)) -
      (UnitAddTorus.mFourier (-k) q *
        ((A (euclideanRepresentative q) component : ℝ) : ℂ))
    push_cast
    ring
  rw [hintegrand]
  have hout :
      (∫ q : SpatialTorus,
        (nu : ℂ) * (UnitAddTorus.mFourier (-k) q * lapLift q) -
          (UnitAddTorus.mFourier (-k) q * pressureLift q) -
          (UnitAddTorus.mFourier (-k) q * advectionLift q)) =
        (∫ q : SpatialTorus,
          (nu : ℂ) * (UnitAddTorus.mFourier (-k) q * lapLift q) -
            (UnitAddTorus.mFourier (-k) q * pressureLift q)) -
        (∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) q * advectionLift q) :=
    integral_sub ((hLint.const_mul nu).sub hPint) hAint
  rw [hout]
  have hinner :
      (∫ q : SpatialTorus,
        (nu : ℂ) * (UnitAddTorus.mFourier (-k) q * lapLift q) -
          (UnitAddTorus.mFourier (-k) q * pressureLift q)) =
        (∫ q : SpatialTorus,
          (nu : ℂ) * (UnitAddTorus.mFourier (-k) q * lapLift q)) -
        (∫ q : SpatialTorus,
          UnitAddTorus.mFourier (-k) q * pressureLift q) :=
    integral_sub (hLint.const_mul nu) hPint
  rw [hinner]
  rw [integral_const_mul]
  change ((nu : ℂ) * _ - _ - _) + _ = (nu : ℂ) * _ - _
  ring

/-- The actual nonlinear vorticity-mode source is minus the frequency curl of the genuine
advective coefficient. -/
def vorticityNonlinearMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexVector :=
  -frequencyCurlMultiplier k (openAdvectionMode solution t k)

/-- The exact pressure-free vorticity ODE in diagonal Stokes form. -/
theorem openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (fun τ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
      (((-(nu * torusStokesEigenvalue k) : ℝ) : ℂ) •
          frequencyCurlMultiplier k (velocityMode velocity k t.1) +
        vorticityNonlinearMode solution t k) t.1 := by
  have hderiv :=
    openPeriodicSolutionOn_hasDerivAt_vorticityMode_pressureFree solution t k
  convert hderiv using 1
  rw [pressureFreeMomentumMode_eq_viscous_sub_advection solution t k,
    openPeriodicSolutionOn_velocityLaplacianMode_eq_stokes solution t k]
  change _ = frequencyCurlMultiplierCLM k
      ((nu : ℂ) • (-(torusStokesEigenvalue k : ℂ) •
        velocityMode velocity k t.1) - openAdvectionMode solution t k)
  rw [map_sub, map_smul, map_smul]
  simp only [frequencyCurlMultiplierCLM_apply, vorticityNonlinearMode,
    smul_smul]
  ext component
  simp
  ring

/-- The actual nonlinear vorticity-mode source is continuous on the strict interior. -/
theorem continuous_vorticityNonlinearMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (k : SpatialFrequency) :
    Continuous (fun t : Ioo 0 T ↦ vorticityNonlinearMode solution t k) := by
  exact continuous_neg.comp
    ((frequencyCurlMultiplierCLM k).continuous.comp
      (continuous_openAdvectionMode solution k))

/-- Clamp a real time to a chosen compact strict-interior interval and retain its interior
certificate.  On the interval itself this is exactly the original time. -/
def compactInteriorTime
    {T s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) (τ : ℝ) :
    Ioo (0 : ℝ) T :=
  ⟨(Set.projIcc s t hst τ).1,
    hs.trans_le (Set.projIcc s t hst τ).2.1,
    (Set.projIcc s t hst τ).2.2.trans_lt ht⟩

theorem continuous_compactInteriorTime
    {T s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    Continuous (compactInteriorTime hs hst ht) :=
  ((continuous_subtype_val.comp
    (continuous_projIcc : Continuous (Set.projIcc s t hst))).subtype_mk _)

@[simp]
theorem compactInteriorTime_eq
    {T s t : ℝ} (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    {τ : ℝ} (hτ : τ ∈ Icc s t) :
    (compactInteriorTime hs hst ht τ).1 = τ := by
  exact congrArg Subtype.val (Set.projIcc_of_mem hst hτ)

/-- Continuous real-time extension of the actual nonlinear mode, changing it only outside the
chosen compact interval. -/
def compactVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  vorticityNonlinearMode solution (compactInteriorTime hs hst ht τ) k

theorem continuous_compactVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    Continuous (compactVorticityNonlinearMode solution hs hst ht k) :=
  (continuous_vorticityNonlinearMode solution k).comp
    (continuous_compactInteriorTime hs hst ht)

/-- On the addressed interval, the compact extension is literally the nonlinear mode of the
actual open solution at that time. -/
theorem compactVorticityNonlinearMode_eq_actual
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    compactVorticityNonlinearMode solution hs hst ht k τ =
      vorticityNonlinearMode solution
        ⟨τ, hs.trans_le hτ.1, hτ.2.trans_lt ht⟩ k := by
  unfold compactVorticityNonlinearMode
  congr 2
  apply Subtype.ext
  exact compactInteriorTime_eq hs hst ht hτ

/-- The clamped nonlinear mode is interval-integrable on its addressed compact interval. -/
theorem compactVorticityNonlinearMode_intervalIntegrable
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    IntervalIntegrable (compactVorticityNonlinearMode solution hs hst ht k)
      volume s t :=
  (continuous_compactVorticityNonlinearMode solution hs hst ht k).intervalIntegrable _ _

/-- The same Stokes vorticity ODE, presented over the real scalar structure used by the
integrating factor. -/
theorem openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes_real
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (fun τ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
      ((-(nu * torusStokesEigenvalue k) : ℝ) •
          frequencyCurlMultiplier k (velocityMode velocity k t.1) +
        vorticityNonlinearMode solution t k) t.1 := by
  have h := openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes solution t k
  convert h using 1
  ext component
  simp

/-- The vorticity mode multiplied by its exact diagonal Stokes integrating factor. -/
private def vorticityIntegratingFactorMode
    {nu : ℝ} {velocity : VelocityField}
    (k : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  Real.exp ((nu * torusStokesEigenvalue k) * τ) •
    frequencyCurlMultiplier k (velocityMode velocity k τ)

/-- The compactly extended nonlinear source multiplied by the same integrating factor. -/
private def compactWeightedVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  Real.exp ((nu * torusStokesEigenvalue k) * τ) •
    compactVorticityNonlinearMode solution hs hst ht k τ

private theorem continuous_compactWeightedVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    Continuous
      (compactWeightedVorticityNonlinearMode solution hs hst ht k) := by
  exact (Real.continuous_exp.comp
    (continuous_const.mul continuous_id)).smul
      (continuous_compactVorticityNonlinearMode solution hs hst ht k)

private theorem compactWeightedVorticityNonlinearMode_intervalIntegrable
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    IntervalIntegrable
      (compactWeightedVorticityNonlinearMode solution hs hst ht k)
      volume s t :=
  (continuous_compactWeightedVorticityNonlinearMode solution hs hst ht k)
    |>.intervalIntegrable _ _

/-- On the addressed compact interval, the integrating-factor mode differentiates exactly to
the weighted actual nonlinear source. -/
private theorem hasDerivAt_vorticityIntegratingFactorMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    HasDerivAt
      (vorticityIntegratingFactorMode (nu := nu) (velocity := velocity) k)
      (compactWeightedVorticityNonlinearMode solution hs hst ht k τ) τ := by
  let τi : Ioo (0 : ℝ) T :=
    ⟨τ, hs.trans_le hτ.1, hτ.2.trans_lt ht⟩
  have hmode :=
    openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes_real solution τi k
  have hsource :
      compactVorticityNonlinearMode solution hs hst ht k τ =
        vorticityNonlinearMode solution τi k := by
    exact compactVorticityNonlinearMode_eq_actual
      solution hs hst ht k hτ
  have hexp :
      HasDerivAt
        (fun x : ℝ ↦ Real.exp ((nu * torusStokesEigenvalue k) * x))
        ((nu * torusStokesEigenvalue k) *
          Real.exp ((nu * torusStokesEigenvalue k) * τ)) τ := by
    have h := ((hasDerivAt_id τ).const_mul
      (nu * torusStokesEigenvalue k)).exp
    simpa [mul_comm] using h
  have hproduct := hexp.smul hmode
  apply hproduct.congr_deriv
  rw [compactWeightedVorticityNonlinearMode, hsource]
  ext component
  simp
  ring

/-- **Exact compact-interior integrating-factor identity.**  This is the vector-valued FTC
applied to the actual pressure-free vorticity modal ODE. -/
private theorem openPeriodicSolutionOn_vorticityMode_integratingFactor_identity
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    (∫ τ in s..t,
      compactWeightedVorticityNonlinearMode solution hs hst ht k τ) =
      vorticityIntegratingFactorMode (nu := nu) (velocity := velocity) k t -
        vorticityIntegratingFactorMode (nu := nu) (velocity := velocity) k s := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro τ hτ
    rw [Set.uIcc_of_le hst] at hτ
    exact hasDerivAt_vorticityIntegratingFactorMode
      solution hs hst ht k hτ
  · exact compactWeightedVorticityNonlinearMode_intervalIntegrable
      solution hs hst ht k

/-- The actual nonlinear modal source transported from its source time to the addressed final
time by the diagonal Stokes semigroup. -/
def compactStokesTransportedVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) (τ : ℝ) : ComplexVector :=
  heatStokesMultiplier nu (t - τ) k •
    compactVorticityNonlinearMode solution hs hst ht k τ

theorem continuous_compactStokesTransportedVorticityNonlinearMode
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    Continuous
      (compactStokesTransportedVorticityNonlinearMode solution hs hst ht k) := by
  unfold compactStokesTransportedVorticityNonlinearMode heatStokesMultiplier
  exact (Real.continuous_exp.comp (by fun_prop)).smul
    (continuous_compactVorticityNonlinearMode solution hs hst ht k)

/-- **Exact compact-interior mild vorticity-mode identity.**  Every term is derived from the
genuine open periodic solution.  The only extension is the continuous clamp, which equals the
actual nonlinear source at every integration time in `[s,t]`. -/
theorem openPeriodicSolutionOn_vorticityMode_mild_identity
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    frequencyCurlMultiplier k (velocityMode velocity k t) =
      heatStokesMultiplier nu (t - s) k •
          frequencyCurlMultiplier k (velocityMode velocity k s) +
        ∫ τ in s..t,
          compactStokesTransportedVorticityNonlinearMode
            solution hs hst ht k τ := by
  let rate : ℝ := nu * torusStokesEigenvalue k
  have hweighted :=
    openPeriodicSolutionOn_vorticityMode_integratingFactor_identity
      solution hs hst ht k
  have htransport :
      (∫ τ in s..t,
        compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k τ) =
        Real.exp (-rate * t) •
          ∫ τ in s..t,
            compactWeightedVorticityNonlinearMode
              solution hs hst ht k τ := by
    rw [← intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr
    intro τ _hτ
    change Real.exp (-(nu * (t - τ) * torusStokesEigenvalue k)) •
        compactVorticityNonlinearMode solution hs hst ht k τ =
      Real.exp (-rate * t) •
        (Real.exp (rate * τ) •
          compactVorticityNonlinearMode solution hs hst ht k τ)
    rw [smul_smul, ← Real.exp_add]
    congr 2
    dsimp [rate]
    ring
  have hcancel : Real.exp (-rate * t) * Real.exp (rate * t) = 1 := by
    calc
      Real.exp (-rate * t) * Real.exp (rate * t) =
          Real.exp (-rate * t + rate * t) := (Real.exp_add _ _).symm
      _ = 1 := by rw [show -rate * t + rate * t = 0 by ring, Real.exp_zero]
  have hshift :
      Real.exp (-rate * t) * Real.exp (rate * s) =
        Real.exp (-rate * (t - s)) := by
    rw [← Real.exp_add]
    apply congrArg Real.exp
    ring
  have hheat :
      heatStokesMultiplier nu (t - s) k =
        Real.exp (-rate * (t - s)) := by
    unfold heatStokesMultiplier
    apply congrArg Real.exp
    dsimp [rate]
    ring
  rw [htransport, hweighted]
  simp only [vorticityIntegratingFactorMode]
  rw [hheat, smul_sub, smul_smul, smul_smul, hcancel, hshift, one_smul]
  abel

section Audit

#print axioms continuous_vorticityNonlinearMode
#print axioms openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes_real
#print axioms openPeriodicSolutionOn_vorticityMode_mild_identity

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity

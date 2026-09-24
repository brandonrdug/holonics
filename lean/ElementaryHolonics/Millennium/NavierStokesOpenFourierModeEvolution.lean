import ElementaryHolonics.Millennium.NavierStokesCoordinateH1Production
import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Strict-interior Fourier-mode evolution of an open periodic solution

This module is intentionally confined to the open lifespan.  It derives each mode equation from
the actual pointwise momentum and curled-momentum owners; it does not posit a spectral evolution
law and makes no terminal-time claim.
-/

noncomputable section

open ContDiff Function Set Topology MeasureTheory
open scoped BigOperators ComplexConjugate Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/- Keep the probability-Haar chart used by the genuine-torus Fourier owner. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A strict-interior time section has the Eulerian joint time jet as its actual derivative. -/
theorem openPeriodicSolutionOn_hasDerivAt_velocity_time
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (velocity x) (eulerianTimeJet velocity x t) t := by
  have hdomain : openSpaceTimeSlab T ∈ 𝓝 (x, t) := by
    apply Filter.mem_of_superset
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2))
    rintro ⟨y, τ⟩ ⟨_hy, hτ⟩
    exact ⟨Set.mem_univ y, hτ.1.le, hτ.2⟩
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (solution.velocitySmooth.contDiffAt hdomain)
      |>.differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt

/-- Differentiating the admitted spatial period in time shows that the actual Eulerian time jet
is itself one-periodic. -/
theorem openPeriodicSolutionOn_eulerianTimeJet_isOnePeriodic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsOnePeriodic (fun x ↦ eulerianTimeJet velocity x t) := by
  intro x i
  let shifted : Space := x + EuclideanSpace.single i (1 : ℝ)
  have heq : velocity shifted =ᶠ[𝓝 t] velocity x := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with τ hτ
    exact solution.velocityPeriodic τ ⟨hτ.1.le, hτ.2⟩ x i
  have hshifted := openPeriodicSolutionOn_hasDerivAt_velocity_time solution shifted ht
  have hunshifted := openPeriodicSolutionOn_hasDerivAt_velocity_time solution x ht
  exact (heq.hasDerivAt_iff.mp hshifted).unique hunshifted

/-- The actual velocity, descended through the spatial quotient throughout the strict interior. -/
def torusVelocityWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    C((Ioo 0 T) × SpatialTorus, Space) where
  toFun := fun z ↦ velocity (euclideanRepresentative z.2) z.1.1
  continuous_toFun := by
    have hsource : Continuous
        (fun z : (Ioo 0 T) × Space ↦ velocity z.2 z.1.1) := by
      rw [continuous_iff_continuousAt]
      intro z
      have hdomain : openSpaceTimeSlab T ∈ 𝓝 (z.2, z.1.1) := by
        apply Filter.mem_of_superset
          (prod_mem_nhds Filter.univ_mem
            (Ioo_mem_nhds z.1.2.1 z.1.2.2))
        rintro ⟨y, τ⟩ ⟨_hy, hτ⟩
        exact ⟨Set.mem_univ y, hτ.1.le, hτ.2⟩
      have hvelocityAt : ContinuousAt (Function.uncurry velocity) (z.2, z.1.1) :=
        (solution.velocitySmooth.contDiffAt hdomain).continuousAt
      exact hvelocityAt.comp_of_eq
        (continuousAt_snd.prodMk (continuousAt_subtype_val.comp continuousAt_fst)) rfl
    letI : LocallyCompactSpace (Ioo 0 T) := isOpen_Ioo.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun x ↦ velocity x z.1.1)
      (solution.velocityPeriodic z.1.1 ⟨z.1.2.1.le, z.1.2.2⟩)
    exact (euclideanToSpatialTorus_representative _).symm

/-- The actual Eulerian time jet, descended jointly through the spatial quotient. -/
def torusEulerianTimeJetWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    C((Ioo 0 T) × SpatialTorus, Space) where
  toFun := fun z ↦ eulerianTimeJet velocity (euclideanRepresentative z.2) z.1.1
  continuous_toFun := by
    have hinterior : ContDiffOn ℝ ∞ (Function.uncurry velocity)
        (Set.univ ×ˢ Ioo 0 T) := by
      apply solution.velocitySmooth.mono
      rintro ⟨x, τ⟩ ⟨_hx, hτ⟩
      exact ⟨Set.mem_univ x, hτ.1.le, hτ.2⟩
    have hopen : IsOpen ((Set.univ : Set Space) ×ˢ Ioo (0 : ℝ) T) :=
      isOpen_univ.prod isOpen_Ioo
    have hjet : ContinuousOn
        (fun z : Space × ℝ ↦ fderiv ℝ (Function.uncurry velocity) z timeDirection)
        (Set.univ ×ˢ Ioo 0 T) := by
      exact (hinterior.continuousOn_fderiv_of_isOpen hopen (by simp)).clm_apply
        continuousOn_const
    have hsource : Continuous
        (fun z : (Ioo 0 T) × Space ↦ eulerianTimeJet velocity z.2 z.1.1) := by
      rw [continuous_iff_continuousAt]
      intro z
      have hjetAt : ContinuousAt
          (fun w : Space × ℝ ↦
            fderiv ℝ (Function.uncurry velocity) w timeDirection) (z.2, z.1.1) :=
        hjet.continuousAt
          (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds z.1.2.1 z.1.2.2))
      have hcomp := hjetAt.comp_of_eq
        (continuousAt_snd.prodMk (continuousAt_subtype_val.comp continuousAt_fst)) rfl
      unfold eulerianTimeJet
      change ContinuousAt
        (fun w : (Ioo 0 T) × Space ↦
          fderiv ℝ (Function.uncurry velocity) (w.2, w.1.1) timeDirection) z
      exact hcomp
    letI : LocallyCompactSpace (Ioo 0 T) := isOpen_Ioo.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
      (fun x ↦ eulerianTimeJet velocity x z.1.1)
      (openPeriodicSolutionOn_eulerianTimeJet_isOnePeriodic solution z.1.2)
    exact (euclideanToSpatialTorus_representative _).symm

/-! ## Differentiating a genuine-torus coefficient in time -/

/-- The unbundled coefficient integrand of one actual velocity component. -/
def velocityModeIntegrand
    (velocity : VelocityField) (k : SpatialFrequency) (component : Fin 3)
    (t : ℝ) (q : SpatialTorus) : ℂ :=
  UnitAddTorus.mFourier (-k) q *
    (velocity (euclideanRepresentative q) t component : ℂ)

/-- The matching integrand of the actual Eulerian time jet. -/
def eulerianTimeJetModeIntegrand
    (velocity : VelocityField) (k : SpatialFrequency) (component : Fin 3)
    (t : ℝ) (q : SpatialTorus) : ℂ :=
  UnitAddTorus.mFourier (-k) q *
    (eulerianTimeJet velocity (euclideanRepresentative q) t component : ℂ)

/-- One component of the actual velocity coefficient, written in the same normalized Haar chart
as the established torus coefficient.  Outside the admitted lifespan this is only an unbundled
integral; all evolution theorems below are strict-interior statements. -/
def velocityModeComponent
    (velocity : VelocityField) (k : SpatialFrequency) (component : Fin 3)
    (t : ℝ) : ℂ :=
  ∫ q : SpatialTorus, velocityModeIntegrand velocity k component t q

/-- At an admitted time the unbundled integral is exactly the established genuine-torus mode. -/
theorem velocityModeComponent_eq_openPeriodicVelocityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) (component : Fin 3) :
    velocityModeComponent velocity k component t.1 =
      openPeriodicVelocityFourierMode solution t k component := by
  rw [openPeriodicVelocityFourierMode, vectorSpatialFourierCoeff_apply]
  rfl

/-- **Exact time derivative of one genuine-torus velocity coefficient.**  The derivative is
obtained by differentiating the actual descended field under normalized Haar integration. -/
theorem openPeriodicSolutionOn_hasDerivAt_velocityModeComponent
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) (component : Fin 3) :
    HasDerivAt (velocityModeComponent velocity k component)
      (∫ q : SpatialTorus, eulerianTimeJetModeIntegrand velocity k component t q) t := by
  let lower : ℝ := t / 2
  let upper : ℝ := (t + T) / 2
  let timeSet : Set ℝ := Ioo lower upper
  have hlower0 : 0 < lower := by dsimp [lower]; linarith [ht.1]
  have htupper : t < upper := by dsimp [upper]; linarith [ht.2]
  have hupperT : upper < T := by dsimp [upper]; linarith [ht.2]
  have hlowerUpper : lower ≤ upper := by
    dsimp [lower, upper]
    linarith [ht.1, ht.2]
  have htimeSet : timeSet ∈ 𝓝 t := by
    apply Ioo_mem_nhds <;> dsimp [timeSet, lower, upper] <;> linarith [ht.1, ht.2]
  let compactToInterior : Icc lower upper → Ioo (0 : ℝ) T :=
    fun τ ↦ ⟨τ.1, hlower0.trans_le τ.2.1, τ.2.2.trans_lt hupperT⟩
  have hcompactToInterior : Continuous compactToInterior := by
    exact continuous_subtype_val.subtype_mk _
  let jetNorm : C((Icc lower upper) × SpatialTorus, ℝ) := {
    toFun := fun z ↦
      ‖(torusEulerianTimeJetWorldTube solution (compactToInterior z.1, z.2)
          component : ℝ)‖
    continuous_toFun := by
      exact continuous_norm.comp
        ((EuclideanSpace.proj component).continuous.comp
          ((torusEulerianTimeJetWorldTube solution).continuous.comp
            (hcompactToInterior.comp continuous_fst |>.prodMk continuous_snd))) }
  have hcompactDomain :
      IsCompact (Set.univ : Set ((Icc lower upper) × SpatialTorus)) := isCompact_univ
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (hcompactDomain.bddAbove_image jetNorm.continuous.continuousOn)
  have hFmeas : ∀ᶠ τ in 𝓝 t, AEStronglyMeasurable
      (velocityModeIntegrand velocity k component τ) := by
    filter_upwards [htimeSet] with τ hτ
    let τi : Ioo (0 : ℝ) T := ⟨τ, hlower0.trans hτ.1, hτ.2.trans hupperT⟩
    have hcontinuous : Continuous (velocityModeIntegrand velocity k component τ) := by
      have hcomponent : Continuous (fun q : SpatialTorus ↦
          ((torusVelocityWorldTube solution (τi, q) component : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp
          ((EuclideanSpace.proj component).continuous.comp
            ((torusVelocityWorldTube solution).continuous.comp
              (continuous_const.prodMk continuous_id)))
      exact (UnitAddTorus.mFourier (-k)).continuous.mul hcomponent
    exact hcontinuous.aestronglyMeasurable
  have hFint : Integrable (velocityModeIntegrand velocity k component t) := by
    let ti : Ioo (0 : ℝ) T := ⟨t, ht⟩
    let field : C(SpatialTorus, ℂ) := {
      toFun := velocityModeIntegrand velocity k component t
      continuous_toFun := by
        have hcomponent : Continuous (fun q : SpatialTorus ↦
            ((torusVelocityWorldTube solution (ti, q) component : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.comp
            ((EuclideanSpace.proj component).continuous.comp
              ((torusVelocityWorldTube solution).continuous.comp
                (continuous_const.prodMk continuous_id)))
        exact (UnitAddTorus.mFourier (-k)).continuous.mul hcomponent }
    exact continuousMap_integrable_on_compact field
  have hF'meas : AEStronglyMeasurable
      (eulerianTimeJetModeIntegrand velocity k component t) := by
    let ti : Ioo (0 : ℝ) T := ⟨t, ht⟩
    have hcomponent : Continuous (fun q : SpatialTorus ↦
        ((torusEulerianTimeJetWorldTube solution (ti, q) component : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((EuclideanSpace.proj component).continuous.comp
          ((torusEulerianTimeJetWorldTube solution).continuous.comp
            (continuous_const.prodMk continuous_id)))
    exact ((UnitAddTorus.mFourier (-k)).continuous.mul hcomponent).aestronglyMeasurable
  have hbound : ∀ᵐ q : SpatialTorus, ∀ τ ∈ timeSet,
      ‖eulerianTimeJetModeIntegrand velocity k component τ q‖ ≤ C := by
    filter_upwards [] with q
    intro τ hτ
    rw [eulerianTimeJetModeIntegrand, norm_mul]
    have hcharacter : ‖UnitAddTorus.mFourier (-k) q‖ = 1 := by
      simp only [UnitAddTorus.mFourier, fourier_apply, ContinuousMap.coe_mk,
        norm_prod, Circle.norm_coe, Finset.prod_const_one]
    rw [hcharacter, one_mul, Complex.norm_real]
    apply hC
    let τc : Icc lower upper := ⟨τ, hτ.1.le, hτ.2.le⟩
    refine ⟨(τc, q), Set.mem_univ _, ?_⟩
    rfl
  have hboundIntegrable : Integrable (fun _ : SpatialTorus ↦ C) :=
    integrable_const C
  have hdiff : ∀ᵐ q : SpatialTorus, ∀ τ ∈ timeSet,
      HasDerivAt
        (fun σ ↦ velocityModeIntegrand velocity k component σ q)
        (eulerianTimeJetModeIntegrand velocity k component τ q) τ := by
    filter_upwards [] with q
    intro τ hτ
    have hτi : τ ∈ Ioo (0 : ℝ) T :=
      ⟨hlower0.trans hτ.1, hτ.2.trans hupperT⟩
    have hvelocity :=
      openPeriodicSolutionOn_hasDerivAt_velocity_time solution
        (euclideanRepresentative q) hτi
    have hreal := (EuclideanSpace.proj component).hasFDerivAt.comp_hasDerivAt
      τ hvelocity
    have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt τ hreal
    have hscaled := hcomplex.const_smul (UnitAddTorus.mFourier (-k) q)
    change HasDerivAt
      (fun σ : ℝ ↦ UnitAddTorus.mFourier (-k) q *
        (velocity (euclideanRepresentative q) σ component : ℂ))
      (UnitAddTorus.mFourier (-k) q *
        (eulerianTimeJet velocity (euclideanRepresentative q) τ component : ℂ)) τ
      at hscaled
    exact hscaled
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := velocityModeIntegrand velocity k component)
    (F' := eulerianTimeJetModeIntegrand velocity k component)
    (bound := fun _ : SpatialTorus ↦ C) (x₀ := t) (s := timeSet)
    (μ := volume) htimeSet hFmeas hFint hF'meas hbound hboundIntegrable hdiff).2

/-! ## The exact unforced mode ODE -/

/-- Fourier integrand of the complete unforced momentum right-hand side.  The pressure gradient
is deliberately retained here; its later cancellation is a separate spatial Fourier passage. -/
def unforcedMomentumModeIntegrand
    (nu : ℝ) (velocity : VelocityField) (pressure : PressureField)
    (k : SpatialFrequency) (component : Fin 3) (t : ℝ) (q : SpatialTorus) : ℂ :=
  UnitAddTorus.mFourier (-k) q *
    ((nu • Δ (fun y ↦ velocity y t) (euclideanRepresentative q) -
        gradient (fun y ↦ pressure y t) (euclideanRepresentative q) -
        fderiv ℝ (fun y ↦ velocity y t) (euclideanRepresentative q)
          (velocity (euclideanRepresentative q) t)) component : ℂ)

/-- The exact normalized-Haar coefficient of the complete unforced momentum right-hand side. -/
def unforcedMomentumModeComponent
    (nu : ℝ) (velocity : VelocityField) (pressure : PressureField)
    (k : SpatialFrequency) (component : Fin 3) (t : ℝ) : ℂ :=
  ∫ q : SpatialTorus,
    unforcedMomentumModeIntegrand nu velocity pressure k component t q

/-- The actual pointwise momentum owner identifies the time-jet coefficient with the complete
viscous-minus-pressure-minus-advection coefficient. -/
theorem openPeriodicSolutionOn_eulerianTimeJetMode_eq_unforcedMomentumMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) (component : Fin 3) :
    (∫ q : SpatialTorus, eulerianTimeJetModeIntegrand velocity k component t q) =
      unforcedMomentumModeComponent nu velocity pressure k component t := by
  apply integral_congr_ae
  filter_upwards [] with q
  have hm := openPeriodicSolutionOn_unforced_vector_momentum
    solution ht (euclideanRepresentative q)
  have htime :
      eulerianTimeJet velocity (euclideanRepresentative q) t =
        nu • Δ (fun y ↦ velocity y t) (euclideanRepresentative q) -
          gradient (fun y ↦ pressure y t) (euclideanRepresentative q) -
          fderiv ℝ (fun y ↦ velocity y t) (euclideanRepresentative q)
            (velocity (euclideanRepresentative q) t) := by
    calc
      eulerianTimeJet velocity (euclideanRepresentative q) t =
          (eulerianTimeJet velocity (euclideanRepresentative q) t +
            fderiv ℝ (fun y ↦ velocity y t) (euclideanRepresentative q)
              (velocity (euclideanRepresentative q) t)) -
            fderiv ℝ (fun y ↦ velocity y t) (euclideanRepresentative q)
              (velocity (euclideanRepresentative q) t) := by abel
      _ = (nu • Δ (fun y ↦ velocity y t) (euclideanRepresentative q) -
            gradient (fun y ↦ pressure y t) (euclideanRepresentative q)) -
          fderiv ℝ (fun y ↦ velocity y t) (euclideanRepresentative q)
            (velocity (euclideanRepresentative q) t) := by rw [hm]
  rw [eulerianTimeJetModeIntegrand, unforcedMomentumModeIntegrand]
  congr 1
  exact_mod_cast congrArg (fun v : Space ↦ v component) htime

/-- **Exact unforced velocity-mode ODE.**  Every component of every genuine-torus velocity mode
has derivative equal to the Fourier coefficient of the actual strong pointwise momentum return.
No spectral PDE has been postulated, and the pressure term remains visible. -/
theorem openPeriodicSolutionOn_hasDerivAt_velocityModeComponent_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) (component : Fin 3) :
    HasDerivAt (velocityModeComponent velocity k component)
      (unforcedMomentumModeComponent nu velocity pressure k component t) t := by
  have hderiv :=
    openPeriodicSolutionOn_hasDerivAt_velocityModeComponent solution ht k component
  rw [openPeriodicSolutionOn_eulerianTimeJetMode_eq_unforcedMomentumMode
    solution ht k component] at hderiv
  exact hderiv

/-- The complete velocity mode as a real-time vector-valued function. -/
def velocityMode
    (velocity : VelocityField) (k : SpatialFrequency) (t : ℝ) : ComplexVector :=
  fun component ↦ velocityModeComponent velocity k component t

/-- The complete Fourier coefficient of the unforced momentum return. -/
def unforcedMomentumMode
    (nu : ℝ) (velocity : VelocityField) (pressure : PressureField)
    (k : SpatialFrequency) (t : ℝ) : ComplexVector :=
  fun component ↦ unforcedMomentumModeComponent nu velocity pressure k component t

/-- Vector packaging of the exact componentwise unforced mode ODE. -/
theorem openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (velocityMode velocity k)
      (unforcedMomentumMode nu velocity pressure k t) t := by
  rw [hasDerivAt_pi]
  intro component
  exact openPeriodicSolutionOn_hasDerivAt_velocityModeComponent_unforced
    solution ht k component

/-- The already-proved frequency-curl multiplier, bundled as a complex continuous-linear map. -/
def frequencyCurlMultiplierCLM (k : SpatialFrequency) :
    ComplexVector →L[ℂ] ComplexVector :=
  (2 * (Real.pi : ℂ) * Complex.I) •
    LinearMap.toContinuousLinearMap (crossProduct (complexFrequencyVector k))

@[simp]
theorem frequencyCurlMultiplierCLM_apply
    (k : SpatialFrequency) (mode : ComplexVector) :
    frequencyCurlMultiplierCLM k mode = frequencyCurlMultiplier k mode := rfl

/-- The same multiplier regarded as a real continuous-linear receiver for real-time
differentiation. -/
def frequencyCurlMultiplierRealCLM (k : SpatialFrequency) :
    ComplexVector →L[ℝ] ComplexVector :=
  (frequencyCurlMultiplierCLM k).restrictScalars ℝ

@[simp]
theorem frequencyCurlMultiplierRealCLM_apply
    (k : SpatialFrequency) (mode : ComplexVector) :
    frequencyCurlMultiplierRealCLM k mode = frequencyCurlMultiplier k mode := rfl

/-- At every admitted time the frequency curl of the unbundled velocity coefficient is exactly
the established Fourier coefficient of the actual vorticity. -/
theorem frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    frequencyCurlMultiplier k (velocityMode velocity k t.1) =
      openPeriodicVorticityFourierMode solution t k := by
  rw [openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier]
  congr 1
  ext component
  exact velocityModeComponent_eq_openPeriodicVelocityFourierMode
    solution t k component

/-- The divergence-free hypothesis carried by the open periodic solution gives the explicit
longitudinal constraint on the coefficient used in the mode ODE. -/
theorem openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k) (velocityMode velocity k t.1) = 0 := by
  have hmode :
      velocityMode velocity k t.1 =
        openPeriodicVelocityFourierMode solution t k := by
    ext component
    exact velocityModeComponent_eq_openPeriodicVelocityFourierMode
      solution t k component
  rw [hmode]
  exact complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩)
    k

/-- **Exact vorticity-mode ODE obtained from the actual velocity mode.**  The left side is the
established Fourier coefficient of actual vorticity at every strict-interior time.  The right side
is the frequency curl of the complete momentum coefficient; hence no pressure cancellation is
silently assumed in this theorem. -/
theorem openPeriodicSolutionOn_hasDerivAt_frequencyCurlVelocityMode_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (k : SpatialFrequency) :
    HasDerivAt (fun τ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
      (frequencyCurlMultiplier k
        (unforcedMomentumMode nu velocity pressure k t)) t := by
  have hvelocity :=
    openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced solution ht k
  have hcurl := (frequencyCurlMultiplierRealCLM k).hasFDerivAt.comp_hasDerivAt
    t hvelocity
  change HasDerivAt
    (fun τ ↦ frequencyCurlMultiplier k (velocityMode velocity k τ))
    (frequencyCurlMultiplier k
      (unforcedMomentumMode nu velocity pressure k t)) t at hcurl
  exact hcurl

section Audit

#print axioms openPeriodicSolutionOn_hasDerivAt_velocity_time
#print axioms openPeriodicSolutionOn_eulerianTimeJet_isOnePeriodic
#print axioms torusVelocityWorldTube
#print axioms torusEulerianTimeJetWorldTube
#print axioms openPeriodicSolutionOn_hasDerivAt_velocityModeComponent
#print axioms openPeriodicSolutionOn_hasDerivAt_velocityModeComponent_unforced
#print axioms openPeriodicSolutionOn_hasDerivAt_velocityMode_unforced
#print axioms openPeriodicSolutionOn_complexDot_velocityMode_eq_zero
#print axioms openPeriodicSolutionOn_hasDerivAt_frequencyCurlVelocityMode_unforced

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution

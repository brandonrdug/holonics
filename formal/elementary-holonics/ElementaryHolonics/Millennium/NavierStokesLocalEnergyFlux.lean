import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy
import ElementaryHolonics.Millennium.NavierStokesDynamicRescaling
import ElementaryHolonics.Millennium.NavierStokesStationaryRescalingExclusion

/-!
# Local kinetic energy retains pressure, viscous and moving-frame flux

The source's global energy cancellation cannot be reused on a local concentrating core without
its spatial flux. This owner first constructs that flux from the actual velocity and pressure.
The moving-frame energy law then retains dilation and centre transport as flux, with the
amplitude/dilation production read from the same source momentum equation.
-/

noncomputable section

open ContDiff Set Filter InnerProductSpace MeasureTheory
open scoped BigOperators Laplacian Topology

namespace Soma.Holonics.Millennium.NavierStokesLocalEnergyFlux

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesDynamicRescaling

theorem divergence_add (u v : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y ↦ u y + v y) x = divergence u x + divergence v x := by
  unfold divergence
  rw [fderiv_fun_add hu hv]
  exact LinearMap.map_add _ _ _

theorem divergence_sub (u v : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y ↦ u y - v y) x = divergence u x - divergence v x := by
  unfold divergence
  rw [fderiv_fun_sub hu hv]
  exact LinearMap.map_sub _ _ _

theorem divergence_const_smul (c : ℝ) (u : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    divergence (fun y ↦ c • u y) x = c * divergence u x := by
  unfold divergence
  rw [fderiv_fun_const_smul hu c]
  exact LinearMap.map_smul _ _ _

theorem divergence_finite_sum {ι : Type*} (S : Finset ι) (u : ι → InitialVelocity) (x : Space)
    (hu : ∀ i ∈ S, DifferentiableAt ℝ (u i) x) :
    divergence (fun y ↦ ∑ i ∈ S, u i y) x = ∑ i ∈ S, divergence (u i) x := by
  unfold divergence
  rw [fderiv_fun_sum hu, ContinuousLinearMap.toLinearMap_sum]
  exact map_sum _ _ _

def viscousEnergyFlux (u : InitialVelocity) : InitialVelocity :=
  fun x ↦ ∑ i : Fin 3, u x i • gradient (fun y ↦ u y i) x

def energyDissipationDensity (u : InitialVelocity) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖gradient (fun y ↦ u y i) x‖ ^ 2

theorem viscousEnergyFlux_contDiff_one (u : InitialVelocity) (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (viscousEnergyFlux u) := by
  apply ContDiff.sum
  intro i _hi
  have hc : ContDiff ℝ 2 (fun y ↦ u y i) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  exact (hc.of_le (by norm_num)).smul (gradient_contDiff_one _ hc)

theorem energyDissipationDensity_continuous (u : InitialVelocity) (hu : ContDiff ℝ 2 u) :
    Continuous (energyDissipationDensity u) := by
  apply continuous_finsetSum
  intro i _hi
  have hc : ContDiff ℝ 2 (fun y ↦ u y i) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  exact ((gradient_contDiff_one _ hc).continuous.norm).pow 2

theorem divergence_viscousEnergyFlux (u : InitialVelocity) (hu : ContDiff ℝ 2 u) (x : Space) :
    divergence (viscousEnergyFlux u) x =
      inner ℝ (Δ u x) (u x) + energyDissipationDensity u x := by
  have hc (i : Fin 3) : ContDiff ℝ 2 (fun y ↦ u y i) := by
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp hu
  have hgrad (i : Fin 3) : ContDiff ℝ 1 (gradient (fun y ↦ u y i)) :=
    gradient_contDiff_one _ (hc i)
  unfold viscousEnergyFlux
  rw [divergence_finite_sum]
  · have hlap (i : Fin 3) : Δ (fun y ↦ u y i) x = (Δ u x) i := by
      simpa [Function.comp_def] using
        (hu.contDiffAt (x := x)).laplacian_CLM_comp_left (l := EuclideanSpace.proj i)
    simp_rw [divergence_pressureFlux _ _ x
      ((hgrad _).differentiable (by norm_num) x) ((hc _).differentiable (by norm_num) x),
      real_inner_self_eq_norm_sq, divergence_gradient_eq_laplacian _ (hc _) x, hlap]
    simp [Finset.sum_add_distrib, energyDissipationDensity, PiLp.inner_apply, add_comm]
  · intro i _hi
    exact ((hc i).differentiable (by norm_num) x).smul
      ((hgrad i).differentiable (by norm_num) x)

/-- The velocity transporting energy relative to the moving chart. -/
def relativeTransport (dilation : ℝ) (translation : Space) (u : InitialVelocity) : InitialVelocity :=
  fun y ↦ u y - dilation • y - translation

theorem relativeTransport_differentiableAt (dilation : ℝ) (translation : Space)
    (u : InitialVelocity) (x : Space) (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ (relativeTransport dilation translation u) x :=
  (hu.sub (differentiableAt_id.const_smul dilation)).sub_const translation

theorem divergence_relativeTransport (dilation : ℝ) (translation : Space)
    (u : InitialVelocity) (x : Space) (hu : DifferentiableAt ℝ u x) :
    divergence (relativeTransport dilation translation u) x = divergence u x - 3 * dilation := by
  unfold relativeTransport
  rw [divergence_sub (fun y ↦ u y - dilation • y) (fun _ ↦ translation) x
    (hu.sub (differentiableAt_id.const_smul dilation))
    (differentiableAt_const translation),
    divergence_sub u (fun y ↦ dilation • y) x hu (differentiableAt_id.const_smul dilation),
    divergence_const_smul dilation (fun y : Space ↦ y) x differentiableAt_id]
  simp [divergence, LinearMap.trace_id]
  ring

/-- Pressure work remains in the local flux; its cancellation requires the actual boundary return. -/
def movingEnergyFlux (mu dilation : ℝ) (translation : Space)
    (u : InitialVelocity) (p : Space → ℝ) : InitialVelocity :=
  fun y ↦ kineticEnergyDensity u y • relativeTransport dilation translation u y
    + p y • u y - mu • viscousEnergyFlux u y

theorem movingEnergyFlux_contDiff_one (mu dilation : ℝ) (translation : Space)
    (u : InitialVelocity) (p : Space → ℝ) (hu : ContDiff ℝ 2 u) (hp : ContDiff ℝ 1 p) :
    ContDiff ℝ 1 (movingEnergyFlux mu dilation translation u p) := by
  have hu' : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have he : ContDiff ℝ 1 (kineticEnergyDensity u) :=
    contDiff_const.mul (hu'.norm_sq ℝ)
  have ht : ContDiff ℝ 1 (relativeTransport dilation translation u) :=
    (hu'.sub (contDiff_id.const_smul dilation)).sub contDiff_const
  convert ((he.smul ht).add (hp.smul hu')).sub
    ((viscousEnergyFlux_contDiff_one u hu).const_smul mu) using 1 <;> rfl

theorem divergence_movingEnergyFlux (mu dilation : ℝ) (translation : Space)
    (u : InitialVelocity) (p : Space → ℝ) (hu : ContDiff ℝ 2 u) (hp : ContDiff ℝ 1 p)
    (x : Space) (hdiv : divergence u x = 0) :
    divergence (movingEnergyFlux mu dilation translation u p) x =
      inner ℝ (fderiv ℝ u x (relativeTransport dilation translation u x)) (u x)
        - 3 * dilation * kineticEnergyDensity u x
        + inner ℝ (gradient p x) (u x)
        - mu * (inner ℝ (Δ u x) (u x) + energyDissipationDensity u x) := by
  have hu' := hu.differentiable (by norm_num) x
  have hp' := hp.differentiable (by norm_num) x
  have he : DifferentiableAt ℝ (kineticEnergyDensity u) x :=
    (hu'.norm_sq ℝ).const_mul (1 / 2 : ℝ)
  have ht := relativeTransport_differentiableAt dilation translation u x hu'
  have hv := (viscousEnergyFlux_contDiff_one u hu).differentiable (by norm_num) x
  unfold movingEnergyFlux
  rw [divergence_sub
    (fun y ↦ kineticEnergyDensity u y • relativeTransport dilation translation u y + p y • u y)
    (fun y ↦ mu • viscousEnergyFlux u y) x
    ((he.smul ht).add (hp'.smul hu')) (hv.const_smul mu),
    divergence_add (fun y ↦ kineticEnergyDensity u y • relativeTransport dilation translation u y)
      (fun y ↦ p y • u y) x (he.smul ht) (hp'.smul hu'),
    divergence_const_smul _ _ x hv,
    divergence_kineticEnergyFlux_direction _ _ x ht hu',
    divergence_pressureFlux _ _ x hu' hp',
    divergence_relativeTransport _ _ _ _ hu', hdiv,
    divergence_viscousEnergyFlux _ hu x]
  ring

/-- Local kinetic-energy work retains all relative transport and viscous gradient components. -/
theorem localEnergyBalance_of_momentum
    (mu dilation amplitudeRate : ℝ) (translation : Space)
    (u : InitialVelocity) (p : Space → ℝ) (hu : ContDiff ℝ 2 u) (hp : ContDiff ℝ 1 p)
    (x timeJet force : Space) (hdiv : divergence u x = 0)
    (hmomentum : timeJet + fderiv ℝ u x (u x) =
      mu • Δ u x - gradient p x + dilation • fderiv ℝ u x x
        + fderiv ℝ u x translation + amplitudeRate • u x + force) :
    inner ℝ timeJet (u x) + divergence (movingEnergyFlux mu dilation translation u p) x =
      (2 * amplitudeRate - 3 * dilation) * kineticEnergyDensity u x
        - mu * energyDissipationDensity u x + inner ℝ force (u x) := by
  have hwork := congrArg (fun v : Space ↦ inner ℝ v (u x)) hmomentum
  simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at hwork
  rw [divergence_movingEnergyFlux mu dilation translation u p hu hp x hdiv]
  simp only [relativeTransport, map_sub, map_smul, inner_sub_left, real_inner_smul_left,
    kineticEnergyDensity]
  nlinarith

theorem hasDerivAt_kineticEnergyDensity_time (velocity : VelocityField) (x : Space)
    {t : ℝ} (ht : DifferentiableAt ℝ (velocity x) t) :
    HasDerivAt (fun r ↦ kineticEnergyDensity (fun y ↦ velocity y r) x)
      (inner ℝ (deriv (velocity x) t) (velocity x t)) t := by
  have h := ht.hasDerivAt.norm_sq.const_mul (1 / 2 : ℝ)
  convert h using 1 <;> first | rfl | simp [real_inner_comm]

theorem rescaledVelocity_slice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (s : ℝ) (ht : clock s ∈ openTimeSlab T) :
    ContDiff ℝ ∞ (fun y ↦ rescaledVelocity centre length amplitude clock velocity y s) := by
  have hsource := OpenSmoothSolutionOn.velocitySlice_contDiff solution ht
  have hmap : ContDiff ℝ ∞ (fun y : Space ↦ centre s + length s • y) :=
    contDiff_const.add (contDiff_id.const_smul (length s))
  convert (hsource.comp hmap).const_smul (amplitude s) using 1 <;> rfl

/-- The local moving energy law is read from MFR1's actual rescaled momentum, rather than
postulated for a normalized profile. Periodicity is not required for this pointwise source law. -/
theorem OpenSmoothSolutionOn.rescaled_localEnergyBalance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (y : Space) (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet : ℝ)
    (ht : clock s ∈ Ioo 0 T)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock (length s * amplitude s) s)
    (hq : amplitude s ≠ 0) (hell : length s ≠ 0) :
    let U := rescaledVelocity centre length amplitude clock velocity
    let P := rescaledPressure centre length amplitude clock pressure
    let mu := nu * amplitude s / length s
    let dilation := lengthJet / length s
    let translation := (length s)⁻¹ • centreJet
    deriv (fun r ↦ kineticEnergyDensity (fun z ↦ U z r) y) s
      + divergence (movingEnergyFlux mu dilation translation (fun z ↦ U z s) (fun z ↦ P z s)) y =
      (2 * (amplitudeJet / amplitude s) - 3 * dilation) * kineticEnergyDensity (fun z ↦ U z s) y
        - mu * energyDissipationDensity (fun z ↦ U z s) y
        + inner ℝ ((length s * amplitude s ^ 2) • force (centre s + length s • y) (clock s))
          (U y s) := by
  dsimp only
  let U := rescaledVelocity centre length amplitude clock velocity
  let P := rescaledPressure centre length amplitude clock pressure
  have hu : ContDiff ℝ 2 (fun z ↦ U z s) :=
    (rescaledVelocity_slice_contDiff solution centre length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hp : ContDiff ℝ 1 (fun z ↦ P z s) :=
    (NavierStokesStationaryRescalingExclusion.rescaledPressure_slice_contDiff solution centre
      length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le (by simp)
  have hjet := Soma.Holonics.Millennium.NavierStokesDynamicRescaling.hasDerivAt_rescaledVelocity
    velocity centre length amplitude clock y s centreJet lengthJet amplitudeJet
    (length s * amplitude s) (OpenSmoothSolutionOn.joint_differentiableAt solution _ ht)
    hcentre hlength hamplitude hclock
  rw [(hasDerivAt_kineticEnergyDensity_time U y hjet.differentiableAt).deriv]
  apply localEnergyBalance_of_momentum _ _ _ _ (fun z ↦ U z s) (fun z ↦ P z s) hu hp
    y (deriv (U y) s) _
    (OpenSmoothSolutionOn.rescaled_incompressible solution centre length amplitude clock y s
      ⟨ht.1.le, ht.2⟩)
  simpa only [map_smul] using
    OpenSmoothSolutionOn.rescaled_momentum solution centre length amplitude clock y s centreJet
      lengthJet amplitudeJet ht hcentre hlength hamplitude hclock hq hell

/-- A spatially selective energy receiver retains the work crossing its selection gradient.
The pressure term is inside the same complete flux as advection and viscosity. -/
theorem OpenSmoothSolutionOn.rescaled_cutoffEnergyBalance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial force velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (chi : Space → ℝ) (hchi : ContDiff ℝ 1 chi)
    (y : Space) (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet : ℝ)
    (ht : clock s ∈ Ioo 0 T)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock (length s * amplitude s) s)
    (hq : amplitude s ≠ 0) (hell : length s ≠ 0) :
    let U := rescaledVelocity centre length amplitude clock velocity
    let P := rescaledPressure centre length amplitude clock pressure
    let mu := nu * amplitude s / length s
    let dilation := lengthJet / length s
    let translation := (length s)⁻¹ • centreJet
    let J := movingEnergyFlux mu dilation translation (fun z ↦ U z s) (fun z ↦ P z s)
    chi y * deriv (fun r ↦ kineticEnergyDensity (fun z ↦ U z r) y) s
      + divergence (fun z ↦ chi z • J z) y =
      chi y * ((2 * (amplitudeJet / amplitude s) - 3 * dilation) *
          kineticEnergyDensity (fun z ↦ U z s) y - mu * energyDissipationDensity (fun z ↦ U z s) y
        + inner ℝ ((length s * amplitude s ^ 2) • force (centre s + length s • y) (clock s)) (U y s))
      + inner ℝ (gradient chi y) (J y) := by
  dsimp only
  let U := rescaledVelocity centre length amplitude clock velocity
  let P := rescaledPressure centre length amplitude clock pressure
  let J := movingEnergyFlux (nu * amplitude s / length s) (lengthJet / length s)
    ((length s)⁻¹ • centreJet) (fun z ↦ U z s) (fun z ↦ P z s)
  have hu : ContDiff ℝ 2 (fun z ↦ U z s) :=
    (rescaledVelocity_slice_contDiff solution centre length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hp : ContDiff ℝ 1 (fun z ↦ P z s) :=
    (NavierStokesStationaryRescalingExclusion.rescaledPressure_slice_contDiff solution centre
      length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le (by simp)
  have hJ : ContDiff ℝ 1 J := movingEnergyFlux_contDiff_one _ _ _ _ _ hu hp
  have hb := OpenSmoothSolutionOn.rescaled_localEnergyBalance solution centre length amplitude clock
    y s centreJet lengthJet amplitudeJet ht hcentre hlength hamplitude hclock hq hell
  rw [divergence_pressureFlux J chi y
    (hJ.differentiable (by norm_num) y) (hchi.differentiable (by norm_num) y)]
  dsimp only at hb
  nlinarith [congrArg (fun r : ℝ ↦ chi y * r) hb]

/-- The local balance supplies integrability of its rate as well as the integrated equality.
No cancellation of flux at the observer's boundary is assumed. -/
theorem integrableOn_and_integral_localBalance
    (rate production : Space → ℝ) (J : InitialVelocity)
    (hproduction : Continuous production) (hJ : ContDiff ℝ 1 J)
    (hbalance : ∀ x, rate x + divergence J x = production x) :
    IntegrableOn rate unitCube ∧
      (∫ x in unitCube, rate x) + (∫ x in unitCube, divergence J x) =
        ∫ x in unitCube, production x := by
  have hcube : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hpi : IntegrableOn production unitCube :=
    hproduction.continuousOn.integrableOn_compact hcube
  have hdi : IntegrableOn (divergence J) unitCube :=
    (divergence_continuous_of_contDiff_one J hJ).continuousOn.integrableOn_compact hcube
  have hr : rate = fun x ↦ production x - divergence J x :=
    funext fun x ↦ (eq_sub_iff_add_eq).mpr (hbalance x)
  rw [hr]
  refine ⟨hpi.sub hdi, ?_⟩
  rw [integral_sub hpi hdi]
  ring

/-- The source-bound weighted energy rate over a declared fixed local chart cube.
This cube is an observer aperture; it is not silently identified with the changing periodic cell.
The complete oriented boundary current and the selection-gradient work both remain in the return. -/
theorem OpenSmoothSolutionOn.rescaled_cutoffEnergyIntegral_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenSmoothSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (centre : ℝ → Space) (length amplitude clock : ℝ → ℝ)
    (chi : Space → ℝ) (hchi : ContDiff ℝ 2 chi)
    (s : ℝ) (centreJet : Space) (lengthJet amplitudeJet : ℝ)
    (ht : clock s ∈ Ioo 0 T)
    (hcentre : HasDerivAt centre centreJet s)
    (hlength : HasDerivAt length lengthJet s)
    (hamplitude : HasDerivAt amplitude amplitudeJet s)
    (hclock : HasDerivAt clock (length s * amplitude s) s)
    (hq : amplitude s ≠ 0) (hell : length s ≠ 0) :
    let U := rescaledVelocity centre length amplitude clock velocity
    let P := rescaledPressure centre length amplitude clock pressure
    let mu := nu * amplitude s / length s
    let dilation := lengthJet / length s
    let translation := (length s)⁻¹ • centreJet
    let J := movingEnergyFlux mu dilation translation (fun z ↦ U z s) (fun z ↦ P z s)
    let rate := fun y ↦ chi y * deriv (fun r ↦ kineticEnergyDensity (fun z ↦ U z r) y) s
    let production := fun y ↦ (2 * (amplitudeJet / amplitude s) - 3 * dilation) *
      kineticEnergyDensity (fun z ↦ U z s) y - mu * energyDissipationDensity (fun z ↦ U z s) y
    IntegrableOn rate unitCube ∧
      (∫ y in unitCube, rate y) + unitCubeBoundaryFlux (fun z ↦ chi z • J z) =
        (∫ y in unitCube, chi y * production y) +
          ∫ y in unitCube, inner ℝ (gradient chi y) (J y) := by
  dsimp only
  let U := rescaledVelocity centre length amplitude clock velocity
  let P := rescaledPressure centre length amplitude clock pressure
  let J := movingEnergyFlux (nu * amplitude s / length s) (lengthJet / length s)
    ((length s)⁻¹ • centreJet) (fun z ↦ U z s) (fun z ↦ P z s)
  let production := fun y ↦ (2 * (amplitudeJet / amplitude s) - 3 * (lengthJet / length s)) *
    kineticEnergyDensity (fun z ↦ U z s) y -
      (nu * amplitude s / length s) * energyDissipationDensity (fun z ↦ U z s) y
  have hu : ContDiff ℝ 2 (fun z ↦ U z s) :=
    (rescaledVelocity_slice_contDiff solution centre length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hp : ContDiff ℝ 1 (fun z ↦ P z s) :=
    (NavierStokesStationaryRescalingExclusion.rescaledPressure_slice_contDiff solution centre
      length amplitude clock s ⟨ht.1.le, ht.2⟩).of_le (by simp)
  have hJ : ContDiff ℝ 1 J := movingEnergyFlux_contDiff_one _ _ _ _ _ hu hp
  have he : Continuous (kineticEnergyDensity (fun z ↦ U z s)) :=
    continuous_const.mul ((hu.norm_sq ℝ).continuous)
  have hd := energyDissipationDensity_continuous _ hu
  have hprod : Continuous production :=
    (continuous_const.mul he).sub (continuous_const.mul hd)
  have hselected := hchi.continuous.mul hprod
  have hwork : Continuous (fun y ↦ inner ℝ (gradient chi y) (J y)) :=
    (gradient_contDiff_one chi hchi).continuous.inner hJ.continuous
  have hselectedFlux : ContDiff ℝ 1 (fun z ↦ chi z • J z) :=
    (hchi.of_le (by norm_num)).smul hJ
  have hb (y : Space) := OpenSmoothSolutionOn.rescaled_cutoffEnergyBalance solution
    centre length amplitude clock chi (hchi.of_le (by norm_num)) y s centreJet lengthJet amplitudeJet
    ht hcentre hlength hamplitude hclock hq hell
  have hbalance : ∀ y,
      chi y * deriv (fun r ↦ kineticEnergyDensity (fun z ↦ U z r) y) s +
        divergence (fun z ↦ chi z • J z) y =
      chi y * production y + inner ℝ (gradient chi y) (J y) := by
    intro y
    simpa only [Pi.zero_apply, smul_zero, inner_zero_left, add_zero] using hb y
  have hint := integrableOn_and_integral_localBalance _ _ _
    (hselected.add hwork) hselectedFlux hbalance
  have hcube : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc
  have hsi : IntegrableOn (fun y ↦ chi y * production y) unitCube :=
    hselected.continuousOn.integrableOn_compact hcube
  have hwi : IntegrableOn (fun y ↦ inner ℝ (gradient chi y) (J y)) unitCube :=
    hwork.continuousOn.integrableOn_compact hcube
  simp only [Pi.add_apply, Pi.mul_apply] at hint
  rw [integral_add hsi hwi] at hint
  rw [integral_divergence_unitCube_eq_boundaryFlux _ hselectedFlux] at hint
  exact hint

#print axioms divergence_viscousEnergyFlux
#print axioms divergence_movingEnergyFlux
#print axioms OpenSmoothSolutionOn.rescaled_localEnergyBalance
#print axioms OpenSmoothSolutionOn.rescaled_cutoffEnergyBalance
#print axioms OpenSmoothSolutionOn.rescaled_cutoffEnergyIntegral_unforced

end Soma.Holonics.Millennium.NavierStokesLocalEnergyFlux

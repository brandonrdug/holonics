import ElementaryHolonics.Millennium.NavierStokesCrossCurrentCalculus
import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import ElementaryHolonics.Millennium.NavierStokesLocalEnergyFlux
import ElementaryHolonics.Millennium.NavierStokesCellCurrentLaw
import ElementaryHolonics.Millennium.NavierStokesPeriodicCubeInterpolation

/-!
# The actual nonlinear velocity-vorticity cross-current

We use C = u × curl u, the negative of the existing omega-cross-u Lamb convention.
The PDE below is derived from the actual finite-lifespan momentum and vorticity equations.
Pressure, stretching, forcing and mixed diffusion remain oriented source terms.
-/
noncomputable section
open ContDiff InnerProductSpace Set MeasureTheory
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesLambCurrentEvolution
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesCrossCurrentCalculus

/-- The oriented nonlinear current of one actual velocity field. -/
def velocityVorticityCurrent (u : InitialVelocity) : InitialVelocity :=
  fun x => cross (u x) (vorticityAt u x)

def velocityVorticityCurrentField (velocity : VelocityField) : VelocityField :=
  fun x t => velocityVorticityCurrent (fun y => velocity y t) x

def mixedDiffusionCurrent (u w : InitialVelocity) (x : Space) : Space :=
  ∑ i : Fin 3, cross (fderiv ℝ u x (EuclideanSpace.basisFun (Fin 3) ℝ i))
    (fderiv ℝ w x (EuclideanSpace.basisFun (Fin 3) ℝ i))

/-- The complete source, with force and curl-force retained separately. -/
def velocityVorticitySource (nu : ℝ) (force velocity : VelocityField)
    (pressure : PressureField) (x : Space) (t : ℝ) : Space :=
  cross (velocity x t)
      (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t)) -
    cross (gradient (fun y => pressure y t) x) (vorticityField velocity x t) +
    cross (force x t) (vorticityField velocity x t) +
    cross (velocity x t) (vorticityField force x t) -
    (2 * nu) • mixedDiffusionCurrent (fun y => velocity y t)
      (fun y => vorticityField velocity y t) x

/-- Spatial smoothness of the current follows from the actual derivative used by curl. -/
theorem velocityVorticityCurrent_contDiff_two (u : InitialVelocity)
    (hu : ContDiff ℝ 3 u) : ContDiff ℝ 2 (velocityVorticityCurrent u) := by
  have hw := vorticityField_contDiff_two (fun x _ => u x) 0 hu
  exact cross_contDiff (hu.of_le (by norm_num)) hw

/-- The actual finite-slab current is jointly smooth on the open slab. -/
theorem smoothSolutionOn_current_contDiffOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (velocityVorticityCurrentField velocity))
      (NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
  have hu := solution.velocitySmooth.mono (show
    NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ⊆ spaceTimeSlab T from by
      rintro ⟨x,t⟩ ⟨hx,ht⟩; exact ⟨hx,ht.1.le,ht.2.le⟩)
  have hw := smoothSolutionOn_vorticityField_contDiffOn_interior solution
  exact (crossBilinear.contDiff.comp_contDiffOn hu).clm_apply hw

/-- The nonlinear current equation uses actual time/space derivatives and actual pressure. -/
theorem smoothSolutionOn_velocityVorticityCurrent_equation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet (velocityVorticityCurrentField velocity) x t +
      fderiv ℝ (fun y => velocityVorticityCurrentField velocity y t) x (velocity x t) =
      nu • Δ (fun y => velocityVorticityCurrentField velocity y t) x +
        velocityVorticitySource nu force velocity pressure x t := by
  have hu : ContDiff ℝ ∞ (fun y => velocity y t) :=
    smoothSolutionOn_velocitySpatialSmooth solution ht0 htT
  have hw : ContDiff ℝ 2 (fun y => vorticityField velocity y t) :=
    vorticityField_contDiff_two velocity t (hu.of_le (WithTop.coe_le_coe.mpr le_top))
  have huj : DifferentiableAt ℝ (Function.uncurry velocity) (x,t) :=
    (contDiffAt_of_contDiffOn_spaceTimeSlab velocity solution.velocitySmooth x ht0 htT).differentiableAt (by simp)
  have hwj : DifferentiableAt ℝ (Function.uncurry (vorticityField velocity)) (x,t) := by
    have hopen : IsOpen (NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) :=
      isOpen_univ.prod isOpen_Ioo
    exact ((smoothSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt
      (hopen.mem_nhds ⟨mem_univ _,ht0,htT⟩)).differentiableAt (by simp)
  have htCross := fderiv_cross_apply huj hwj (0,1)
  change eulerianTimeJet (velocityVorticityCurrentField velocity) x t =
    cross (eulerianTimeJet velocity x t) (vorticityField velocity x t) +
      cross (velocity x t) (eulerianTimeJet (vorticityField velocity) x t) at htCross
  have hxCross := fderiv_cross_apply (hu.differentiable (by simp) x)
    (hw.differentiable (by norm_num) x) (velocity x t)
  change fderiv ℝ (fun y => velocityVorticityCurrentField velocity y t) x (velocity x t) =
    cross (fderiv ℝ (fun y => velocity y t) x (velocity x t)) (vorticityField velocity x t) +
      cross (velocity x t) (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t)) at hxCross
  have hLap := laplacian_cross (fun y => velocity y t) (fun y => vorticityField velocity y t)
    (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hw x
  change Δ (fun y => velocityVorticityCurrentField velocity y t) x =
    cross (Δ (fun y => velocity y t) x) (vorticityField velocity x t) +
      cross (velocity x t) (Δ (fun y => vorticityField velocity y t) x) +
      (2 : ℝ) • mixedDiffusionCurrent (fun y => velocity y t)
        (fun y => vorticityField velocity y t) x at hLap
  have hm := solution.momentum x t ⟨ht0.le,htT.le⟩
  rw [← smoothSolutionOn_eulerianTimeJet_eq_derivWithin solution x ht0 htT] at hm
  have hv := smoothSolutionOn_pointwiseVorticityBalance solution ht0 htT x
  have hmt := eq_sub_of_add_eq hm
  have hvt := eq_sub_of_add_eq hv
  rw [htCross,hxCross,hLap,hmt,hvt]
  simp only [velocityVorticitySource, cross_add_left, cross_add_right,
    cross_sub_left, cross_sub_right, cross_smul_left, cross_smul_right]
  module

/-- An actual open-lifespan solution supplies the same equation without a terminal smoothness
assumption: take a compact interior slab containing the addressed time. -/
theorem openPeriodicSolutionOn_velocityVorticityCurrent_equation
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet (velocityVorticityCurrentField velocity) x t +
      fderiv ℝ (fun y => velocityVorticityCurrentField velocity y t) x (velocity x t) =
      nu • Δ (fun y => velocityVorticityCurrentField velocity y t) x +
        velocityVorticitySource nu force velocity pressure x t := by
  let S := (t+T)/2
  have hS : 0 < S := by dsimp [S]; linarith
  have htS : t < S := by dsimp [S]; linarith
  have hST : S < T := by dsimp [S]; linarith
  exact smoothSolutionOn_velocityVorticityCurrent_equation
    (solution.toClosedInterior hS hST).toSmoothSolutionOn ht0 htS x

/-- The kinetic-energy gradient is the actual transposed velocity derivative. -/
theorem gradient_kineticEnergy_eq_transpose (u : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    gradient (kineticEnergyDensity u) x = transposeAction (velocityJacobianAt u x) (u x) := by
  ext i
  have h := inner_gradient_kineticEnergyDensity_direction
    (fun _ => EuclideanSpace.basisFun (Fin 3) ℝ i) u x hu
  rw [EuclideanSpace.inner_basisFun_real] at h
  rw [h]
  simp [transposeAction,matrixAction_apply,Matrix.transpose_apply,
    velocityJacobianAt,jacobianMatrix_apply,PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The cross-current supplies nonlinear transport after both gradient terms are retained. -/
theorem smoothSolutionOn_rotational_momentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet velocity x t = nu • Δ (fun y => velocity y t) x +
      velocityVorticityCurrentField velocity x t -
      (gradient (fun y => pressure y t) x +
        gradient (kineticEnergyDensity (fun y => velocity y t)) x) + force x t := by
  let u : InitialVelocity := fun y => velocity y t
  have hu := (smoothSolutionOn_velocitySpatialSmooth solution ht0 htT).differentiable (by simp) x
  have hL := lambIdentity_velocityCrossVorticity (velocityJacobianAt u x) (u x)
  rw [velocityJacobianAt, matrixAction_jacobianMatrix] at hL
  change fderiv ℝ u x (u x) = transposeAction (velocityJacobianAt u x) (u x) -
    velocityVorticityCurrent u x at hL
  rw [← gradient_kineticEnergy_eq_transpose u x hu] at hL
  have hm := solution.momentum x t ⟨ht0.le,htT.le⟩
  rw [← smoothSolutionOn_eulerianTimeJet_eq_derivWithin solution x ht0 htT] at hm
  change eulerianTimeJet velocity x t + fderiv ℝ u x (u x) = _ at hm
  rw [hL] at hm
  dsimp [u] at hm
  unfold velocityVorticityCurrentField
  rw [eq_sub_of_add_eq hm]
  module

/-- Advective and diffusive transport of one component of the same current. -/
def currentComponentFlux (nu : ℝ) (velocity : VelocityField)
    (t : ℝ) (i : Fin 3) : InitialVelocity := fun x =>
  velocityVorticityCurrentField velocity x t i • velocity x t -
    nu • gradient (fun y => velocityVorticityCurrentField velocity y t i) x

theorem currentComponentFlux_contDiff_one (nu : ℝ) (velocity : VelocityField)
    (t : ℝ) (i : Fin 3) (hu : ContDiff ℝ 3 (fun y => velocity y t)) :
    ContDiff ℝ 1 (currentComponentFlux nu velocity t i) := by
  have hC := velocityVorticityCurrent_contDiff_two (fun y => velocity y t) hu
  have hc : ContDiff ℝ 2 (fun y => velocityVorticityCurrentField velocity y t i) :=
    by
      convert ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hC) using 1 <;> rfl
  exact ((hc.of_le (by norm_num)).smul (hu.of_le (by norm_num))).sub
    ((gradient_contDiff_one _ hc).const_smul nu)

/-- The local divergence form carries the outward component flux, not a zero-boundary assumption. -/
theorem smoothSolutionOn_current_component_balance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) (i : Fin 3) :
    eulerianTimeJet (velocityVorticityCurrentField velocity) x t i +
      divergence (currentComponentFlux nu velocity t i) x =
        velocityVorticitySource nu force velocity pressure x t i := by
  have hu := smoothSolutionOn_velocitySpatialSmooth solution ht0 htT
  have hC := velocityVorticityCurrent_contDiff_two (fun y => velocity y t)
    (hu.of_le (WithTop.coe_le_coe.mpr le_top))
  have hc : ContDiff ℝ 2 (fun y => velocityVorticityCurrentField velocity y t i) :=
    by
      convert ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hC) using 1 <;> rfl
  have hg := gradient_contDiff_one _ hc
  have hflux : DifferentiableAt ℝ
      (fun y => velocityVorticityCurrentField velocity y t i • velocity y t) x := by
    convert (hc.differentiable (by norm_num) x).smul (hu.differentiable (by simp) x) using 1 <;> rfl
  have hdiffusion : DifferentiableAt ℝ
      (fun y => nu • gradient (fun z => velocityVorticityCurrentField velocity z t i) y) x := by
    convert (hg.differentiable (by norm_num) x).const_smul nu using 1 <;> rfl
  have hdiv : divergence (currentComponentFlux nu velocity t i) x =
      divergence (fun y => velocityVorticityCurrentField velocity y t i • velocity y t) x -
      divergence (fun y => nu • gradient (fun z => velocityVorticityCurrentField velocity z t i) y) x := by
    convert NavierStokesLocalEnergyFlux.divergence_sub _ _ x hflux hdiffusion using 1 <;> rfl
  rw [hdiv,
    divergence_pressureFlux _ _ x (hu.differentiable (by simp) x) (hc.differentiable (by norm_num) x),
    NavierStokesLocalEnergyFlux.divergence_const_smul nu _ x (hg.differentiable (by norm_num) x),
    divergence_gradient_eq_laplacian _ hc x,
    solution.incompressible x t ⟨ht0.le,htT.le⟩, mul_zero, add_zero,
    inner_gradient_left]
  have hcomponent : fderiv ℝ
      (fun y => velocityVorticityCurrentField velocity y t i) x (velocity x t) =
      (fderiv ℝ (fun y => velocityVorticityCurrentField velocity y t) x (velocity x t)) i := by
    convert NavierStokesPeriodicCubeInterpolation.fderiv_component_apply _
      (hC.of_le (by norm_num)) x (velocity x t) i using 1 <;> rfl
  rw [hcomponent]
  have hlap := (hC.contDiffAt (x := x)).laplacian_CLM_comp_left (l := (EuclideanSpace.proj i : Space →L[ℝ] ℝ))
  change Δ (fun y => velocityVorticityCurrentField velocity y t i) x =
    (Δ (fun y => velocityVorticityCurrentField velocity y t) x) i at hlap
  rw [hlap]
  have h := congrArg (fun v : Space => v i)
    (smoothSolutionOn_velocityVorticityCurrent_equation solution ht0 htT x)
  simp only [PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] at h
  linarith

/-- Curl retains both parts of a genuinely differentiable field decomposition. -/
theorem vorticityAt_add (v w : InitialVelocity) (x : Space)
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w x) :
    vorticityAt (fun y => v y + w y) x = vorticityAt v x + vorticityAt w x := by
  change derivativeCurlLinearMap (fderiv ℝ (fun y => v y + w y) x) = _
  rw [fderiv_fun_add hv hw, map_add]
  rfl

/-- The complete resolved/remainder current includes both ordered cross terms. -/
theorem velocityVorticityCurrent_add (v w : InitialVelocity) (x : Space)
    (hv : DifferentiableAt ℝ v x) (hw : DifferentiableAt ℝ w x) :
    velocityVorticityCurrent (fun y => v y + w y) x =
      velocityVorticityCurrent v x + cross (v x) (vorticityAt w x) +
        cross (w x) (vorticityAt v x) + velocityVorticityCurrent w x := by
  simp only [velocityVorticityCurrent, vorticityAt_add v w x hv hw,
    cross_add_left,cross_add_right]
  abel

/-- The three fluid axes are a section of the existing four-axis current receiver. -/
def fluidCurrentAxes (u : Space) : HolonicEntropyActionInduction.FourTorusEntropyCurrent ℝ :=
  ![u 0,u 1,u 2,0]

theorem velocityVorticityCurrent_entropy_receiver (u : InitialVelocity) (x : Space) :
    HolonicEntropyActionInduction.entropyAxisCrossCurrent
      (fluidCurrentAxes (u x)) (fluidCurrentAxes (vorticityAt u x)) 0 1 =
        velocityVorticityCurrent u x 2 := by
  simp [HolonicEntropyActionInduction.entropyAxisCrossCurrent,fluidCurrentAxes,
    velocityVorticityCurrent,cross,crossProduct]

theorem velocityVorticityCurrent_complex_receiver (u : InitialVelocity) (x : Space) :
    velocityVorticityCurrent u x 2 =
      (star (HolonicEntropyHeatCurrent.complexPlaneFace (fluidCurrentAxes (u x))) *
        HolonicEntropyHeatCurrent.complexPlaneFace (fluidCurrentAxes (vorticityAt u x))).im := by
  rw [← velocityVorticityCurrent_entropy_receiver]
  exact HolonicEntropyHeatCurrent.entropyAxisCrossCurrent_eq_complex_pairing _ _

#print axioms smoothSolutionOn_rotational_momentum
#print axioms smoothSolutionOn_current_component_balance
#print axioms smoothSolutionOn_velocityVorticityCurrent_equation
#print axioms openPeriodicSolutionOn_velocityVorticityCurrent_equation
#print axioms velocityVorticityCurrent_add
#print axioms velocityVorticityCurrent_complex_receiver
end Soma.Holonics.Millennium.NavierStokesLambCurrentEvolution

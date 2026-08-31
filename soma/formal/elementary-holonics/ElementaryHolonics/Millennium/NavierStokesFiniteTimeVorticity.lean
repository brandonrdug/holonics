import ElementaryHolonics.Millennium.NavierStokesFiniteTime
import ElementaryHolonics.Millennium.NavierStokesCurlCommutation

/-!
# Finite-time periodic vorticity

The global `PeriodicSolution` carrier already assumes a world-tube on every nonnegative time.
This module instead works on the actual bounded slab `Icc 0 T`.  At every interior event
`0 < t < T`, joint smoothness supplies the same space--time curl commutation, pressure-kernel,
and nonlinear stretching identities as in the global development.  The resulting pointwise
vorticity equation therefore belongs to the finite carrier and does not assume global existence.

Periodic integration is carried by `NavierStokesFiniteTimeEnstrophy`; conditional control and the
terminal continuation fibre are carried by `NavierStokesFiniteTimeContinuation`.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- A finite smooth solution carrying the spatial return data needed on the torus chart. -/
structure PeriodicSolutionOn
    (T nu : ℝ) (initial : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop
    extends SmoothSolutionOn T nu initial force velocity pressure where
  velocityPeriodic : ∀ t ∈ timeSlab T, IsOnePeriodic (fun x => velocity x t)
  pressurePeriodic : ∀ t ∈ timeSlab T, IsOnePeriodic (fun x => pressure x t)

/-- Every global periodic solution restricts to a genuine finite periodic carrier. -/
def PeriodicSolution.toPeriodicSolutionOn
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    {T : ℝ} (hT : 0 < T) :
    PeriodicSolutionOn T nu initial force velocity pressure where
  toSmoothSolutionOn :=
    Soma.Holonics.Millennium.NavierStokesFiniteTime.SmoothSolution.toSmoothSolutionOn
      solution.toSmoothSolution hT
  velocityPeriodic t ht := solution.velocityPeriodic t ht.1
  pressurePeriodic t ht := solution.pressurePeriodic t ht.1

/-- Restriction preserves the complete finite periodic carrier. -/
def PeriodicSolutionOn.restrict
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {S : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    PeriodicSolutionOn S nu initial force velocity pressure where
  toSmoothSolutionOn := solution.toSmoothSolutionOn.restrict hS hST
  velocityPeriodic t ht := solution.velocityPeriodic t (timeSlab_mono hST ht)
  pressurePeriodic t ht := solution.pressurePeriodic t (timeSlab_mono hST ht)

/-- The open interior of the bounded space--time slab. -/
def openSpaceTimeSlab (T : ℝ) : Set (Space × ℝ) := Set.univ ×ˢ Ioo 0 T

/-- Interior points see the closed slab as a neighbourhood. -/
theorem spaceTimeSlab_mem_nhds
    {T : ℝ} (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    spaceTimeSlab T ∈ nhds (x, t) := by
  apply Filter.mem_of_superset
    (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
  rintro z ⟨_hzspace, hztime⟩
  exact ⟨Set.mem_univ z.1, hztime.1.le, hztime.2.le⟩

/-- A smooth slab field is jointly smooth at every interior event. -/
theorem contDiffAt_of_contDiffOn_spaceTimeSlab
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {T : ℝ} (field : Space → ℝ → F)
    (hfield : ContDiffOn ℝ n (Function.uncurry field) (spaceTimeSlab T))
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiffAt ℝ n (Function.uncurry field) (x, t) :=
  hfield.contDiffAt (spaceTimeSlab_mem_nhds x ht0 htT)

/-- Every interior spatial slice of a smooth slab field is globally smooth in space. -/
theorem spatialSlice_contDiff_of_contDiffOn_spaceTimeSlab
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {T : ℝ} (field : Space → ℝ → F)
    (hfield : ContDiffOn ℝ n (Function.uncurry field) (spaceTimeSlab T))
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ n (fun x => field x t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hjoint := contDiffAt_of_contDiffOn_spaceTimeSlab field hfield x ht0 htT
  have hpair : ContDiffAt ℝ n (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using hjoint.comp x hpair

/-- The joint Eulerian jet agrees with the derivative within the actual finite slab at every
interior event. -/
theorem smoothSolutionOn_eulerianTimeJet_eq_derivWithin
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    eulerianTimeJet velocity x t = derivWithin (velocity x) (timeSlab T) t := by
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (contDiffAt_of_contDiffOn_spaceTimeSlab velocity solution.velocitySmooth x ht0 htT)
      |>.differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have htimeApply := congrArg (fun L : ℝ →L[ℝ] Space => L 1) htime.fderiv
  have hslab : timeSlab T ∈ nhds t := by
    apply Filter.mem_of_superset (Ioo_mem_nhds ht0 htT)
    exact fun _ h => ⟨h.1.le, h.2.le⟩
  rw [derivWithin_of_mem_nhds hslab]
  simpa [eulerianTimeJet, Function.comp_def, fderiv_apply_one_eq_deriv] using
    htimeApply.symm

/-- The two joint/slice vorticity realizations agree throughout the slab interior. -/
theorem smoothSolutionOn_jointVorticityField_eq_vorticityField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    jointVorticityField velocity x t = vorticityField velocity x t := by
  apply jointVorticityField_eq_vorticityField_of_contDiffAt
  exact (contDiffAt_of_contDiffOn_spaceTimeSlab velocity solution.velocitySmooth x ht0 htT).of_le
    (by norm_num)

/-- Joint vorticity is smooth on the complete open interior cylinder. -/
theorem smoothSolutionOn_jointVorticityField_contDiffOn_interior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (jointVorticityField velocity))
      (openSpaceTimeSlab T) := by
  have hopen : IsOpen (openSpaceTimeSlab T) := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) (openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, t⟩ ⟨_hx, ht⟩
    exact ⟨Set.mem_univ x, ht.1.le, ht.2.le⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) (openSpaceTimeSlab T) :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have hcurl := jointSpatialCurlLinearMap.contDiff.comp_contDiffOn hderivative
  apply hcurl.congr
  rintro ⟨x, t⟩ hxt
  rfl

/-- Slice-defined vorticity is jointly smooth on the slab interior. -/
theorem smoothSolutionOn_vorticityField_contDiffOn_interior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (vorticityField velocity))
      (openSpaceTimeSlab T) := by
  apply (smoothSolutionOn_jointVorticityField_contDiffOn_interior solution).congr
  rintro ⟨x, t⟩ ⟨_hx, ht⟩
  exact (smoothSolutionOn_jointVorticityField_eq_vorticityField
    solution x ht.1 ht.2).symm

/-- Spatial curl commutes with the Eulerian time jet at every interior slab event. -/
theorem smoothSolutionOn_eulerianTimeJet_vorticityField_eq_vorticityAt_eulerianTimeJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    eulerianTimeJet (vorticityField velocity) x t =
      vorticityAt (fun y => eulerianTimeJet velocity y t) x := by
  have hfield : ContDiffAt ℝ 2 (Function.uncurry velocity) (x, t) :=
    (contDiffAt_of_contDiffOn_spaceTimeSlab velocity solution.velocitySmooth x ht0 htT).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hlocal :
      Function.uncurry (jointVorticityField velocity) =ᶠ[nhds (x, t)]
        Function.uncurry (vorticityField velocity) := by
    filter_upwards [prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT)] with z hz
    exact smoothSolutionOn_jointVorticityField_eq_vorticityField
      solution z.1 hz.2.1 hz.2.2
  rw [← eulerianTimeJet_jointVorticityField_eq_vorticityAt_eulerianTimeJet
    velocity x t hfield]
  unfold eulerianTimeJet
  rw [hlocal.fderiv_eq]

/-- An interior Eulerian time-jet slice is spatially `C²`. -/
theorem smoothSolutionOn_eulerianTimeJet_contDiff_two
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ 2 (fun x => eulerianTimeJet velocity x t) := by
  have hopen : IsOpen (openSpaceTimeSlab T) := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) (openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, tau⟩ ⟨_hx, htau⟩
    exact ⟨Set.mem_univ x, htau.1.le, htau.2.le⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) (openSpaceTimeSlab T) :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have htimeJoint : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (Function.uncurry velocity) z timeDirection)
      (openSpaceTimeSlab T) := hderivative.clm_apply contDiffOn_const
  have htimeField : ContDiffOn ℝ ∞
      (Function.uncurry (eulerianTimeJet velocity)) (openSpaceTimeSlab T) := by
    change ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (Function.uncurry velocity) z (0, 1)) (openSpaceTimeSlab T)
    simpa [timeDirection] using htimeJoint
  rw [contDiff_iff_contDiffAt]
  intro x
  have hjoint : ContDiffAt ℝ ∞
      (Function.uncurry (eulerianTimeJet velocity)) (x, t) :=
    htimeField.contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht0 htT))
  have hpair : ContDiffAt ℝ ∞ (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  exact (by simpa [Function.comp_def] using hjoint.comp x hpair :
    ContDiffAt ℝ ∞ (fun y => eulerianTimeJet velocity y t) x).of_le
      (WithTop.coe_le_coe.mpr le_top)

/-! ## The interior curled momentum equation -/

/-- Velocity slices are globally smooth in space at every interior slab time. -/
theorem smoothSolutionOn_velocitySpatialSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ ∞ (fun x => velocity x t) :=
  spatialSlice_contDiff_of_contDiffOn_spaceTimeSlab velocity
    solution.velocitySmooth ht0 htT

/-- Pressure slices are globally smooth in space at every interior slab time. -/
theorem smoothSolutionOn_pressureSpatialSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ ∞ (fun x => pressure x t) :=
  spatialSlice_contDiff_of_contDiffOn_spaceTimeSlab pressure
    solution.pressureSmooth ht0 htT

/-- Curl commutes with the vector Laplacian on every interior velocity slice. -/
theorem smoothSolutionOn_vorticityAt_laplacian_eq_laplacian_vorticityField
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    vorticityAt (fun y => Δ (fun z => velocity z t) y) x =
      Δ (fun y => vorticityField velocity y t) x :=
  vorticityAt_laplacian_eq_laplacian_vorticityAt
    (fun y => velocity y t) (smoothSolutionOn_velocitySpatialSmooth solution ht0 htT) x

/-- The finite momentum equation reconstructs a `C²` spatial force slice at every interior
time; no independent force regularity is assumed. -/
theorem smoothSolutionOn_forceSpatialSmooth
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    ContDiff ℝ 2 (fun x => force x t) := by
  let u : InitialVelocity := fun x => velocity x t
  let p : Space → ℝ := fun x => pressure x t
  let time : InitialVelocity := fun x => eulerianTimeJet velocity x t
  let advection : InitialVelocity := fun x => fderiv ℝ u x (u x)
  let viscous : InitialVelocity := Δ u
  let pressureGradient : InitialVelocity := gradient p
  have hu : ContDiff ℝ ∞ u := smoothSolutionOn_velocitySpatialSmooth solution ht0 htT
  have hp : ContDiff ℝ ∞ p := smoothSolutionOn_pressureSpatialSmooth solution ht0 htT
  have htime : ContDiff ℝ 2 time :=
    smoothSolutionOn_eulerianTimeJet_contDiff_two solution ht0 htT
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have huTwo : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hadvection : ContDiff ℝ 2 advection := hDu.clm_apply huTwo
  have hDuThree : ContDiff ℝ 3 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) :=
    hDuThree.fderiv_right (by norm_num)
  have hviscous : ContDiff ℝ 2 viscous := by
    have hlapfun : viscous = fun y => ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
      funext y
      exact laplacian_eq_sum_secondFDeriv u y
    rw [hlapfun]
    apply ContDiff.sum
    intro i _hi
    exact (hD2.clm_apply contDiff_const).clm_apply contDiff_const
  have hDp : ContDiff ℝ 2 (fderiv ℝ p) :=
    hp.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hpressureGradient : ContDiff ℝ 2 pressureGradient := by
    change ContDiff ℝ 2 ((InnerProductSpace.toDual ℝ Space).symm ∘ fderiv ℝ p)
    exact (InnerProductSpace.toDual ℝ Space).symm.contDiff.comp hDp
  have hforceEq : (fun x => force x t) =
      fun x => time x + advection x - nu • viscous x + pressureGradient x := by
    funext x
    have hm := solution.momentum x t ⟨ht0.le, htT.le⟩
    rw [← smoothSolutionOn_eulerianTimeJet_eq_derivWithin
      solution x ht0 htT] at hm
    have hadd := congrArg
      (fun z : Space => z - (nu • viscous x - pressureGradient x)) hm
    simpa [u, p, time, advection, viscous, pressureGradient, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using hadd.symm
  rw [hforceEq]
  exact ((htime.add hadvection).sub (hviscous.const_smul nu)).add hpressureGradient

/-- Curl of the nonlinear advective field is transport minus stretching on the finite slab. -/
theorem smoothSolutionOn_vorticityAt_advection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    (x : Space) {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    vorticityAt
        (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
      fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) -
        fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) := by
  let u : InitialVelocity := fun y => velocity y t
  have hu : ContDiffAt ℝ 2 u x :=
    (smoothSolutionOn_velocitySpatialSmooth solution ht0 htT).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hmixed : HasMixedSpatialSymmetry (secondJetAt u x) :=
    secondJetAt_hasMixedSpatialSymmetry u x hu
  have hdiv : divergenceFromJacobian (velocityJacobianAt u x) = 0 := by
    rw [divergenceFromJacobian_velocityJacobianAt]
    exact solution.incompressible x t ⟨ht0.le, htT.le⟩
  have hcurl := curl_advectionJacobian_of_incompressible
    (secondJetAt u x) (velocityJacobianAt u x) (u x) hmixed hdiv
  rw [vorticityAt,
    velocityJacobianAt_advection_eq_advectionJacobianFromJets u x hu,
    hcurl,
    ← velocityJacobianAt_vorticity_eq_vorticityJacobianFromSecondJet u x hu,
    velocityJacobianAt, matrixAction_jacobianMatrix,
    velocityJacobianAt, matrixAction_jacobianMatrix]
  rfl

/-- Differentiating finite-slab momentum in space and applying curl removes pressure and returns
the unexpanded pointwise vorticity balance. -/
theorem smoothSolutionOn_curledMomentum
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet (vorticityField velocity) x t +
        vorticityAt
          (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
      nu • Δ (fun y => vorticityField velocity y t) x +
        vorticityField force x t := by
  let u : InitialVelocity := fun y => velocity y t
  let p : Space → ℝ := fun y => pressure y t
  let time : InitialVelocity := fun y => eulerianTimeJet velocity y t
  let advection : InitialVelocity := fun y => fderiv ℝ u y (u y)
  let viscous : InitialVelocity := Δ u
  let pressureGradient : InitialVelocity := gradient p
  let forceSlice : InitialVelocity := fun y => force y t
  have hu : ContDiff ℝ ∞ u := smoothSolutionOn_velocitySpatialSmooth solution ht0 htT
  have hp : ContDiff ℝ ∞ p := smoothSolutionOn_pressureSpatialSmooth solution ht0 htT
  have htime : ContDiff ℝ 2 time :=
    smoothSolutionOn_eulerianTimeJet_contDiff_two solution ht0 htT
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have huTwo : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hadvection : ContDiff ℝ 2 advection := hDu.clm_apply huTwo
  have hDuThree : ContDiff ℝ 3 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) :=
    hDuThree.fderiv_right (by norm_num)
  have hviscous : ContDiff ℝ 2 viscous := by
    have hlapfun : viscous = fun y => ∑ i : Fin 3,
        fderiv ℝ (fderiv ℝ u) y
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
      funext y
      exact laplacian_eq_sum_secondFDeriv u y
    rw [hlapfun]
    apply ContDiff.sum
    intro i _hi
    exact (hD2.clm_apply contDiff_const).clm_apply contDiff_const
  have hDp : ContDiff ℝ 2 (fderiv ℝ p) :=
    hp.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hpressureGradient : ContDiff ℝ 2 pressureGradient := by
    change ContDiff ℝ 2 ((InnerProductSpace.toDual ℝ Space).symm ∘ fderiv ℝ p)
    exact (InnerProductSpace.toDual ℝ Space).symm.contDiff.comp hDp
  have hforce : ContDiff ℝ 2 forceSlice :=
    smoothSolutionOn_forceSpatialSmooth solution ht0 htT
  have hmomentumFunctions :
      (fun y => time y + advection y) =
        (fun y => nu • viscous y - pressureGradient y + forceSlice y) := by
    funext y
    change eulerianTimeJet velocity y t +
        fderiv ℝ (fun z => velocity z t) y (velocity y t) =
      nu • Δ (fun z => velocity z t) y -
        gradient (fun z => pressure z t) y + force y t
    rw [smoothSolutionOn_eulerianTimeJet_eq_derivWithin solution y ht0 htT]
    exact solution.momentum y t ⟨ht0.le, htT.le⟩
  have htimeDiff : DifferentiableAt ℝ time x := htime.differentiable (by norm_num) x
  have hadvectionDiff : DifferentiableAt ℝ advection x :=
    hadvection.differentiable (by norm_num) x
  have hviscousDiff : DifferentiableAt ℝ viscous x :=
    hviscous.differentiable (by norm_num) x
  have hpressureDiff : DifferentiableAt ℝ pressureGradient x :=
    hpressureGradient.differentiable (by norm_num) x
  have hforceDiff : DifferentiableAt ℝ forceSlice x :=
    hforce.differentiable (by norm_num) x
  have hderivative := congrArg (fun f : InitialVelocity => fderiv ℝ f x)
    hmomentumFunctions
  change fderiv ℝ (fun y => time y + advection y) x =
    fderiv ℝ (fun y => nu • viscous y - pressureGradient y + forceSlice y) x
      at hderivative
  have hleft : fderiv ℝ (fun y => time y + advection y) x =
      fderiv ℝ time x + fderiv ℝ advection x :=
    (htimeDiff.hasFDerivAt.add hadvectionDiff.hasFDerivAt).fderiv
  have hright :
      fderiv ℝ (fun y => nu • viscous y - pressureGradient y + forceSlice y) x =
        nu • fderiv ℝ viscous x - fderiv ℝ pressureGradient x +
          fderiv ℝ forceSlice x :=
    (((hviscousDiff.hasFDerivAt.const_smul nu).sub hpressureDiff.hasFDerivAt).add
      hforceDiff.hasFDerivAt).fderiv
  rw [hleft, hright] at hderivative
  have hcurl := congrArg derivativeCurlLinearMap hderivative
  simp only [map_add, map_sub, map_smul] at hcurl
  have htimeCurl :=
    smoothSolutionOn_eulerianTimeJet_vorticityField_eq_vorticityAt_eulerianTimeJet
      solution x ht0 htT
  have hviscousCurl :=
    smoothSolutionOn_vorticityAt_laplacian_eq_laplacian_vorticityField
      solution x ht0 htT
  have hpressureCurl : vorticityAt pressureGradient x = 0 := by
    apply curl_gradient_eq_zero
    exact hp.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  change vorticityAt time x + vorticityAt advection x =
    nu • vorticityAt viscous x - vorticityAt pressureGradient x +
      vorticityAt forceSlice x at hcurl
  rw [← htimeCurl, hviscousCurl, hpressureCurl, sub_zero] at hcurl
  simpa [u, time, advection, viscous, pressureGradient, forceSlice,
    vorticityField] using hcurl

/-- The finite smooth momentum equation supplies the complete unexpanded vorticity-balance port
at every interior time. -/
theorem smoothSolutionOn_hasPointwiseVorticityBalanceAt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    HasPointwiseVorticityBalanceAt nu force velocity t where
  forceSpatialSmooth := smoothSolutionOn_forceSpatialSmooth solution ht0 htT
  curledMomentum := smoothSolutionOn_curledMomentum solution ht0 htT

/-- The expanded finite-slab vorticity equation, with transport and stretching kept distinct. -/
theorem smoothSolutionOn_pointwiseVorticityBalance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    eulerianTimeJet (vorticityField velocity) x t +
        fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) =
      fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) +
        nu • Δ (fun y => vorticityField velocity y t) x +
          vorticityField force x t := by
  have hnonlinear := smoothSolutionOn_vorticityAt_advection solution x ht0 htT
  have hcurled := smoothSolutionOn_curledMomentum solution ht0 htT x
  rw [hnonlinear] at hcurled
  calc
    eulerianTimeJet (vorticityField velocity) x t +
        fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) =
      (eulerianTimeJet (vorticityField velocity) x t +
          (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t) -
            fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))) +
        fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) := by abel
    _ = (nu • Δ (fun y => vorticityField velocity y t) x +
          vorticityField force x t) +
        fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t) := by
          rw [hcurled]
    _ = _ := by abel



section Audit

#print axioms PeriodicSolution.toPeriodicSolutionOn
#print axioms smoothSolutionOn_hasPointwiseVorticityBalanceAt
#print axioms smoothSolutionOn_pointwiseVorticityBalance

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

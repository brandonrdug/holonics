import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy

/-!
# Curl commutation closes the periodic enstrophy balance

This module discharges the two linear compatibility squares left explicit by
`NavierStokesPeriodicEnstrophy`:

* spatial curl commutes with the positive-time Eulerian derivative by symmetry of the admitted
  joint second derivative;
* spatial curl commutes with the vector Laplacian by third-derivative symmetry, proved from finite
  `C^3` calculus rather than an analyticity assumption.

The official smooth momentum equation then reconstructs `C^2` spatial regularity of the force,
removes pressure through the existing symmetric-gradient curl kernel, and returns
`HasPointwiseVorticityBalanceAt` without an extra PDE hypothesis.  Consequently the periodic
forced enstrophy identity is unconditional on `PeriodicSolution` at strictly positive time.  The
three-dimensional stretching term remains; this module proves no estimate absorbing it.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- The positive time direction in the joint space--time carrier. -/
def timeDirection : Space × ℝ := (0, 1)

/-- At a genuine joint `C^2` occurrence, first restricting the time derivative to a spatial slice
equals first restricting spatially and then differentiating in time. -/
theorem fderiv_timeSlice_eq_time_fderiv_spatial
    (field : VelocityField) (x : Space) (t : ℝ)
    (hfield : ContDiffAt ℝ 2 (Function.uncurry field) (x, t)) :
    fderiv ℝ (fun y : Space =>
      fderiv ℝ (Function.uncurry field) (y, t) timeDirection) x =
      (fderiv ℝ (fderiv ℝ (Function.uncurry field)) (x, t) timeDirection).comp
        spatialInclusion := by
  let F : Space × ℝ → Space := Function.uncurry field
  let pair : Space → Space × ℝ := fun y => (y, t)
  let G : Space × ℝ → (Space × ℝ →L[ℝ] Space) := fderiv ℝ F
  have hG : DifferentiableAt ℝ G (x, t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hpair : HasFDerivAt pair spatialInclusion x :=
    hasFDerivAt_prodMk_left (𝕜 := ℝ) x t
  have hcomp : fderiv ℝ (G ∘ pair) x =
      (fderiv ℝ G (x, t)).comp spatialInclusion := by
    exact (hG.hasFDerivAt.comp x hpair).fderiv
  have hc : DifferentiableAt ℝ (G ∘ pair) x := hG.comp x hpair.differentiableAt
  have happly := fderiv_clm_apply hc (differentiableAt_const timeDirection)
  have hsymm : IsSymmSndFDerivAt ℝ F (x, t) :=
    hfield.isSymmSndFDerivAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro e
  change fderiv ℝ (fun y => ((G ∘ pair) y) timeDirection) x e =
    ((fderiv ℝ G (x, t) timeDirection).comp spatialInclusion) e
  rw [happly, ContinuousLinearMap.add_apply, hcomp]
  simp [spatialInclusion]
  exact hsymm.eq (e, 0) timeDirection

/-- The Eulerian derivative of the joint-derivative vorticity realization is the spatial curl of
the Eulerian derivative. -/
theorem eulerianTimeJet_jointVorticityField_eq_vorticityAt_eulerianTimeJet
    (field : VelocityField) (x : Space) (t : ℝ)
    (hfield : ContDiffAt ℝ 2 (Function.uncurry field) (x, t)) :
    eulerianTimeJet (jointVorticityField field) x t =
      vorticityAt (fun y => eulerianTimeJet field y t) x := by
  have hG : DifferentiableAt ℝ
      (fderiv ℝ (Function.uncurry field)) (x, t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have htimeSpatial := fderiv_timeSlice_eq_time_fderiv_spatial field x t hfield
  unfold eulerianTimeJet jointVorticityField vorticityAt velocityJacobianAt
  change fderiv ℝ
      (jointSpatialCurlLinearMap ∘ fderiv ℝ (Function.uncurry field)) (x, t)
        timeDirection =
    derivativeCurlLinearMap
      (fderiv ℝ (fun y =>
        fderiv ℝ (Function.uncurry field) (y, t) timeDirection) x)
  rw [fderiv_comp (x, t) jointSpatialCurlLinearMap.differentiableAt hG,
    ContinuousLinearMap.fderiv, htimeSpatial]
  rfl

/-- Mixed time--curl commutation on the actual slice-defined positive-time solution vorticity. -/
theorem smoothSolution_eulerianTimeJet_vorticityField_eq_vorticityAt_eulerianTimeJet
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    eulerianTimeJet (vorticityField velocity) x t =
      vorticityAt (fun y => eulerianTimeJet velocity y t) x := by
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  have hfield : ContDiffAt ℝ 2 (Function.uncurry velocity) (x, t) :=
    (solution.velocitySmooth.contDiffAt hdomain).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hlocal :
      Function.uncurry (jointVorticityField velocity) =ᶠ[nhds (x, t)]
        Function.uncurry (vorticityField velocity) := by
    filter_upwards [prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht)] with z hz
    exact smoothSolution_jointVorticityField_eq_vorticityField
      solution z.1 z.2 hz.2
  rw [← eulerianTimeJet_jointVorticityField_eq_vorticityAt_eulerianTimeJet
    velocity x t hfield]
  unfold eulerianTimeJet
  rw [hlocal.fderiv_eq]

/-- The joint Eulerian derivative agrees with the official within-time derivative for every smooth
solution; periodicity is irrelevant to this local attachment. -/
theorem smoothSolution_eulerianTimeJet_eq_derivWithin
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    eulerianTimeJet velocity x t = derivWithin (velocity x) (Ici 0) t := by
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzspace, hztime⟩
    exact ⟨Set.mem_univ z.1, show 0 ≤ z.2 from le_of_lt hztime⟩
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (solution.velocitySmooth.contDiffAt hdomain).differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have htimeApply := congrArg (fun L : ℝ →L[ℝ] Space => L 1) htime.fderiv
  have hhalf : Set.Ici (0 : ℝ) ∈ nhds t :=
    Filter.mem_of_superset (Ioi_mem_nhds ht) Set.Ioi_subset_Ici_self
  rw [derivWithin_of_mem_nhds hhalf]
  simpa [eulerianTimeJet, Function.comp_def, fderiv_apply_one_eq_deriv] using
    htimeApply.symm

/-- A positive-time Eulerian time-jet slice of a smooth solution is spatially `C^2`. -/
theorem smoothSolution_eulerianTimeJet_contDiff_two
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ 2 (fun x => eulerianTimeJet velocity x t) := by
  let positiveCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioi (0 : ℝ)
  have hopen : IsOpen positiveCylinder := isOpen_univ.prod isOpen_Ioi
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) positiveCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, tau⟩ ⟨_hx, htau⟩
    exact ⟨Set.mem_univ x, show 0 ≤ tau from le_of_lt htau⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) positiveCylinder :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have htimeJoint : ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (Function.uncurry velocity) z timeDirection)
      positiveCylinder :=
    hderivative.clm_apply contDiffOn_const
  have htimeField : ContDiffOn ℝ ∞
      (Function.uncurry (eulerianTimeJet velocity)) positiveCylinder := by
    change ContDiffOn ℝ ∞
      (fun z => fderiv ℝ (Function.uncurry velocity) z (0, 1)) positiveCylinder
    simpa [timeDirection] using htimeJoint
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (positiveTimeSpatialSlice_contDiffAt
    (eulerianTimeJet velocity) x t ht htimeField).of_le
      (WithTop.coe_le_coe.mpr le_top)

/-- Differentiating a second derivative evaluated on two fixed directions returns the admitted
third derivative in those directions. -/
theorem fderiv_secondDerivative_apply
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (x a b c : Space) :
    fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y a c) x b =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b a c := by
  let K : Space → (Space →L[ℝ] Space →L[ℝ] Space) :=
    fderiv ℝ (fderiv ℝ u)
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hKsmooth : ContDiff ℝ 1 K := by
    exact hDu.fderiv_right (by norm_num)
  have hK : DifferentiableAt ℝ K x :=
    hKsmooth.differentiable (by norm_num) x
  have hKa : DifferentiableAt ℝ (fun y => K y a) x :=
    hK.clm_apply (differentiableAt_const a)
  have ha := fderiv_clm_apply hK (differentiableAt_const a)
  have hc := fderiv_clm_apply hKa (differentiableAt_const c)
  change fderiv ℝ (fun y => (K y a) c) x b = fderiv ℝ K x b a c
  rw [hc, ContinuousLinearMap.add_apply, ha]
  simp

/-- Cyclic rotation of three derivative directions for a smooth spatial field.  The proof uses
only repeated second-derivative symmetry and therefore assumes no analyticity. -/
theorem thirdFDeriv_rotate
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (x a b c : Space) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x a b c =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b c a := by
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have houter :
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x a b c =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b a c := by
    exact congrArg (fun L : Space →L[ℝ] Space => L c)
      ((hDu.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq a b)
  have hsecondFunctions :
      (fun y => fderiv ℝ (fderiv ℝ u) y a c) =
        (fun y => fderiv ℝ (fderiv ℝ u) y c a) := by
    funext y
    have hu2 : ContDiffAt ℝ 2 u y :=
      hu.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    exact (hu2.isSymmSndFDerivAt (by norm_num)).eq a c
  have hinner :
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b a c =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x b c a := by
    rw [← fderiv_secondDerivative_apply u hu x a b c,
      ← fderiv_secondDerivative_apply u hu x c b a,
      hsecondFunctions]
  exact houter.trans hinner

/-- Coordinate expansion of the Euclidean Laplacian through the standard orthonormal basis. -/
theorem laplacian_eq_sum_secondFDeriv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : Space → F) (x : Space) :
    Δ u x = ∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis u
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [iteratedFDeriv_two_apply]
  rfl

/-- The spatial derivative commutes with the Euclidean vector Laplacian on a smooth field. -/
theorem fderiv_laplacian_eq_laplacian_fderiv
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (x : Space) :
    fderiv ℝ (Δ u) x = Δ (fderiv ℝ u) x := by
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) := by
    exact hDu.fderiv_right (by norm_num)
  have hterm : ∀ i : Fin 3, DifferentiableAt ℝ
      (fun y => fderiv ℝ (fderiv ℝ u) y
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ i)) x := by
    intro i
    exact ((hD2.differentiable (by norm_num) x).clm_apply
      (differentiableAt_const (EuclideanSpace.basisFun (Fin 3) ℝ i))).clm_apply
        (differentiableAt_const (EuclideanSpace.basisFun (Fin 3) ℝ i))
  have hlapfun : Δ u = fun y => ∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ u) y
        (EuclideanSpace.basisFun (Fin 3) ℝ i)
        (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
    funext y
    exact laplacian_eq_sum_secondFDeriv u y
  rw [hlapfun, fderiv_fun_sum (fun i _hi => hterm i)]
  apply ContinuousLinearMap.ext
  intro v
  rw [laplacian_eq_sum_secondFDeriv]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [fderiv_secondDerivative_apply u hu]
  exact thirdFDeriv_rotate u hu x v
    (EuclideanSpace.basisFun (Fin 3) ℝ i)
    (EuclideanSpace.basisFun (Fin 3) ℝ i)

/-- Spatial curl commutes with the vector Laplacian on a smooth three-dimensional field. -/
theorem vorticityAt_laplacian_eq_laplacian_vorticityAt
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (x : Space) :
    vorticityAt (Δ u) x = Δ (fun y => vorticityAt u y) x := by
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hl := (hDu.contDiffAt (x := x)).laplacian_CLM_comp_left
    (l := derivativeCurlLinearMap)
  unfold vorticityAt velocityJacobianAt
  change derivativeCurlLinearMap (fderiv ℝ (Δ u) x) =
    Δ (derivativeCurlLinearMap ∘ fderiv ℝ u) x
  rw [fderiv_laplacian_eq_laplacian_fderiv u hu x]
  exact hl.symm

/-- Curl--Laplacian commutation attached to a positive-time smooth-solution slice. -/
theorem smoothSolution_vorticityAt_laplacian_eq_laplacian_vorticityField
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    vorticityAt (fun y => Δ (fun z => velocity z t) y) x =
      Δ (fun y => vorticityField velocity y t) x := by
  have hu : ContDiff ℝ ∞ (fun y => velocity y t) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity y t
      solution.velocitySmooth ht
  exact vorticityAt_laplacian_eq_laplacian_vorticityAt
    (fun y => velocity y t) hu x

/-- At positive time the official momentum equality reconstructs a globally `C^2` spatial force
slice from the smooth time, advection, viscosity, and pressure-gradient faces. -/
theorem smoothSolution_forceSpatialSmooth
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ 2 (fun x => force x t) := by
  let u : InitialVelocity := fun x => velocity x t
  let p : Space → ℝ := fun x => pressure x t
  let time : InitialVelocity := fun x => eulerianTimeJet velocity x t
  let advection : InitialVelocity := fun x => fderiv ℝ u x (u x)
  let viscous : InitialVelocity := Δ u
  let pressureGradient : InitialVelocity := gradient p
  have hu : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
      solution.velocitySmooth ht
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
      solution.pressureSmooth ht
  have htime : ContDiff ℝ 2 time :=
    smoothSolution_eulerianTimeJet_contDiff_two solution t ht
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have huTwo : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hadvection : ContDiff ℝ 2 advection := hDu.clm_apply huTwo
  have hDuThree : ContDiff ℝ 3 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := by
    exact hDuThree.fderiv_right (by norm_num)
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
    have hm := solution.momentum x t ht.le
    rw [← smoothSolution_eulerianTimeJet_eq_derivWithin solution x t ht] at hm
    have hadd := congrArg
      (fun z : Space => z - (nu • viscous x - pressureGradient x)) hm
    simpa [u, p, time, advection, viscous, pressureGradient, sub_eq_add_neg,
      add_assoc, add_comm, add_left_comm] using hadd.symm
  rw [hforceEq]
  exact ((htime.add hadvection).sub (hviscous.const_smul nu)).add
    hpressureGradient

/-- Differentiating the official momentum equality in space and applying the linear curl receiver
removes pressure and returns the unexpanded curled momentum balance. -/
theorem smoothSolution_curledMomentum
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (x : Space) :
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
  have hu : ContDiff ℝ ∞ u := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity y t
      solution.velocitySmooth ht
  have hp : ContDiff ℝ ∞ p := by
    rw [contDiff_iff_contDiffAt]
    intro y
    exact spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure y t
      solution.pressureSmooth ht
  have htime : ContDiff ℝ 2 time :=
    smoothSolution_eulerianTimeJet_contDiff_two solution t ht
  have hDu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have huTwo : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hadvection : ContDiff ℝ 2 advection := hDu.clm_apply huTwo
  have hDuThree : ContDiff ℝ 3 (fderiv ℝ u) :=
    hu.fderiv_right (WithTop.coe_le_coe.mpr le_top)
  have hD2 : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ u)) := by
    exact hDuThree.fderiv_right (by norm_num)
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
    smoothSolution_forceSpatialSmooth solution t ht
  have hmomentumFunctions :
      (fun y => time y + advection y) =
        (fun y => nu • viscous y - pressureGradient y + forceSlice y) := by
    funext y
    change eulerianTimeJet velocity y t +
        fderiv ℝ (fun z => velocity z t) y (velocity y t) =
      nu • Δ (fun z => velocity z t) y -
        gradient (fun z => pressure z t) y + force y t
    rw [smoothSolution_eulerianTimeJet_eq_derivWithin solution y t ht]
    exact solution.momentum y t ht.le
  have htimeDiff : DifferentiableAt ℝ time x :=
    htime.differentiable (by norm_num) x
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
    smoothSolution_eulerianTimeJet_vorticityField_eq_vorticityAt_eulerianTimeJet
      solution x t ht
  have hviscousCurl :=
    smoothSolution_vorticityAt_laplacian_eq_laplacian_vorticityField
      solution x t ht
  have hpressureCurl := smoothSolution_pressureCurl_eq_zero solution x t ht
  change vorticityAt time x + vorticityAt advection x =
    nu • vorticityAt viscous x - vorticityAt pressureGradient x +
      vorticityAt forceSlice x at hcurl
  rw [← htimeCurl, hviscousCurl, hpressureCurl, sub_zero] at hcurl
  simpa [u, time, advection, viscous, pressureGradient, forceSlice,
    vorticityField] using hcurl

/-- The official smooth momentum equation itself supplies the formerly open pointwise curled
balance at every strictly positive time.  No independent force-regularity or vorticity-equation
hypothesis is needed: force regularity is reconstructed from momentum and the smooth velocity and
pressure carriers. -/
theorem smoothSolution_hasPointwiseVorticityBalanceAt
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    HasPointwiseVorticityBalanceAt nu force velocity t where
  forceSpatialSmooth := smoothSolution_forceSpatialSmooth solution t ht
  curledMomentum := smoothSolution_curledMomentum solution t ht

/-- The forced periodic enstrophy identity now follows from `PeriodicSolution` alone at every
strictly positive time; the previous explicit balance port is filled by differentiated momentum. -/
theorem periodicSolution_hasDerivAt_periodicEnstrophy_fromMomentum
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) :
    HasDerivAt (periodicEnstrophy velocity)
      (periodicEnstrophyRate nu force velocity t) t :=
  periodicSolution_hasDerivAt_periodicEnstrophy solution t ht
    (smoothSolution_hasPointwiseVorticityBalanceAt solution.toSmoothSolution t ht)

/-- For nonnegative viscosity the exact stretching-absorption criterion is unconditional on the
positive-time periodic solution carrier. -/
theorem periodicSolution_deriv_periodicEnstrophy_nonpos_iff_fromMomentum
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (t : ℝ) (ht : 0 < t) (hnu : 0 ≤ nu) :
    deriv (periodicEnstrophy velocity) t ≤ 0 ↔
      periodicVortexStretching velocity t +
          periodicCurlForcingWork force velocity t ≤
        nu * periodicVorticityDissipation velocity t :=
  periodicSolution_deriv_periodicEnstrophy_nonpos_iff solution t ht hnu
    (smoothSolution_hasPointwiseVorticityBalanceAt solution.toSmoothSolution t ht)

end Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy

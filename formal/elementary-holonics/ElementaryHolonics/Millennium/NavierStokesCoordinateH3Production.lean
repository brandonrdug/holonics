import ElementaryHolonics.Millennium.NavierStokesCoordinateH2Production

/-!
# The twenty-seven third-coordinate words of the periodic quadratic production law

This successor differentiates the actual unforced momentum return through every ordered triple of
spatial basis directions.  It keeps the seven lower Leibniz faces, while top transport and mixed
pressure work cancel on the periodic cube and viscosity is integrated by parts.  The result is an
exact order-three energy identity; no nonlinear norm estimate is asserted.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH3Production

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The ordered three-letter coordinate word `(i,j,k)`. -/
def thirdCoordinateWord (i j k : Fin 3) : Fin 3 → Fin 3 := ![i, j, k]

/-- The actual order-three joint coordinate jet. -/
def thirdCoordinateJet (velocity : VelocityField) (i j k : Fin 3) : VelocityField :=
  coordinateJetField velocity 3 (thirdCoordinateWord i j k)

/-- The corresponding ordered third spatial derivative. -/
def thirdSpatialCoordinateJet (u : InitialVelocity) (i j k : Fin 3) : InitialVelocity :=
  spatialDirectionalJet (secondSpatialCoordinateJet u j k) i

/-- The ordered third scalar pressure jet matching `(i,j,k)`. -/
def thirdPressureCoordinateJet (p : Space → ℝ) (i j k : Fin 3) : Space → ℝ :=
  pressureDirectionalJet (secondPressureCoordinateJet p j k) i

/-- At a genuinely smooth occurrence, a three-letter joint word is the first-coordinate jet of
the actual two-letter suffix. -/
theorem thirdCoordinateJet_eq_nestedSecond_of_contDiffAt
    (field : VelocityField) (x : Space) (t : ℝ) (i j k : Fin 3)
    (hfield : ContDiffAt ℝ ∞ (Function.uncurry field) (x, t)) :
    thirdCoordinateJet field i j k x t =
      firstCoordinateJet (secondCoordinateJet field j k) i x t := by
  let F : Space × ℝ → Space := Function.uncurry field
  let ei : Space × ℝ := jointSpatialBasisDirection i
  let directions : Fin 2 → Space × ℝ :=
    coordinateWordDirections (secondCoordinateWord j k)
  let evaluate : ((Space × ℝ) [×2]→L[ℝ] Space) →L[ℝ] Space :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ Space × ℝ) Space directions
  have hD2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 F) (x, t) :=
    hfield.differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2))
  have hevaluate :
      fderiv ℝ (fun z ↦ evaluate (iteratedFDeriv ℝ 2 F z)) (x, t) =
        evaluate.comp (fderiv ℝ (iteratedFDeriv ℝ 2 F) (x, t)) := by
    simpa only [ContinuousLinearMap.fderiv] using
      fderiv_fun_comp (x, t) evaluate.differentiableAt hD2
  have hevaluateApply := congrArg
    (fun L : (Space × ℝ) →L[ℝ] Space ↦ L ei) hevaluate
  have htail :
      Fin.tail (coordinateWordDirections (thirdCoordinateWord i j k)) = directions := by
    funext q
    fin_cases q <;> rfl
  have hfirst : coordinateWordDirections (firstCoordinateWord i) = fun _ ↦ ei := by
    funext q
    fin_cases q
    simp [firstCoordinateWord, coordinateWordDirections, ei]
  change iteratedFDeriv ℝ 3 F (x, t)
      (coordinateWordDirections (thirdCoordinateWord i j k)) =
    iteratedFDeriv ℝ 1
      (fun z ↦ iteratedFDeriv ℝ 2 F z directions) (x, t)
      (coordinateWordDirections (firstCoordinateWord i))
  rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_one_apply, htail, hfirst]
  simpa [evaluate, Function.comp_def, thirdCoordinateWord,
    coordinateWordDirections, jointSpatialBasisDirection, ei] using hevaluateApply.symm

/-- On an admitted interior slab, the actual three-letter word is the spatial derivative of its
actual two-letter suffix. -/
theorem openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    thirdCoordinateJet velocity i j k x t =
      spatialDirectionalJet (fun y ↦ secondCoordinateJet velocity j k y t) i x := by
  let slab : Set (Space × ℝ) :=
    Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) slab := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hsecond : ContDiffOn ℝ ∞
      (Function.uncurry (secondCoordinateJet velocity j k)) slab := by
    simpa [secondCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 2 (secondCoordinateWord j k)
  have hdomain : slab ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hvelocityAt : ContDiffAt ℝ ∞ (Function.uncurry velocity) (x, t) :=
    hvelocity.contDiffAt hdomain
  have hnested := thirdCoordinateJet_eq_nestedSecond_of_contDiffAt
    velocity x t i j k hvelocityAt
  have hsecondDiff : DifferentiableAt ℝ
      (Function.uncurry (secondCoordinateJet velocity j k)) (x, t) :=
    (hsecond.contDiffAt hdomain).differentiableAt (by simp)
  have hslice := hsecondDiff.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have hsliceApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hslice.fderiv
  rw [hnested]
  change iteratedFDeriv ℝ 1
      (Function.uncurry (secondCoordinateJet velocity j k)) (x, t)
        (coordinateWordDirections (firstCoordinateWord i)) =
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity j k y t) x
      (spatialBasisVector i)
  rw [iteratedFDeriv_one_apply]
  simpa [coordinateWordDirections, firstCoordinateWord, jointSpatialBasisDirection,
    spatialInclusion, Function.comp_def] using
      congrArg (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i))
        hslice.fderiv.symm

/-- Hence the joint word agrees exactly with the nested fixed-time spatial derivative. -/
theorem openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    thirdCoordinateJet velocity i j k x t =
      thirdSpatialCoordinateJet (fun y ↦ velocity y t) i j k x := by
  rw [openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
    solution ht x i j k]
  have hsuffix : (fun y ↦ secondCoordinateJet velocity j k y t) =
      secondSpatialCoordinateJet (fun y ↦ velocity y t) j k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y j k
  rw [hsuffix]
  rfl

theorem thirdSpatialCoordinateJet_contDiff
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (i j k : Fin 3) :
    ContDiff ℝ ∞ (thirdSpatialCoordinateJet u i j k) := by
  exact spatialDirectionalJet_contDiff (secondSpatialCoordinateJet u j k)
    (secondSpatialCoordinateJet_contDiff u hu j k) i

theorem thirdSpatialCoordinateJet_isOnePeriodic
    (u : InitialVelocity) (hu : IsOnePeriodic u) (i j k : Fin 3) :
    IsOnePeriodic (thirdSpatialCoordinateJet u i j k) := by
  exact spatialDirectionalJet_isOnePeriodic (secondSpatialCoordinateJet u j k)
    (secondSpatialCoordinateJet_isOnePeriodic u hu j k) i

/-- Three spatial coordinate differentiations preserve incompressibility. -/
theorem divergence_thirdSpatialCoordinateJet_eq_zero
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) (i j k : Fin 3) :
    divergence (thirdSpatialCoordinateJet u i j k) x = 0 := by
  let suffix := secondSpatialCoordinateJet u j k
  have hsuffixSmooth : ContDiff ℝ ∞ suffix :=
    secondSpatialCoordinateJet_contDiff u hu j k
  have hsuffixDiv : ∀ y, divergence suffix y = 0 := fun y ↦
    divergence_secondSpatialCoordinateJet_eq_zero u hu hdiv y j k
  exact divergence_spatialDirectionalJet_eq_zero suffix
    (hsuffixSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) hsuffixDiv x i

theorem thirdPressureCoordinateJet_contDiff
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (i j k : Fin 3) :
    ContDiff ℝ ∞ (thirdPressureCoordinateJet p i j k) := by
  exact pressureDirectionalJet_contDiff (secondPressureCoordinateJet p j k)
    (secondPressureCoordinateJet_contDiff p hp j k) i

theorem thirdPressureCoordinateJet_isOnePeriodic
    (p : Space → ℝ) (hp : IsOnePeriodic p) (i j k : Fin 3) :
    IsOnePeriodic (thirdPressureCoordinateJet p i j k) := by
  exact pressureDirectionalJet_isOnePeriodic (secondPressureCoordinateJet p j k)
    (secondPressureCoordinateJet_isOnePeriodic p hp j k) i

/-- The derivative of the order-two pressure gradient is the gradient of the matching ordered
order-three scalar pressure jet. -/
theorem gradient_thirdPressureCoordinateJet_eq_fderiv_secondPressureGradient
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (x : Space) (i j k : Fin 3) :
    gradient (thirdPressureCoordinateJet p i j k) x =
      fderiv ℝ (gradient (secondPressureCoordinateJet p j k)) x
        (spatialBasisVector i) := by
  exact gradient_pressureDirectionalJet_eq_fderiv_gradient
    (secondPressureCoordinateJet p j k)
    ((secondPressureCoordinateJet_contDiff p hp j k).of_le
      (WithTop.coe_le_coe.mpr le_top)) x i

/-! ## Joint time and third spatial differentiation -/

/-- The actual order-three time jet is the spatial derivative of the actual order-two time jet. -/
theorem openPeriodicSolutionOn_eulerianTimeJet_thirdCoordinateJet_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    eulerianTimeJet (thirdCoordinateJet velocity i j k) x t =
      fderiv ℝ
        (fun y ↦ eulerianTimeJet (secondCoordinateJet velocity j k) y t) x
        (spatialBasisVector i) := by
  let slab : Set (Space × ℝ) :=
    Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T
  have hopen : IsOpen slab := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) slab := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hsecond : ContDiffOn ℝ ∞
      (Function.uncurry (secondCoordinateJet velocity j k)) slab := by
    simpa [secondCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 2 (secondCoordinateWord j k)
  have hdomain : slab ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hsecondAt : ContDiffAt ℝ 2
      (Function.uncurry (secondCoordinateJet velocity j k)) (x, t) :=
    (hsecond.contDiffAt hdomain).of_le (WithTop.coe_le_coe.mpr le_top)
  have hmixed := eulerianTimeJet_firstCoordinateJet_eq_fderiv_time_of_contDiffAt
    (secondCoordinateJet velocity j k) x t i hsecondAt
  have hlocal :
      Function.uncurry (thirdCoordinateJet velocity i j k) =ᶠ[nhds (x, t)]
        Function.uncurry (firstCoordinateJet (secondCoordinateJet velocity j k) i) := by
    filter_upwards [hdomain] with z hz
    have hzfield : ContDiffAt ℝ ∞ (Function.uncurry velocity) z :=
      hvelocity.contDiffAt (hopen.mem_nhds hz)
    exact thirdCoordinateJet_eq_nestedSecond_of_contDiffAt
      velocity z.1 z.2 i j k hzfield
  rw [← hmixed]
  unfold eulerianTimeJet
  rw [hlocal.fderiv_eq]

/-! ## The three-times differentiated actual momentum equation -/

/-- Differentiate the actual order-two production identity in the outer basis direction, before
splitting its nonlinear product faces. -/
theorem openPeriodicSolutionOn_unforced_thirdSpatialDerivative_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    fderiv ℝ
          (fun y ↦ eulerianTimeJet (secondCoordinateJet velocity j k) y t) x
          (spatialBasisVector i) +
        fderiv ℝ
          (fun y ↦ fderiv ℝ (fun z ↦ secondCoordinateJet velocity j k z t) y
            (velocity y t)) x (spatialBasisVector i) =
      nu • fderiv ℝ (Δ (fun y ↦ secondCoordinateJet velocity j k y t)) x
          (spatialBasisVector i) -
        fderiv ℝ
          (gradient (secondPressureCoordinateJet (fun y ↦ pressure y t) j k)) x
          (spatialBasisVector i) -
        fderiv ℝ
          (fun y ↦ secondCoordinateLowerCommutator velocity t j k y) x
          (spatialBasisVector i) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let Wjk : InitialVelocity := fun y ↦ secondCoordinateJet velocity j k y t
  let qjk : Space → ℝ := secondPressureCoordinateJet (fun y ↦ pressure y t) j k
  let timejk : InitialVelocity :=
    fun y ↦ eulerianTimeJet (secondCoordinateJet velocity j k) y t
  let transportjk : InitialVelocity := fun y ↦ fderiv ℝ Wjk y (u y)
  let lowerjk : InitialVelocity :=
    fun y ↦ secondCoordinateLowerCommutator velocity t j k y
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ (fun y ↦ pressure y t) :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hWjkFun : Wjk = secondSpatialCoordinateJet u j k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y j k
  have hWjk : ContDiff ℝ ∞ Wjk := by
    rw [hWjkFun]
    exact secondSpatialCoordinateJet_contDiff u hu j k
  have hqjk : ContDiff ℝ ∞ qjk :=
    secondPressureCoordinateJet_contDiff (fun y ↦ pressure y t) hp j k
  have hsecondJoint : ContDiffOn ℝ ∞
      (Function.uncurry (secondCoordinateJet velocity j k))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    simpa [secondCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 2 (secondCoordinateWord j k)
  have htimejk : ContDiff ℝ ∞ timejk :=
    eulerianTimeJetSlice_contDiff_of_contDiffOn_openSlab
      (secondCoordinateJet velocity j k) hsecondJoint ht
  have hDWjk : ContDiff ℝ ∞ (fderiv ℝ Wjk) := hWjk.fderiv_right (by simp)
  have htransportjk : ContDiff ℝ ∞ transportjk := hDWjk.clm_apply hu
  have hviscous : ContDiff ℝ ∞ (Δ Wjk) := laplacian_contDiff hWjk
  have hpressure : ContDiff ℝ ∞ (gradient qjk) := gradient_contDiff hqjk
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let wk : InitialVelocity := fun y ↦ firstCoordinateJet velocity k y t
  have hwjFun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hwkFun : wk = spatialDirectionalJet u k := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y k
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hwk : ContDiff ℝ ∞ wk := by
    rw [hwkFun]
    exact spatialDirectionalJet_contDiff u hu k
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDwk : ContDiff ℝ ∞ (fderiv ℝ wk) := hwk.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hlowerjk : ContDiff ℝ ∞ lowerjk := by
    have hfirst : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ wk y (wj y)) :=
      hDwk.clm_apply hwj
    have hsecond : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ wj y (wk y)) :=
      hDwj.clm_apply hwk
    have hthird : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (Wjk y)) :=
      hDu.clm_apply hWjk
    simpa [lowerjk, secondCoordinateLowerCommutator, u, wj, wk, Wjk] using
      (hfirst.add hsecond).add hthird
  have hm : (fun y ↦ timejk y + transportjk y) =
      (fun y ↦ nu • Δ Wjk y - gradient qjk y - lowerjk y) := by
    funext y
    exact openPeriodicSolutionOn_unforced_secondCoordinateProductionIdentity
      solution ht y j k
  have hderivative := congrArg (fun f : InitialVelocity ↦ fderiv ℝ f x) hm
  change fderiv ℝ (fun y ↦ timejk y + transportjk y) x =
    fderiv ℝ (fun y ↦ nu • Δ Wjk y - gradient qjk y - lowerjk y) x at hderivative
  rw [fderiv_fun_add (htimejk.differentiable (by simp) x)
      (htransportjk.differentiable (by simp) x),
    fderiv_fun_sub
      (((hviscous.const_smul nu).sub hpressure).differentiable (by simp) x)
      (hlowerjk.differentiable (by simp) x),
    fderiv_fun_sub ((hviscous.const_smul nu).differentiable (by simp) x)
      (hpressure.differentiable (by simp) x),
    fderiv_fun_const_smul (hviscous.differentiable (by simp) x) nu] at hderivative
  have happly := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hderivative
  simpa [u, Wjk, qjk, timejk, transportjk, lowerjk] using happly

/-- The six derivative faces obtained from the three lower order-two products.  The seventh lower
face comes from differentiating top transport and is added in `thirdCoordinateLowerCommutator`. -/
theorem openPeriodicSolutionOn_fderiv_secondCoordinateLowerCommutator_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    fderiv ℝ (fun y ↦ secondCoordinateLowerCommutator velocity t j k y) x
        (spatialBasisVector i) =
      fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
          (firstCoordinateJet velocity j x t) +
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
          (secondCoordinateJet velocity i j x t) +
      fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
          (firstCoordinateJet velocity k x t) +
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
          (secondCoordinateJet velocity i k x t) +
      fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
          (secondCoordinateJet velocity j k x t) +
      fderiv ℝ (fun y ↦ velocity y t) x
          (thirdCoordinateJet velocity i j k x t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let wk : InitialVelocity := fun y ↦ firstCoordinateJet velocity k y t
  let Wij : InitialVelocity := fun y ↦ secondCoordinateJet velocity i j y t
  let Wik : InitialVelocity := fun y ↦ secondCoordinateJet velocity i k y t
  let Wjk : InitialVelocity := fun y ↦ secondCoordinateJet velocity j k y t
  let V : InitialVelocity := fun y ↦ thirdCoordinateJet velocity i j k y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hwiFun : wi = spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hwjFun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hwkFun : wk = spatialDirectionalJet u k := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y k
  have hWijFun : Wij = spatialDirectionalJet wj i := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
      solution ht y i j
  have hWikFun : Wik = spatialDirectionalJet wk i := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
      solution ht y i k
  have hWjkFun : Wjk = secondSpatialCoordinateJet u j k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y j k
  have hVFun : V = spatialDirectionalJet Wjk i := by
    funext y
    exact openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
      solution ht y i j k
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hwk : ContDiff ℝ ∞ wk := by
    rw [hwkFun]
    exact spatialDirectionalJet_contDiff u hu k
  have hWjk : ContDiff ℝ ∞ Wjk := by
    rw [hWjkFun]
    exact secondSpatialCoordinateJet_contDiff u hu j k
  have hfirst := fderiv_jacobianAction_eq_transport_add_lower
    wk wj (hwk.of_le (WithTop.coe_le_coe.mpr le_top))
      (hwj.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hsecond := fderiv_jacobianAction_eq_transport_add_lower
    wj wk (hwj.of_le (WithTop.coe_le_coe.mpr le_top))
      (hwk.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hthird := fderiv_jacobianAction_eq_transport_add_lower
    u Wjk (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (hWjk.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hwiDerivative : fderiv ℝ u x (spatialBasisVector i) = wi x := by
    simpa [spatialDirectionalJet] using congrFun hwiFun x |>.symm
  have hWijDerivative : fderiv ℝ wj x (spatialBasisVector i) = Wij x := by
    simpa [spatialDirectionalJet] using congrFun hWijFun x |>.symm
  have hWikDerivative : fderiv ℝ wk x (spatialBasisVector i) = Wik x := by
    simpa [spatialDirectionalJet] using congrFun hWikFun x |>.symm
  have hVDerivative : fderiv ℝ Wjk x (spatialBasisVector i) = V x := by
    simpa [spatialDirectionalJet] using congrFun hVFun x |>.symm
  have hfirstActual :
      fderiv ℝ (fun y ↦ fderiv ℝ wk y (wj y)) x (spatialBasisVector i) =
        fderiv ℝ Wik x (wj x) + fderiv ℝ wk x (Wij x) := by
    rw [← hWikFun, hWijDerivative] at hfirst
    exact hfirst
  have hsecondActual :
      fderiv ℝ (fun y ↦ fderiv ℝ wj y (wk y)) x (spatialBasisVector i) =
        fderiv ℝ Wij x (wk x) + fderiv ℝ wj x (Wik x) := by
    rw [← hWijFun, hWikDerivative] at hsecond
    exact hsecond
  have hthirdActual :
      fderiv ℝ (fun y ↦ fderiv ℝ u y (Wjk y)) x (spatialBasisVector i) =
        fderiv ℝ wi x (Wjk x) + fderiv ℝ u x (V x) := by
    rw [← hwiFun, hVDerivative] at hthird
    exact hthird
  have hDwk : ContDiff ℝ ∞ (fderiv ℝ wk) := hwk.fderiv_right (by simp)
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have htermOne : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ wk y (wj y)) :=
    hDwk.clm_apply hwj
  have htermTwo : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ wj y (wk y)) :=
    hDwj.clm_apply hwk
  have htermThree : ContDiff ℝ ∞ (fun y ↦ fderiv ℝ u y (Wjk y)) :=
    hDu.clm_apply hWjk
  change fderiv ℝ
      (fun y ↦ (fderiv ℝ wk y (wj y) + fderiv ℝ wj y (wk y)) +
        fderiv ℝ u y (Wjk y)) x (spatialBasisVector i) = _
  rw [fderiv_fun_add ((htermOne.add htermTwo).differentiable (by simp) x)
      (htermThree.differentiable (by simp) x),
    fderiv_fun_add (htermOne.differentiable (by simp) x)
      (htermTwo.differentiable (by simp) x)]
  simp only [add_apply]
  rw [hfirstActual, hsecondActual, hthirdActual]
  dsimp [u, wi, wj, wk, Wij, Wik, Wjk, V]
  abel

/-- The complete seven-face lower nonlinear population in the ordered third derivative of
`Du(u)`, after top transport of the third jet is separated. -/
def thirdCoordinateLowerCommutator
    (velocity : VelocityField) (t : ℝ) (i j k : Fin 3) (x : Space) : Space :=
  fderiv ℝ (fun y ↦ secondCoordinateJet velocity j k y t) x
      (firstCoordinateJet velocity i x t) +
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
      (firstCoordinateJet velocity j x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
      (secondCoordinateJet velocity i j x t) +
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
      (firstCoordinateJet velocity k x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
      (secondCoordinateJet velocity i k x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
      (secondCoordinateJet velocity j k x t) +
    fderiv ℝ (fun y ↦ velocity y t) x
      (thirdCoordinateJet velocity i j k x t)

/-- Exact pointwise production equation for one actual ordered third-coordinate word. -/
theorem openPeriodicSolutionOn_unforced_thirdCoordinateProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j k : Fin 3) :
    eulerianTimeJet (thirdCoordinateJet velocity i j k) x t +
        fderiv ℝ (fun y ↦ thirdCoordinateJet velocity i j k y t) x
          (velocity x t) =
      nu • Δ (fun y ↦ thirdCoordinateJet velocity i j k y t) x -
        gradient (thirdPressureCoordinateJet (fun y ↦ pressure y t) i j k) x -
        thirdCoordinateLowerCommutator velocity t i j k x := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let Wjk : InitialVelocity := fun y ↦ secondCoordinateJet velocity j k y t
  let V : InitialVelocity := fun y ↦ thirdCoordinateJet velocity i j k y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hwiFun : wi = spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hWjkFun : Wjk = secondSpatialCoordinateJet u j k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y j k
  have hVFun : V = spatialDirectionalJet Wjk i := by
    funext y
    exact openPeriodicSolutionOn_thirdCoordinateJet_eq_spatialDerivative_secondCoordinateJet
      solution ht y i j k
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hWjk : ContDiff ℝ ∞ Wjk := by
    rw [hWjkFun]
    exact secondSpatialCoordinateJet_contDiff u hu j k
  have hm := openPeriodicSolutionOn_unforced_thirdSpatialDerivative_momentum
    solution ht x i j k
  have htransport := fderiv_jacobianAction_eq_transport_add_lower
    Wjk u (hWjk.of_le (WithTop.coe_le_coe.mpr le_top))
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hviscous := fderiv_laplacian_apply_eq_laplacian_spatialDirectionalJet
    Wjk hWjk x i
  have hpressure := gradient_thirdPressureCoordinateJet_eq_fderiv_secondPressureGradient
    p hp x i j k
  have htime := openPeriodicSolutionOn_eulerianTimeJet_thirdCoordinateJet_eq
    solution ht x i j k
  have hlower := openPeriodicSolutionOn_fderiv_secondCoordinateLowerCommutator_eq
    solution ht x i j k
  have hwiDerivative : fderiv ℝ u x (spatialBasisVector i) = wi x := by
    simpa [spatialDirectionalJet] using congrFun hwiFun x |>.symm
  have hVDerivative : fderiv ℝ Wjk x (spatialBasisVector i) = V x := by
    simpa [spatialDirectionalJet] using congrFun hVFun x |>.symm
  have htransportActual :
      fderiv ℝ (fun y ↦ fderiv ℝ Wjk y (u y)) x (spatialBasisVector i) =
        fderiv ℝ V x (u x) + fderiv ℝ Wjk x (wi x) := by
    rw [← hVFun, hwiDerivative] at htransport
    exact htransport
  have hviscousActual :
      fderiv ℝ (Δ Wjk) x (spatialBasisVector i) = Δ V x := by
    rw [hviscous, ← hVFun]
  dsimp [u, Wjk] at htransportActual
  dsimp [Wjk, V] at hviscousActual
  rw [htransportActual, hviscousActual, ← hpressure, hlower] at hm
  let tail : Space :=
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i k y t) x
        (firstCoordinateJet velocity j x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity k y t) x
        (secondCoordinateJet velocity i j x t) +
    fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x
        (firstCoordinateJet velocity k x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
        (secondCoordinateJet velocity i k x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
        (secondCoordinateJet velocity j k x t) +
    fderiv ℝ (fun y ↦ velocity y t) x
        (thirdCoordinateJet velocity i j k x t)
  have hmadd := congrArg (fun z : Space ↦ z + tail) hm
  dsimp [u, wi, Wjk, V, p] at hmadd htime ⊢
  rw [htime]
  apply eq_sub_iff_add_eq.mpr
  simpa [thirdCoordinateLowerCommutator, tail, add_assoc] using hmadd

/-! ## Periodic cancellation and viscous cube integration by parts -/

/-- Exact mixed pressure cancellation for one ordered third-coordinate word. -/
theorem openPeriodicSolutionOn_integral_thirdCoordinatePressureWork_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (gradient (thirdPressureCoordinateJet (fun y ↦ pressure y t) i j k) x)
        (thirdCoordinateJet velocity i j k x t) = 0 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hVfun : (fun x ↦ thirdCoordinateJet velocity i j k x t) =
      thirdSpatialCoordinateJet u i j k := by
    funext x
    exact openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
      solution ht x i j k
  have hVpoint : ∀ x,
      thirdCoordinateJet velocity i j k x t = thirdSpatialCoordinateJet u i j k x :=
    fun x ↦ congrFun hVfun x
  simp_rw [hVpoint]
  apply integral_pressureWork_unitCube_eq_zero
  · exact (thirdSpatialCoordinateJet_contDiff u hu i j k).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact (thirdPressureCoordinateJet_contDiff p hp i j k).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact thirdSpatialCoordinateJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i j k
  · exact thirdPressureCoordinateJet_isOnePeriodic p
      (solution.pressurePeriodic t ⟨ht.1.le, ht.2⟩) i j k
  · exact fun x ↦ divergence_thirdSpatialCoordinateJet_eq_zero u hu
      (fun y ↦ solution.incompressible y t ⟨ht.1.le, ht.2⟩) x i j k

/-- Exact viscous cube integration by parts for one actual ordered third-coordinate word. -/
theorem openPeriodicSolutionOn_integral_thirdCoordinateViscousWork_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y ↦ thirdCoordinateJet velocity i j k y t) x)
        (thirdCoordinateJet velocity i j k x t) =
      -∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ thirdCoordinateJet velocity i j k y t component) x‖ ^ 2 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hVfun : (fun x ↦ thirdCoordinateJet velocity i j k x t) =
      thirdSpatialCoordinateJet u i j k := by
    funext x
    exact openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
      solution ht x i j k
  have hVpoint : ∀ x,
      thirdCoordinateJet velocity i j k x t = thirdSpatialCoordinateJet u i j k x :=
    fun x ↦ congrFun hVfun x
  rw [hVfun]
  simp_rw [hVpoint]
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · exact (thirdSpatialCoordinateJet_contDiff u hu i j k).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact thirdSpatialCoordinateJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i j k

/-- Top transport of every actual ordered third-coordinate jet cancels. -/
theorem openPeriodicSolutionOn_integral_thirdCoordinateTransport_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ thirdCoordinateJet velocity i j k y t) x (velocity x t))
        (thirdCoordinateJet velocity i j k x t) = 0 := by
  simpa [thirdCoordinateJet, thirdCoordinateWord, coordinateJetField] using
    openPeriodicSolutionOn_integral_coordinateJetTransport_eq_zero
      solution ht 3 (thirdCoordinateWord i j k)

/-! ## Integrated production for one ordered triple -/

/-- For one actual order-three word, every term in the pointwise production equation is
integrable on the cube and the three periodic cancellations give the exact energy identity. -/
theorem openPeriodicSolutionOn_unforced_integral_thirdCoordinateProduction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j k : Fin 3) :
    (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t)
          (thirdCoordinateJet velocity i j k x t)) =
      -nu * (∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ thirdCoordinateJet velocity i j k y t component) x‖ ^ 2) -
      ∫ x in unitCube,
        inner ℝ (thirdCoordinateLowerCommutator velocity t i j k x)
          (thirdCoordinateJet velocity i j k x t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let wk : InitialVelocity := fun y ↦ firstCoordinateJet velocity k y t
  let Wij : InitialVelocity := fun y ↦ secondCoordinateJet velocity i j y t
  let Wik : InitialVelocity := fun y ↦ secondCoordinateJet velocity i k y t
  let Wjk : InitialVelocity := fun y ↦ secondCoordinateJet velocity j k y t
  let V : InitialVelocity := fun y ↦ thirdCoordinateJet velocity i j k y t
  let q : Space → ℝ :=
    thirdPressureCoordinateJet (fun y ↦ pressure y t) i j k
  let lower : InitialVelocity := fun x ↦ thirdCoordinateLowerCommutator velocity t i j k x
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hwiFun : wi = spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hwjFun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hwkFun : wk = spatialDirectionalJet u k := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y k
  have hWijFun : Wij = secondSpatialCoordinateJet u i j := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y i j
  have hWikFun : Wik = secondSpatialCoordinateJet u i k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y i k
  have hWjkFun : Wjk = secondSpatialCoordinateJet u j k := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y j k
  have hVFun : V = thirdSpatialCoordinateJet u i j k := by
    funext y
    exact openPeriodicSolutionOn_thirdCoordinateJet_eq_thirdSpatialCoordinateJet
      solution ht y i j k
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hwk : ContDiff ℝ ∞ wk := by
    rw [hwkFun]
    exact spatialDirectionalJet_contDiff u hu k
  have hWij : ContDiff ℝ ∞ Wij := by
    rw [hWijFun]
    exact secondSpatialCoordinateJet_contDiff u hu i j
  have hWik : ContDiff ℝ ∞ Wik := by
    rw [hWikFun]
    exact secondSpatialCoordinateJet_contDiff u hu i k
  have hWjk : ContDiff ℝ ∞ Wjk := by
    rw [hWjkFun]
    exact secondSpatialCoordinateJet_contDiff u hu j k
  have hV : ContDiff ℝ ∞ V := by
    rw [hVFun]
    exact thirdSpatialCoordinateJet_contDiff u hu i j k
  have hp : ContDiff ℝ ∞ (fun y ↦ pressure y t) :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hq : ContDiff ℝ ∞ q :=
    thirdPressureCoordinateJet_contDiff (fun y ↦ pressure y t) hp i j k
  have hDwi : ContDiff ℝ ∞ (fderiv ℝ wi) := hwi.fderiv_right (by simp)
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDwk : ContDiff ℝ ∞ (fderiv ℝ wk) := hwk.fderiv_right (by simp)
  have hDWij : ContDiff ℝ ∞ (fderiv ℝ Wij) := hWij.fderiv_right (by simp)
  have hDWik : ContDiff ℝ ∞ (fderiv ℝ Wik) := hWik.fderiv_right (by simp)
  have hDWjk : ContDiff ℝ ∞ (fderiv ℝ Wjk) := hWjk.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hlower : ContDiff ℝ ∞ lower := by
    have hfirst : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ Wjk x (wi x)) :=
      hDWjk.clm_apply hwi
    have hsecond : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ Wik x (wj x)) :=
      hDWik.clm_apply hwj
    have hthird : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wk x (Wij x)) :=
      hDwk.clm_apply hWij
    have hfourth : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ Wij x (wk x)) :=
      hDWij.clm_apply hwk
    have hfifth : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wj x (Wik x)) :=
      hDwj.clm_apply hWik
    have hsixth : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wi x (Wjk x)) :=
      hDwi.clm_apply hWjk
    have hseventh : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ u x (V x)) :=
      hDu.clm_apply hV
    simpa [lower, thirdCoordinateLowerCommutator, u, wi, wj, wk, Wij, Wik, Wjk, V] using
      ((((((hfirst.add hsecond).add hthird).add hfourth).add hfifth).add hsixth).add hseventh)
  have hfield : ContDiffOn ℝ ∞
      (Function.uncurry (thirdCoordinateJet velocity i j k))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    simpa [thirdCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 3 (thirdCoordinateWord i j k)
  have htimeContinuous : Continuous (fun x ↦
      inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_openSlab
      (thirdCoordinateJet velocity i j k) hfield ht.1 ht.2).inner hV.continuous
  have htransportContinuous : Continuous (fun x ↦
      inner ℝ (fderiv ℝ V x (u x)) (V x)) := by
    have htransported : Continuous (fun x ↦ fderiv ℝ V x (u x)) :=
      (hV.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hu.continuous)
    exact htransported.inner hV.continuous
  have hlowerContinuous : Continuous (fun x ↦ inner ℝ (lower x) (V x)) :=
    hlower.continuous.inner hV.continuous
  have hpressureContinuous : Continuous (fun x ↦
      inner ℝ (gradient q x) (V x)) :=
    (gradient_contDiff_one q (hq.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hV.continuous
  have htimeInt : IntegrableOn (fun x ↦
      inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x)) unitCube :=
    htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have htransportInt : IntegrableOn (fun x ↦
      inner ℝ (fderiv ℝ V x (u x)) (V x)) unitCube :=
    htransportContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hlowerInt : IntegrableOn (fun x ↦ inner ℝ (lower x) (V x)) unitCube :=
    hlowerContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hpressureInt : IntegrableOn (fun x ↦
      inner ℝ (gradient q x) (V x)) unitCube :=
    hpressureContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x ↦ inner ℝ (Δ V x) (V x)) unitCube :=
    integrableOn_inner_laplacian_unitCube V
      (hV.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpoint : ∀ x,
      inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x) +
          inner ℝ (fderiv ℝ V x (u x)) (V x) =
        nu * inner ℝ (Δ V x) (V x) - inner ℝ (gradient q x) (V x) -
          inner ℝ (lower x) (V x) := by
    intro x
    have hpde := openPeriodicSolutionOn_unforced_thirdCoordinateProductionIdentity
      solution ht x i j k
    have hinner := congrArg (fun z : Space ↦ inner ℝ z (V x)) hpde
    simpa [u, V, q, lower, inner_add_left, inner_sub_left, real_inner_smul_left] using hinner
  have hintegrated :
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ V x (u x)) (V x) =
        nu * (∫ x in unitCube, inner ℝ (Δ V x) (V x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (V x)) -
          ∫ x in unitCube, inner ℝ (lower x) (V x) := by
    calc
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ V x (u x)) (V x) =
        ∫ x in unitCube,
          (inner ℝ (eulerianTimeJet (thirdCoordinateJet velocity i j k) x t) (V x) +
            inner ℝ (fderiv ℝ V x (u x)) (V x)) :=
          (integral_add htimeInt htransportInt).symm
      _ = ∫ x in unitCube,
          ((nu * inner ℝ (Δ V x) (V x) - inner ℝ (gradient q x) (V x)) -
            inner ℝ (lower x) (V x)) := by
        apply setIntegral_congr_fun hcubeMeasurable
        intro x _hx
        exact hpoint x
      _ = (∫ x in unitCube,
          (nu * inner ℝ (Δ V x) (V x) - inner ℝ (gradient q x) (V x))) -
          ∫ x in unitCube, inner ℝ (lower x) (V x) :=
        integral_sub ((hviscousInt.const_mul nu).sub hpressureInt) hlowerInt
      _ = ((∫ x in unitCube, nu * inner ℝ (Δ V x) (V x)) -
          ∫ x in unitCube, inner ℝ (gradient q x) (V x)) -
          ∫ x in unitCube, inner ℝ (lower x) (V x) := by
        rw [integral_sub (hviscousInt.const_mul nu) hpressureInt]
      _ = nu * (∫ x in unitCube, inner ℝ (Δ V x) (V x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (V x)) -
          ∫ x in unitCube, inner ℝ (lower x) (V x) := by
        rw [integral_const_mul]
  have htransportZero :=
    openPeriodicSolutionOn_integral_thirdCoordinateTransport_eq_zero
      solution ht i j k
  have hpressureZero :=
    openPeriodicSolutionOn_integral_thirdCoordinatePressureWork_eq_zero
      solution ht i j k
  have hviscous :=
    openPeriodicSolutionOn_integral_thirdCoordinateViscousWork_eq
      solution ht i j k
  dsimp [u, wi, wj, wk, Wij, Wik, Wjk, V, q, lower] at hintegrated ⊢
  rw [htransportZero, hpressureZero, hviscous] at hintegrated
  linarith

/-! ## The complete twenty-seven-word order-three population -/

/-- Exactly the `n = 3` summand inside `coordinateH3TimeWork`. -/
def coordinateH3OrderTimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (eulerianTimeJet (coordinateJetField velocity 3 word) x t)
        (coordinateJet velocity 3 word x t)

def coordinateH3OrderDissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    ∫ x in unitCube, ∑ component : Fin 3,
      ‖gradient (fun y ↦ coordinateJet velocity 3 word y t component) x‖ ^ 2

/-- All seven lower nonlinear faces for every ordered third-coordinate word. -/
def coordinateH3OrderLowerWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 3 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (thirdCoordinateLowerCommutator velocity t (word 0) (word 1) (word 2) x)
        (coordinateJet velocity 3 word x t)

/-- **Exact twenty-seven-word order-three production law.** -/
theorem openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_eq_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH3OrderTimeWork velocity t =
      -nu * coordinateH3OrderDissipation velocity t -
        coordinateH3OrderLowerWork velocity t := by
  have hword : ∀ word : Fin 3 → Fin 3,
      (∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 3 word) x t)
            (coordinateJet velocity 3 word x t)) =
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 3 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (thirdCoordinateLowerCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (coordinateJet velocity 3 word x t) := by
    intro word
    have hwordEq : word = thirdCoordinateWord (word 0) (word 1) (word 2) := by
      funext q
      fin_cases q <;> rfl
    rw [hwordEq]
    convert openPeriodicSolutionOn_unforced_integral_thirdCoordinateProduction
      solution ht (word 0) (word 1) (word 2) using 1 <;> rfl
  unfold coordinateH3OrderTimeWork coordinateH3OrderDissipation
    coordinateH3OrderLowerWork
  calc
    (∑ word : Fin 3 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 3 word) x t)
            (coordinateJet velocity 3 word x t)) =
      ∑ word : Fin 3 → Fin 3,
        (-nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 3 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (thirdCoordinateLowerCommutator velocity t
              (word 0) (word 1) (word 2) x)
            (coordinateJet velocity 3 word x t)) := by
      apply Finset.sum_congr rfl
      intro word _hword
      exact hword word
    _ = (∑ word : Fin 3 → Fin 3,
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 3 word y t component) x‖ ^ 2)) -
        ∑ word : Fin 3 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (thirdCoordinateLowerCommutator velocity t
                (word 0) (word 1) (word 2) x)
              (coordinateJet velocity 3 word x t) := by
      rw [Finset.sum_sub_distrib]
    _ = -nu * (∑ word : Fin 3 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 3 word y t component) x‖ ^ 2) -
        ∑ word : Fin 3 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (thirdCoordinateLowerCommutator velocity t
                (word 0) (word 1) (word 2) x)
              (coordinateJet velocity 3 word x t) := by
      rw [Finset.mul_sum]

/-! ## Exact decomposition of the forty-word time-work population -/

/-- The unique empty word, i.e. the `n = 0` slice of `coordinateH3TimeWork`. -/
def coordinateH0TimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 0 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (eulerianTimeJet (coordinateJetField velocity 0 word) x t)
        (coordinateJet velocity 0 word x t)

/-- The complete forty-word time work is exactly its `1 + 3 + 9 + 27` ordered-word slices. -/
theorem coordinateH3TimeWork_eq_orderSlices
    (velocity : VelocityField) (t : ℝ) :
    coordinateH3TimeWork velocity t =
      coordinateH0TimeWork velocity t +
        coordinateH1TimeWork velocity t +
        coordinateH2TimeWork velocity t +
        coordinateH3OrderTimeWork velocity t := by
  simp [coordinateH3TimeWork, coordinateH0TimeWork, coordinateH1TimeWork,
    coordinateH2TimeWork, coordinateH3OrderTimeWork, Fin.sum_univ_succ, add_assoc]

section Audit

#print axioms thirdCoordinateJet_eq_nestedSecond_of_contDiffAt
#print axioms openPeriodicSolutionOn_eulerianTimeJet_thirdCoordinateJet_eq
#print axioms openPeriodicSolutionOn_fderiv_secondCoordinateLowerCommutator_eq
#print axioms openPeriodicSolutionOn_unforced_thirdCoordinateProductionIdentity
#print axioms openPeriodicSolutionOn_integral_thirdCoordinatePressureWork_eq_zero
#print axioms openPeriodicSolutionOn_integral_thirdCoordinateViscousWork_eq
#print axioms openPeriodicSolutionOn_unforced_integral_thirdCoordinateProduction
#print axioms openPeriodicSolutionOn_unforced_coordinateH3OrderTimeWork_eq_production
#print axioms coordinateH3TimeWork_eq_orderSlices

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateH3Production

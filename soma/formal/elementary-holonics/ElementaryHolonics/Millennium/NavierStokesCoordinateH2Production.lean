import ElementaryHolonics.Millennium.NavierStokesCoordinateH1Production

/-!
# The nine second-coordinate words of the periodic quadratic production law

This successor differentiates the actual unforced momentum return through every ordered pair of
spatial basis directions.  It retains the complete lower nonlinear population, cancels top
transport and mixed pressure work on the periodic cube, and integrates viscosity by parts.

The returned theorem is exactly the `n = 2` slice of `coordinateH3TimeWork`.  The twenty-seven
order-three words are outside this owner.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH2Production

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
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The ordered two-letter coordinate word `(i,j)`. -/
def secondCoordinateWord (i j : Fin 3) : Fin 2 → Fin 3 := ![i, j]

/-- The actual order-two joint coordinate jet. -/
def secondCoordinateJet (velocity : VelocityField) (i j : Fin 3) : VelocityField :=
  coordinateJetField velocity 2 (secondCoordinateWord i j)

/-- The corresponding ordered second spatial derivative. -/
def secondSpatialCoordinateJet (u : InitialVelocity) (i j : Fin 3) : InitialVelocity :=
  spatialDirectionalJet (spatialDirectionalJet u j) i

/-- At an interior solution occurrence, the actual joint two-letter word is the spatial derivative
of the actual first-coordinate jet addressed by its second letter. -/
theorem openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    secondCoordinateJet velocity i j x t =
      spatialDirectionalJet (fun y ↦ firstCoordinateJet velocity j y t) i x := by
  let F : Space × ℝ → Space := Function.uncurry velocity
  let ei : Space × ℝ := jointSpatialBasisDirection i
  let ej : Space × ℝ := jointSpatialBasisDirection j
  have hvelocity : ContDiffOn ℝ ∞ F
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hdomain :
      Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
        nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hfield : ContDiffAt ℝ 2 F (x, t) :=
    (hvelocity.contDiffAt hdomain).of_le (WithTop.coe_le_coe.mpr le_top)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (x, t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfixed : DifferentiableAt ℝ (fun z ↦ fderiv ℝ F z ej) (x, t) :=
    hDF.clm_apply (differentiableAt_const ej)
  have hfixedFDeriv := fderiv_clm_apply hDF (differentiableAt_const ej)
  have hslice := hfixed.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have hsliceApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hslice.fderiv
  have hfixedApply := congrArg
    (fun L : (Space × ℝ) →L[ℝ] Space ↦ L ei) hfixedFDeriv
  change iteratedFDeriv ℝ 2 F (x, t)
      (coordinateWordDirections (secondCoordinateWord i j)) =
    fderiv ℝ (fun y ↦
      iteratedFDeriv ℝ 1 F (y, t)
        (coordinateWordDirections (firstCoordinateWord j))) x (spatialBasisVector i)
  rw [iteratedFDeriv_two_apply]
  have hdirectionZero :
      coordinateWordDirections (secondCoordinateWord i j) 0 = ei := by
    simp [secondCoordinateWord, coordinateWordDirections, ei]
  have hdirectionOne :
      coordinateWordDirections (secondCoordinateWord i j) 1 = ej := by
    simp [secondCoordinateWord, coordinateWordDirections, ej]
  rw [hdirectionZero, hdirectionOne]
  have hleft :
      fderiv ℝ (fderiv ℝ F) (x, t) ei ej =
        fderiv ℝ (fun z ↦ fderiv ℝ F z ej) (x, t) ei := by
    simpa using hfixedApply.symm
  rw [hleft]
  have hright :
      fderiv ℝ (fun y ↦ fderiv ℝ F (y, t) ej) x (spatialBasisVector i) =
        fderiv ℝ (fun z ↦ fderiv ℝ F z ej) (x, t) ei := by
    simpa [ei, jointSpatialBasisDirection, spatialInclusion, Function.comp_def] using
      hsliceApply
  rw [← hright]
  congr 2
  funext y
  simp [ej, firstCoordinateWord, coordinateWordDirections,
    jointSpatialBasisDirection, iteratedFDeriv_one_apply]

/-- Consequently the two-letter joint word is exactly the nested spatial derivative of the
fixed-time velocity slice. -/
theorem openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    secondCoordinateJet velocity i j x t =
      secondSpatialCoordinateJet (fun y ↦ velocity y t) i j x := by
  rw [openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
    solution ht x i j]
  have hfirst : (fun y ↦ firstCoordinateJet velocity j y t) =
      spatialDirectionalJet (fun y ↦ velocity y t) j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  rw [hfirst]
  rfl

theorem secondSpatialCoordinateJet_contDiff
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (i j : Fin 3) :
    ContDiff ℝ ∞ (secondSpatialCoordinateJet u i j) := by
  exact spatialDirectionalJet_contDiff (spatialDirectionalJet u j)
    (spatialDirectionalJet_contDiff u hu j) i

theorem secondSpatialCoordinateJet_isOnePeriodic
    (u : InitialVelocity) (hu : IsOnePeriodic u) (i j : Fin 3) :
    IsOnePeriodic (secondSpatialCoordinateJet u i j) := by
  exact spatialDirectionalJet_isOnePeriodic (spatialDirectionalJet u j)
    (spatialDirectionalJet_isOnePeriodic u hu j) i

/-- Twice differentiating the actual incompressibility identity keeps every ordered second word
divergence-free. -/
theorem divergence_secondSpatialCoordinateJet_eq_zero
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) (i j : Fin 3) :
    divergence (secondSpatialCoordinateJet u i j) x = 0 := by
  let first := spatialDirectionalJet u j
  have hfirstSmooth : ContDiff ℝ ∞ first := spatialDirectionalJet_contDiff u hu j
  have hfirstDiv : ∀ y, divergence first y = 0 := fun y ↦
    divergence_spatialDirectionalJet_eq_zero u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) hdiv y j
  exact divergence_spatialDirectionalJet_eq_zero first
    (hfirstSmooth.of_le (WithTop.coe_le_coe.mpr le_top)) hfirstDiv x i

/-- The ordered second scalar pressure jet matching `(i,j)`. -/
def secondPressureCoordinateJet (p : Space → ℝ) (i j : Fin 3) : Space → ℝ :=
  pressureDirectionalJet (pressureDirectionalJet p j) i

theorem secondPressureCoordinateJet_contDiff
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (i j : Fin 3) :
    ContDiff ℝ ∞ (secondPressureCoordinateJet p i j) := by
  exact pressureDirectionalJet_contDiff (pressureDirectionalJet p j)
    (pressureDirectionalJet_contDiff p hp j) i

theorem secondPressureCoordinateJet_isOnePeriodic
    (p : Space → ℝ) (hp : IsOnePeriodic p) (i j : Fin 3) :
    IsOnePeriodic (secondPressureCoordinateJet p i j) := by
  exact pressureDirectionalJet_isOnePeriodic (pressureDirectionalJet p j)
    (pressureDirectionalJet_isOnePeriodic p hp j) i

/-- Mixed symmetry turns the derivative of the first pressure-gradient face into the gradient of
the ordered second scalar pressure jet. -/
theorem gradient_secondPressureCoordinateJet_eq_fderiv_firstPressureGradient
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (x : Space) (i j : Fin 3) :
    gradient (secondPressureCoordinateJet p i j) x =
      fderiv ℝ (gradient (pressureDirectionalJet p j)) x (spatialBasisVector i) := by
  exact gradient_pressureDirectionalJet_eq_fderiv_gradient
    (pressureDirectionalJet p j)
    ((pressureDirectionalJet_contDiff p hp j).of_le
      (WithTop.coe_le_coe.mpr le_top)) x i

/-- A general differentiated Jacobian action.  The first term is top transport of the addressed
coordinate derivative; the second is the complete lower product face. -/
theorem fderiv_jacobianAction_eq_transport_add_lower
    (carried transport : InitialVelocity)
    (hcarried : ContDiff ℝ 2 carried) (htransport : ContDiff ℝ 1 transport)
    (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y ↦ fderiv ℝ carried y (transport y)) x (spatialBasisVector i) =
      fderiv ℝ (spatialDirectionalJet carried i) x (transport x) +
        fderiv ℝ carried x
          (fderiv ℝ transport x (spatialBasisVector i)) := by
  let e : Space := spatialBasisVector i
  have hDcarried : DifferentiableAt ℝ (fderiv ℝ carried) x :=
    (hcarried.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have htransportDiff : DifferentiableAt ℝ transport x :=
    htransport.differentiable (by norm_num) x
  have haction := fderiv_clm_apply hDcarried htransportDiff
  have hactionApply := congrArg (fun L : Space →L[ℝ] Space ↦ L e) haction
  have hcoordinate := fderiv_clm_apply hDcarried (differentiableAt_const e)
  have hcoordinateApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (transport x)) hcoordinate
  have hactionApplySimple :
      fderiv ℝ (fun y ↦ fderiv ℝ carried y (transport y)) x e =
        fderiv ℝ carried x (fderiv ℝ transport x e) +
          fderiv ℝ (fderiv ℝ carried) x e (transport x) := by
    simpa using hactionApply
  have hcoordinateApplySimple :
      fderiv ℝ (fun y ↦ fderiv ℝ carried y e) x (transport x) =
        fderiv ℝ (fderiv ℝ carried) x (transport x) e := by
    simpa using hcoordinateApply
  have hsymm : IsSymmSndFDerivAt ℝ carried x :=
    hcarried.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change fderiv ℝ (fun y ↦ fderiv ℝ carried y (transport y)) x e =
    fderiv ℝ (fun y ↦ fderiv ℝ carried y e) x (transport x) +
      fderiv ℝ carried x (fderiv ℝ transport x e)
  rw [hactionApplySimple, hcoordinateApplySimple, hsymm.eq e (transport x)]
  abel

/-! ## Joint time and second spatial differentiation -/

/-- At a genuine second-derivative occurrence, the two-letter jet is the nested first-coordinate
jet, in the same ordered directions. -/
theorem secondCoordinateJet_eq_nestedFirst_of_contDiffAt
    (field : VelocityField) (x : Space) (t : ℝ) (i j : Fin 3)
    (hfield : ContDiffAt ℝ 2 (Function.uncurry field) (x, t)) :
    secondCoordinateJet field i j x t =
      firstCoordinateJet (firstCoordinateJet field j) i x t := by
  let F : Space × ℝ → Space := Function.uncurry field
  let ei : Space × ℝ := jointSpatialBasisDirection i
  let ej : Space × ℝ := jointSpatialBasisDirection j
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (x, t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfixed := fderiv_clm_apply hDF (differentiableAt_const ej)
  have hfixedApply := congrArg
    (fun L : (Space × ℝ) →L[ℝ] Space ↦ L ei) hfixed
  change iteratedFDeriv ℝ 2 F (x, t)
      (coordinateWordDirections (secondCoordinateWord i j)) =
    iteratedFDeriv ℝ 1
      (fun z ↦ iteratedFDeriv ℝ 1 F z
        (coordinateWordDirections (firstCoordinateWord j))) (x, t)
      (coordinateWordDirections (firstCoordinateWord i))
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_one_apply]
  have hdirectionZero :
      coordinateWordDirections (secondCoordinateWord i j) 0 = ei := by
    simp [secondCoordinateWord, coordinateWordDirections, ei]
  have hdirectionOne :
      coordinateWordDirections (secondCoordinateWord i j) 1 = ej := by
    simp [secondCoordinateWord, coordinateWordDirections, ej]
  have hfirstI : coordinateWordDirections (firstCoordinateWord i) = fun _ ↦ ei := by
    funext k
    fin_cases k
    simp [firstCoordinateWord, coordinateWordDirections, ei]
  have hfirstJ : coordinateWordDirections (firstCoordinateWord j) = fun _ ↦ ej := by
    funext k
    fin_cases k
    simp [firstCoordinateWord, coordinateWordDirections, ej]
  rw [hdirectionZero, hdirectionOne, hfirstI, hfirstJ]
  simpa [iteratedFDeriv_one_apply] using hfixedApply.symm

/-- The Eulerian time jet in the actual two-letter `coordinateH3TimeWork` face equals the spatial
derivative of the actual first-coordinate time jet. -/
theorem openPeriodicSolutionOn_eulerianTimeJet_secondCoordinateJet_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    eulerianTimeJet (secondCoordinateJet velocity i j) x t =
      fderiv ℝ
        (fun y ↦ eulerianTimeJet (firstCoordinateJet velocity j) y t) x
        (spatialBasisVector i) := by
  let slab : Set (Space × ℝ) :=
    Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T
  have hopen : IsOpen slab := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) slab := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hfirst : ContDiffOn ℝ ∞
      (Function.uncurry (firstCoordinateJet velocity j)) slab := by
    simpa [firstCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 1 (firstCoordinateWord j)
  have hdomain : slab ∈ nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hfirstAt : ContDiffAt ℝ 2
      (Function.uncurry (firstCoordinateJet velocity j)) (x, t) :=
    (hfirst.contDiffAt hdomain).of_le (WithTop.coe_le_coe.mpr le_top)
  have hmixed := eulerianTimeJet_firstCoordinateJet_eq_fderiv_time_of_contDiffAt
    (firstCoordinateJet velocity j) x t i hfirstAt
  have hlocal :
      Function.uncurry (secondCoordinateJet velocity i j) =ᶠ[nhds (x, t)]
        Function.uncurry (firstCoordinateJet (firstCoordinateJet velocity j) i) := by
    filter_upwards [hdomain] with z hz
    have hzfield : ContDiffAt ℝ 2 (Function.uncurry velocity) z :=
      (hvelocity.contDiffAt (hopen.mem_nhds hz)).of_le
        (WithTop.coe_le_coe.mpr le_top)
    exact secondCoordinateJet_eq_nestedFirst_of_contDiffAt
      velocity z.1 z.2 i j hzfield
  rw [← hmixed]
  unfold eulerianTimeJet
  rw [hlocal.fderiv_eq]

/-! ## The twice-differentiated actual momentum equation -/

/-- Differentiating the already attached first-coordinate production equation in a second basis
direction, before splitting its two Jacobian actions. -/
theorem openPeriodicSolutionOn_unforced_secondSpatialDerivative_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    fderiv ℝ
          (fun y ↦ eulerianTimeJet (firstCoordinateJet velocity j) y t) x
          (spatialBasisVector i) +
        fderiv ℝ
          (fun y ↦ fderiv ℝ (fun z ↦ firstCoordinateJet velocity j z t) y
            (velocity y t)) x (spatialBasisVector i) =
      nu • fderiv ℝ (Δ (fun y ↦ firstCoordinateJet velocity j y t)) x
          (spatialBasisVector i) -
        fderiv ℝ
          (gradient (pressureDirectionalJet (fun y ↦ pressure y t) j)) x
          (spatialBasisVector i) -
        fderiv ℝ
          (fun y ↦ fderiv ℝ (fun z ↦ velocity z t) y
            (firstCoordinateJet velocity j y t)) x (spatialBasisVector i) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let qj : Space → ℝ := pressureDirectionalJet (fun y ↦ pressure y t) j
  let timej : InitialVelocity :=
    fun y ↦ eulerianTimeJet (firstCoordinateJet velocity j) y t
  let transportj : InitialVelocity := fun y ↦ fderiv ℝ wj y (u y)
  let stretchj : InitialVelocity := fun y ↦ fderiv ℝ u y (wj y)
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ (fun y ↦ pressure y t) :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hfirstfun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hfirstfun]
    exact spatialDirectionalJet_contDiff u hu j
  have hqj : ContDiff ℝ ∞ qj :=
    pressureDirectionalJet_contDiff (fun y ↦ pressure y t) hp j
  have hfirstJoint : ContDiffOn ℝ ∞
      (Function.uncurry (firstCoordinateJet velocity j))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    simpa [firstCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 1 (firstCoordinateWord j)
  have htimej : ContDiff ℝ ∞ timej :=
    eulerianTimeJetSlice_contDiff_of_contDiffOn_openSlab
      (firstCoordinateJet velocity j) hfirstJoint ht
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have htransportj : ContDiff ℝ ∞ transportj := hDwj.clm_apply hu
  have hstretchj : ContDiff ℝ ∞ stretchj := hDu.clm_apply hwj
  have hviscous : ContDiff ℝ ∞ (Δ wj) := laplacian_contDiff hwj
  have hpressure : ContDiff ℝ ∞ (gradient qj) := gradient_contDiff hqj
  have hm : (fun y ↦ timej y + transportj y) =
      (fun y ↦ nu • Δ wj y - gradient qj y - stretchj y) := by
    funext y
    exact openPeriodicSolutionOn_unforced_firstCoordinateProductionIdentity
      solution ht y j
  have hderivative := congrArg (fun f : InitialVelocity ↦ fderiv ℝ f x) hm
  change fderiv ℝ (fun y ↦ timej y + transportj y) x =
    fderiv ℝ (fun y ↦ nu • Δ wj y - gradient qj y - stretchj y) x at hderivative
  rw [fderiv_fun_add (htimej.differentiable (by simp) x)
      (htransportj.differentiable (by simp) x),
    fderiv_fun_sub
      (((hviscous.const_smul nu).sub hpressure).differentiable (by simp) x)
      (hstretchj.differentiable (by simp) x),
    fderiv_fun_sub ((hviscous.const_smul nu).differentiable (by simp) x)
      (hpressure.differentiable (by simp) x),
    fderiv_fun_const_smul (hviscous.differentiable (by simp) x) nu] at hderivative
  have happly := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hderivative
  simpa [u, wj, qj, timej, transportj, stretchj] using happly

/-- The complete lower nonlinear population left after top transport is removed from the ordered
second derivative of `Du(u)`. -/
def secondCoordinateLowerCommutator
    (velocity : VelocityField) (t : ℝ) (i j : Fin 3) (x : Space) : Space :=
  fderiv ℝ (fun y ↦ firstCoordinateJet velocity j y t) x
      (firstCoordinateJet velocity i x t) +
    fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x
      (firstCoordinateJet velocity j x t) +
    fderiv ℝ (fun y ↦ velocity y t) x (secondCoordinateJet velocity i j x t)

/-- Exact pointwise production equation for one actual ordered second-coordinate word. -/
theorem openPeriodicSolutionOn_unforced_secondCoordinateProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i j : Fin 3) :
    eulerianTimeJet (secondCoordinateJet velocity i j) x t +
        fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x (velocity x t) =
      nu • Δ (fun y ↦ secondCoordinateJet velocity i j y t) x -
        gradient (secondPressureCoordinateJet (fun y ↦ pressure y t) i j) x -
        secondCoordinateLowerCommutator velocity t i j x := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let W : InitialVelocity := fun y ↦ secondCoordinateJet velocity i j y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hwiFun : wi = spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hwjFun : wj = spatialDirectionalJet u j := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y j
  have hWFun : W = spatialDirectionalJet wj i := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_spatialDerivative_firstCoordinateJet
      solution ht y i j
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hm := openPeriodicSolutionOn_unforced_secondSpatialDerivative_momentum
    solution ht x i j
  have htransport := fderiv_jacobianAction_eq_transport_add_lower
    wj u (hwj.of_le (WithTop.coe_le_coe.mpr le_top))
      (hu.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hstretch := fderiv_jacobianAction_eq_transport_add_lower
    u wj (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (hwj.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hviscous := fderiv_laplacian_apply_eq_laplacian_spatialDirectionalJet
    wj hwj x i
  have hpressure := gradient_secondPressureCoordinateJet_eq_fderiv_firstPressureGradient
    p hp x i j
  have htime := openPeriodicSolutionOn_eulerianTimeJet_secondCoordinateJet_eq
    solution ht x i j
  have hwiPoint : fderiv ℝ u x (spatialBasisVector i) = wi x := by
    simpa [spatialDirectionalJet] using congrFun hwiFun x |>.symm
  have hWPoint : spatialDirectionalJet wj i x = W x :=
    congrFun hWFun x |>.symm
  have hWDerivative : fderiv ℝ wj x (spatialBasisVector i) = W x := by
    simpa [spatialDirectionalJet] using hWPoint
  have htransportActual :
      fderiv ℝ (fun y ↦ fderiv ℝ wj y (u y)) x (spatialBasisVector i) =
        fderiv ℝ W x (u x) + fderiv ℝ wj x (wi x) := by
    rw [← hWFun, hwiPoint] at htransport
    exact htransport
  have hstretchActual :
      fderiv ℝ (fun y ↦ fderiv ℝ u y (wj y)) x (spatialBasisVector i) =
        fderiv ℝ wi x (wj x) + fderiv ℝ u x (W x) := by
    rw [← hwiFun, hWDerivative] at hstretch
    exact hstretch
  have hviscousActual :
      fderiv ℝ (Δ wj) x (spatialBasisVector i) = Δ W x := by
    rw [hviscous, ← hWFun]
  rw [htransportActual, hviscousActual, ← hpressure, hstretchActual] at hm
  let tail : Space := fderiv ℝ wi x (wj x) + fderiv ℝ u x (W x)
  have hmadd := congrArg (fun z : Space ↦ z + tail) hm
  dsimp [u, wi, wj, W, p] at hmadd htime ⊢
  rw [htime]
  apply eq_sub_iff_add_eq.mpr
  simpa [secondCoordinateLowerCommutator, tail, u, wi, wj, W, p, add_assoc] using hmadd

/-! ## Periodic cancellation and viscous integration by parts -/

/-- Exact mixed pressure cancellation for one ordered second-coordinate word. -/
theorem openPeriodicSolutionOn_integral_secondCoordinatePressureWork_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (gradient (secondPressureCoordinateJet (fun y ↦ pressure y t) i j) x)
        (secondCoordinateJet velocity i j x t) = 0 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hWfun : (fun x ↦ secondCoordinateJet velocity i j x t) =
      secondSpatialCoordinateJet u i j := by
    funext x
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht x i j
  have hWpoint : ∀ x,
      secondCoordinateJet velocity i j x t = secondSpatialCoordinateJet u i j x :=
    fun x ↦ congrFun hWfun x
  simp_rw [hWpoint]
  apply integral_pressureWork_unitCube_eq_zero
  · exact (secondSpatialCoordinateJet_contDiff u hu i j).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact (secondPressureCoordinateJet_contDiff p hp i j).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact secondSpatialCoordinateJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i j
  · exact secondPressureCoordinateJet_isOnePeriodic p
      (solution.pressurePeriodic t ⟨ht.1.le, ht.2⟩) i j
  · exact fun x ↦ divergence_secondSpatialCoordinateJet_eq_zero u hu
      (fun y ↦ solution.incompressible y t ⟨ht.1.le, ht.2⟩) x i j

/-- Exact viscous cube integration by parts for one actual ordered second-coordinate word. -/
theorem openPeriodicSolutionOn_integral_secondCoordinateViscousWork_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j : Fin 3) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y ↦ secondCoordinateJet velocity i j y t) x)
        (secondCoordinateJet velocity i j x t) =
      -∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ secondCoordinateJet velocity i j y t component) x‖ ^ 2 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hWfun : (fun x ↦ secondCoordinateJet velocity i j x t) =
      secondSpatialCoordinateJet u i j := by
    funext x
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht x i j
  have hWpoint : ∀ x,
      secondCoordinateJet velocity i j x t = secondSpatialCoordinateJet u i j x :=
    fun x ↦ congrFun hWfun x
  rw [hWfun]
  simp_rw [hWpoint]
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · exact (secondSpatialCoordinateJet_contDiff u hu i j).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact secondSpatialCoordinateJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i j

/-- Top transport of every actual ordered second-coordinate jet cancels. -/
theorem openPeriodicSolutionOn_integral_secondCoordinateTransport_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ secondCoordinateJet velocity i j y t) x (velocity x t))
        (secondCoordinateJet velocity i j x t) = 0 := by
  simpa [secondCoordinateJet, secondCoordinateWord] using
    openPeriodicSolutionOn_integral_coordinateJetTransport_eq_zero
      solution ht 2 (secondCoordinateWord i j)

/-! ## Integrated production for one ordered pair -/

theorem openPeriodicSolutionOn_unforced_integral_secondCoordinateProduction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i j : Fin 3) :
    (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t)
          (secondCoordinateJet velocity i j x t)) =
      -nu * (∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ secondCoordinateJet velocity i j y t component) x‖ ^ 2) -
      ∫ x in unitCube,
        inner ℝ (secondCoordinateLowerCommutator velocity t i j x)
          (secondCoordinateJet velocity i j x t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let wi : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let wj : InitialVelocity := fun y ↦ firstCoordinateJet velocity j y t
  let W : InitialVelocity := fun y ↦ secondCoordinateJet velocity i j y t
  let q : Space → ℝ := secondPressureCoordinateJet (fun y ↦ pressure y t) i j
  let lower : InitialVelocity := fun x ↦ secondCoordinateLowerCommutator velocity t i j x
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
  have hWFun : W = secondSpatialCoordinateJet u i j := by
    funext y
    exact openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
      solution ht y i j
  have hwi : ContDiff ℝ ∞ wi := by
    rw [hwiFun]
    exact spatialDirectionalJet_contDiff u hu i
  have hwj : ContDiff ℝ ∞ wj := by
    rw [hwjFun]
    exact spatialDirectionalJet_contDiff u hu j
  have hW : ContDiff ℝ ∞ W := by
    rw [hWFun]
    exact secondSpatialCoordinateJet_contDiff u hu i j
  have hp : ContDiff ℝ ∞ (fun y ↦ pressure y t) :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hq : ContDiff ℝ ∞ q :=
    secondPressureCoordinateJet_contDiff (fun y ↦ pressure y t) hp i j
  have hDwi : ContDiff ℝ ∞ (fderiv ℝ wi) := hwi.fderiv_right (by simp)
  have hDwj : ContDiff ℝ ∞ (fderiv ℝ wj) := hwj.fderiv_right (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hlower : ContDiff ℝ ∞ lower := by
    have hfirst : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wj x (wi x)) := hDwj.clm_apply hwi
    have hsecond : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ wi x (wj x)) := hDwi.clm_apply hwj
    have hthird : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ u x (W x)) := hDu.clm_apply hW
    simpa [lower, secondCoordinateLowerCommutator, u, wi, wj, W] using
      (hfirst.add hsecond).add hthird
  have hfield : ContDiffOn ℝ ∞ (Function.uncurry (secondCoordinateJet velocity i j))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    simpa [secondCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 2 (secondCoordinateWord i j)
  have htimeContinuous : Continuous (fun x ↦
      inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_openSlab
      (secondCoordinateJet velocity i j) hfield ht.1 ht.2).inner hW.continuous
  have htransportContinuous : Continuous (fun x ↦
      inner ℝ (fderiv ℝ W x (u x)) (W x)) := by
    have htransported : Continuous (fun x ↦ fderiv ℝ W x (u x)) :=
      (hW.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hu.continuous)
    exact htransported.inner hW.continuous
  have hlowerContinuous : Continuous (fun x ↦ inner ℝ (lower x) (W x)) :=
    hlower.continuous.inner hW.continuous
  have hpressureContinuous : Continuous (fun x ↦
      inner ℝ (gradient q x) (W x)) :=
    (gradient_contDiff_one q (hq.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hW.continuous
  have htimeInt : IntegrableOn (fun x ↦
      inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x)) unitCube :=
    htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have htransportInt : IntegrableOn (fun x ↦
      inner ℝ (fderiv ℝ W x (u x)) (W x)) unitCube :=
    htransportContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hlowerInt : IntegrableOn (fun x ↦ inner ℝ (lower x) (W x)) unitCube :=
    hlowerContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hpressureInt : IntegrableOn (fun x ↦
      inner ℝ (gradient q x) (W x)) unitCube :=
    hpressureContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x ↦ inner ℝ (Δ W x) (W x)) unitCube :=
    integrableOn_inner_laplacian_unitCube W
      (hW.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpoint : ∀ x,
      inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x) +
          inner ℝ (fderiv ℝ W x (u x)) (W x) =
        nu * inner ℝ (Δ W x) (W x) - inner ℝ (gradient q x) (W x) -
          inner ℝ (lower x) (W x) := by
    intro x
    have hpde := openPeriodicSolutionOn_unforced_secondCoordinateProductionIdentity
      solution ht x i j
    have hinner := congrArg (fun z : Space ↦ inner ℝ z (W x)) hpde
    simpa [u, W, q, lower, inner_add_left, inner_sub_left, real_inner_smul_left] using hinner
  have hintegrated :
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ W x (u x)) (W x) =
        nu * (∫ x in unitCube, inner ℝ (Δ W x) (W x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (W x)) -
          ∫ x in unitCube, inner ℝ (lower x) (W x) := by
    calc
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ W x (u x)) (W x) =
        ∫ x in unitCube,
          (inner ℝ (eulerianTimeJet (secondCoordinateJet velocity i j) x t) (W x) +
            inner ℝ (fderiv ℝ W x (u x)) (W x)) :=
          (integral_add htimeInt htransportInt).symm
      _ = ∫ x in unitCube,
          ((nu * inner ℝ (Δ W x) (W x) - inner ℝ (gradient q x) (W x)) -
            inner ℝ (lower x) (W x)) := by
        apply setIntegral_congr_fun hcubeMeasurable
        intro x _hx
        exact hpoint x
      _ = (∫ x in unitCube,
          (nu * inner ℝ (Δ W x) (W x) - inner ℝ (gradient q x) (W x))) -
          ∫ x in unitCube, inner ℝ (lower x) (W x) :=
        integral_sub ((hviscousInt.const_mul nu).sub hpressureInt) hlowerInt
      _ = ((∫ x in unitCube, nu * inner ℝ (Δ W x) (W x)) -
          ∫ x in unitCube, inner ℝ (gradient q x) (W x)) -
          ∫ x in unitCube, inner ℝ (lower x) (W x) := by
        rw [integral_sub (hviscousInt.const_mul nu) hpressureInt]
      _ = nu * (∫ x in unitCube, inner ℝ (Δ W x) (W x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (W x)) -
          ∫ x in unitCube, inner ℝ (lower x) (W x) := by
        rw [integral_const_mul]
  have htransportZero :=
    openPeriodicSolutionOn_integral_secondCoordinateTransport_eq_zero solution ht i j
  have hpressureZero :=
    openPeriodicSolutionOn_integral_secondCoordinatePressureWork_eq_zero solution ht i j
  have hviscous :=
    openPeriodicSolutionOn_integral_secondCoordinateViscousWork_eq solution ht i j
  dsimp [u, wi, wj, W, q, lower] at hintegrated ⊢
  rw [htransportZero, hpressureZero, hviscous] at hintegrated
  linarith

/-! ## The complete nine-word `n = 2` population -/

/-- Exactly the `n = 2` summand inside `coordinateH3TimeWork`. -/
def coordinateH2TimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 2 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (eulerianTimeJet (coordinateJetField velocity 2 word) x t)
        (coordinateJet velocity 2 word x t)

def coordinateH2Dissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 2 → Fin 3,
    ∫ x in unitCube, ∑ component : Fin 3,
      ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2

/-- All three lower nonlinear faces for every ordered second-coordinate word. -/
def coordinateH2LowerWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 2 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
        (coordinateJet velocity 2 word x t)

/-- The full `coordinateH3TimeWork` splits exactly into the order-two population closed here and
the untouched orders zero, one, and three. -/
theorem coordinateH3TimeWork_eq_coordinateH2TimeWork_add_remainder
    (velocity : VelocityField) (t : ℝ) :
    coordinateH3TimeWork velocity t = coordinateH2TimeWork velocity t +
      (∑ n ∈ Finset.univ.erase (⟨2, by norm_num⟩ : Fin 4),
        ∑ word : Fin (n : ℕ) → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (eulerianTimeJet (coordinateJetField velocity n word) x t)
              (coordinateJet velocity n word x t)) := by
  let orderTwo : Fin 4 := ⟨2, by norm_num⟩
  let work : Fin 4 → ℝ := fun n ↦
    ∑ word : Fin (n : ℕ) → Fin 3,
      ∫ x in unitCube,
        inner ℝ
          (eulerianTimeJet (coordinateJetField velocity n word) x t)
          (coordinateJet velocity n word x t)
  have hsplit := Finset.add_sum_erase Finset.univ work
    (Finset.mem_univ orderTwo)
  change (∑ n : Fin 4, work n) = work orderTwo +
    ∑ n ∈ Finset.univ.erase orderTwo, work n
  exact hsplit.symm

/-- **Exact nine-word order-two production law.** -/
theorem openPeriodicSolutionOn_unforced_coordinateH2TimeWork_eq_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH2TimeWork velocity t =
      -nu * coordinateH2Dissipation velocity t - coordinateH2LowerWork velocity t := by
  have hword : ∀ word : Fin 2 → Fin 3,
      (∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 2 word) x t)
            (coordinateJet velocity 2 word x t)) =
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
            (coordinateJet velocity 2 word x t) := by
    intro word
    have hwordEq : word = secondCoordinateWord (word 0) (word 1) := by
      funext k
      fin_cases k <;> rfl
    rw [hwordEq]
    simpa [secondCoordinateJet] using
      openPeriodicSolutionOn_unforced_integral_secondCoordinateProduction
        solution ht (word 0) (word 1)
  unfold coordinateH2TimeWork coordinateH2Dissipation coordinateH2LowerWork
  calc
    (∑ word : Fin 2 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 2 word) x t)
            (coordinateJet velocity 2 word x t)) =
      ∑ word : Fin 2 → Fin 3,
        (-nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
            (coordinateJet velocity 2 word x t)) := by
      apply Finset.sum_congr rfl
      intro word _hword
      exact hword word
    _ = (∑ word : Fin 2 → Fin 3,
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2)) -
        ∑ word : Fin 2 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
              (coordinateJet velocity 2 word x t) := by
      rw [Finset.sum_sub_distrib]
    _ = -nu * (∑ word : Fin 2 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 2 word y t component) x‖ ^ 2) -
        ∑ word : Fin 2 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (secondCoordinateLowerCommutator velocity t (word 0) (word 1) x)
              (coordinateJet velocity 2 word x t) := by
      rw [Finset.mul_sum]

section Audit

#print axioms openPeriodicSolutionOn_secondCoordinateJet_eq_secondSpatialCoordinateJet
#print axioms divergence_secondSpatialCoordinateJet_eq_zero
#print axioms eulerianTimeJet_firstCoordinateJet_eq_fderiv_time_of_contDiffAt
#print axioms openPeriodicSolutionOn_unforced_secondCoordinateProductionIdentity
#print axioms openPeriodicSolutionOn_integral_secondCoordinatePressureWork_eq_zero
#print axioms openPeriodicSolutionOn_integral_secondCoordinateViscousWork_eq
#print axioms openPeriodicSolutionOn_unforced_coordinateH2TimeWork_eq_production

end Audit


end Soma.Holonics.Millennium.NavierStokesCoordinateH2Production

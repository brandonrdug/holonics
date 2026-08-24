import ElementaryHolonics.Millennium.NavierStokesQuadraticH3Energy
import ElementaryHolonics.Millennium.NavierStokesCurlCommutation

/-!
# The first coordinate layer of the periodic quadratic production law

This owner attaches the three order-one words in `coordinateH3TimeWork` to the actual unforced
momentum equation.  The coordinate jets are the joint space--time derivatives from
`NavierStokesQuadraticH3Energy`; no replacement field or rescaled pointwise premise is used.

The intended returned face is the exact integrated `H¹` production identity.  Pressure is removed
by mixed-derivative symmetry and periodic incompressibility, viscosity is integrated by parts on
the cube, and the top advective transport cancels.  What remains is the genuine first-order
stretching commutator.  Orders two and three are deliberately outside this owner.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesCoordinateH1Production

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- The unique order-one coordinate word addressed by a basis coordinate. -/
def firstCoordinateWord (i : Fin 3) : Fin 1 → Fin 3 := fun _ ↦ i

/-- The corresponding actual joint coordinate jet. -/
def firstCoordinateJet (velocity : VelocityField) (i : Fin 3) : VelocityField :=
  coordinateJetField velocity 1 (firstCoordinateWord i)

/-- The same first spatial derivative viewed on a fixed spatial slice. -/
def spatialDirectionalJet (u : InitialVelocity) (i : Fin 3) : InitialVelocity :=
  fun x ↦ fderiv ℝ u x (spatialBasisVector i)

/-- At an admitted interior occurrence, the joint coordinate jet is exactly the corresponding
derivative of the fixed-time spatial slice. -/
theorem openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i : Fin 3) :
    firstCoordinateJet velocity i x t =
      spatialDirectionalJet (fun y ↦ velocity y t) i x := by
  have hdomain :
      Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
        nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity)
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
    (hvelocity.contDiffAt hdomain).differentiableAt (by simp)
  have hslice := hjoint.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have hsliceFDeriv := hslice.fderiv
  change iteratedFDeriv ℝ 1 (Function.uncurry velocity) (x, t)
      (coordinateWordDirections (firstCoordinateWord i)) =
    fderiv ℝ (fun y ↦ velocity y t) x (spatialBasisVector i)
  rw [iteratedFDeriv_one_apply]
  simpa [coordinateWordDirections, firstCoordinateWord, jointSpatialBasisDirection,
    spatialInclusion, Function.comp_def] using
    congrArg (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hsliceFDeriv.symm

/-- Spatial differentiation of incompressibility: every first coordinate jet remains
divergence-free. -/
theorem divergence_spatialDirectionalJet_eq_zero
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u)
    (hdiv : ∀ x, divergence u x = 0) (x : Space) (i : Fin 3) :
    divergence (spatialDirectionalJet u i) x = 0 := by
  let e : Space := spatialBasisVector i
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have happly := fderiv_clm_apply hDu (differentiableAt_const e)
  have hsymm : IsSymmSndFDerivAt ℝ u x :=
    hu.contDiffAt.isSymmSndFDerivAt (by norm_num)
  have hjetFDeriv :
      fderiv ℝ (spatialDirectionalJet u i) x =
        (fderiv ℝ (fderiv ℝ u) x).flip e := by
    simpa [spatialDirectionalJet, e] using happly
  have hdivfun : divergence u = 0 := by
    funext y
    exact hdiv y
  have hdivDerivative : fderiv ℝ (divergence u) x e = 0 := by
    rw [hdivfun]
    simp
  have hdivCoordinates : divergence u = fun y ↦ ∑ j : Fin 3,
      (EuclideanSpace.proj j).comp (fderiv ℝ u y)
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1)) := by
    funext y
    exact (sum_coordinate_fderiv_eq_divergence u y).symm
  have htermDiff : ∀ j : Fin 3, DifferentiableAt ℝ
      (fun y ↦ (EuclideanSpace.proj j).comp (fderiv ℝ u y)
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1))) x := by
    intro j
    exact (EuclideanSpace.proj j).differentiableAt.comp x
      (hDu.clm_apply (differentiableAt_const
        ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1))))
  have htermApply : ∀ j : Fin 3,
      fderiv ℝ
          (fun y ↦ (EuclideanSpace.proj j).comp (fderiv ℝ u y)
            ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1))) x e =
        (fderiv ℝ (fderiv ℝ u) x e
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1))) j := by
    intro j
    let b : Space :=
      (EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1)
    have happlyBDiff : DifferentiableAt ℝ (fun y ↦ fderiv ℝ u y b) x :=
      hDu.clm_apply (differentiableAt_const b)
    have happlyB := fderiv_clm_apply hDu (differentiableAt_const b)
    have hproject := (EuclideanSpace.proj j).hasFDerivAt.comp x
      happlyBDiff.hasFDerivAt
    have hprojectFDeriv := hproject.fderiv
    have hprojectApply := congrArg (fun L : Space →L[ℝ] ℝ ↦ L e) hprojectFDeriv
    rw [happlyB] at hprojectApply
    simpa [b] using hprojectApply
  rw [hdivCoordinates, fderiv_fun_sum (fun j _hj ↦ htermDiff j)] at hdivDerivative
  simp only [ContinuousLinearMap.sum_apply] at hdivDerivative
  simp_rw [htermApply] at hdivDerivative
  rw [← sum_coordinate_fderiv_eq_divergence (spatialDirectionalJet u i) x,
    hjetFDeriv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  calc
    (∑ j : Fin 3,
        (fderiv ℝ (fderiv ℝ u) x
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1)) e) j) =
        ∑ j : Fin 3,
          (fderiv ℝ (fderiv ℝ u) x e
            ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1))) j := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact congrArg (fun z : Space ↦ z j)
        (hsymm.eq ((EuclideanSpace.equiv (Fin 3) ℝ).symm (Pi.single j 1)) e)
    _ = 0 := hdivDerivative

/-- The scalar pressure derivative paired with the first coordinate velocity jet. -/
def pressureDirectionalJet (p : Space → ℝ) (i : Fin 3) : Space → ℝ :=
  fun x ↦ fderiv ℝ p x (spatialBasisVector i)

/-- Mixed spatial derivatives identify the differentiated pressure gradient with the gradient of
the addressed scalar pressure jet. -/
theorem gradient_pressureDirectionalJet_eq_fderiv_gradient
    (p : Space → ℝ) (hp : ContDiff ℝ 2 p) (x : Space) (i : Fin 3) :
    gradient (pressureDirectionalJet p i) x =
      fderiv ℝ (gradient p) x (spatialBasisVector i) := by
  let e : Space := spatialBasisVector i
  have hDp : DifferentiableAt ℝ (fderiv ℝ p) x :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have happly := fderiv_clm_apply hDp (differentiableAt_const e)
  have hjetFDeriv :
      fderiv ℝ (pressureDirectionalJet p i) x =
        (fderiv ℝ (fderiv ℝ p) x).flip e := by
    simpa [pressureDirectionalJet, e] using happly
  have hgradient :
      fderiv ℝ (gradient p) x =
        (InnerProductSpace.toDual ℝ Space).symm.toContinuousLinearMap.comp
          (fderiv ℝ (fderiv ℝ p) x) := by
    change fderiv ℝ
      ((InnerProductSpace.toDual ℝ Space).symm ∘ fun y ↦ fderiv ℝ p y) x = _
    simpa using (InnerProductSpace.toDual ℝ Space).symm.comp_fderiv
  have hsymm : IsSymmSndFDerivAt ℝ p x :=
    hp.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change (InnerProductSpace.toDual ℝ Space).symm
      (fderiv ℝ (pressureDirectionalJet p i) x) =
    fderiv ℝ (gradient p) x e
  rw [hjetFDeriv, hgradient]
  change (InnerProductSpace.toDual ℝ Space).symm
      ((fderiv ℝ (fderiv ℝ p) x).flip e) =
    (InnerProductSpace.toDual ℝ Space).symm
      (fderiv ℝ (fderiv ℝ p) x e)
  congr 1
  ext direction
  simpa [e] using hsymm.eq direction e

/-! ## Differentiating the actual momentum return -/

/-- The component-line momentum theorem reassembles to the actual vector equation at every
interior spatial occurrence. -/
theorem openPeriodicSolutionOn_unforced_vector_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) :
    eulerianTimeJet velocity x t +
        fderiv ℝ (fun y ↦ velocity y t) x (velocity x t) =
      nu • Δ (fun y ↦ velocity y t) x - gradient (fun y ↦ pressure y t) x := by
  ext component
  have hm := openPeriodicSolutionOn_unforced_componentLine_momentum
    solution ht x 0 component 0
  simpa [eulerianTimeJetComponentLine, advectionComponentLine_eq,
    laplacianComponentLine, pressureGradientComponentLine] using hm

/-- A jointly smooth field has a spatially smooth Eulerian time-jet slice at every interior
time.  This is the shared owner used by every differentiated coordinate layer. -/
theorem eulerianTimeJetSlice_contDiff_of_contDiffOn_openSlab
    {T : ℝ} (field : VelocityField)
    (hfield : ContDiffOn ℝ ∞ (Function.uncurry field)
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T))
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x ↦ eulerianTimeJet field x t) := by
  let slab : Set (Space × ℝ) :=
    Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T
  have hopen : IsOpen slab := isOpen_univ.prod isOpen_Ioo
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry field)) slab :=
    hfield.fderiv_of_isOpen hopen (by simp)
  have htimeJoint : ContDiffOn ℝ ∞
      (fun z ↦ fderiv ℝ (Function.uncurry field) z timeDirection) slab :=
    hderivative.clm_apply contDiffOn_const
  rw [contDiff_iff_contDiffAt]
  intro x
  have hjoint : ContDiffAt ℝ ∞
      (fun z ↦ fderiv ℝ (Function.uncurry field) z timeDirection) (x, t) :=
    htimeJoint.contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2))
  have hslice := hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
  simpa [eulerianTimeJet, timeDirection, Function.comp_def] using hslice

/-- The ordinary Eulerian time-jet slice of an admitted solution inherits all spatial
derivatives at an interior time. -/
theorem openPeriodicSolutionOn_eulerianTimeJetSlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x ↦ eulerianTimeJet velocity x t) := by
  apply eulerianTimeJetSlice_contDiff_of_contDiffOn_openSlab velocity _ ht
  apply solution.velocitySmooth.mono
  rintro ⟨x, s⟩ ⟨_hx, hs⟩
  exact ⟨Set.mem_univ x, hs.1.le, hs.2⟩

/-- Applying one addressed spatial derivative to the actual vector momentum equation. -/
theorem openPeriodicSolutionOn_unforced_firstSpatialDerivative_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector i) +
        fderiv ℝ
          (fun y ↦ fderiv ℝ (fun z ↦ velocity z t) y (velocity y t)) x
          (spatialBasisVector i) =
      nu • fderiv ℝ (Δ (fun y ↦ velocity y t)) x (spatialBasisVector i) -
        fderiv ℝ (gradient (fun y ↦ pressure y t)) x (spatialBasisVector i) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  let timeJet : InitialVelocity := fun y ↦ eulerianTimeJet velocity y t
  let advection : InitialVelocity := fun y ↦ fderiv ℝ u y (u y)
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have htime : ContDiff ℝ ∞ timeJet :=
    openPeriodicSolutionOn_eulerianTimeJetSlice_contDiff solution ht
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hadvection : ContDiff ℝ ∞ advection := hDu.clm_apply hu
  have hviscous : ContDiff ℝ ∞ (Δ u) := laplacian_contDiff hu
  have hpressure : ContDiff ℝ ∞ (gradient p) := gradient_contDiff hp
  have hm : (fun y ↦ timeJet y + advection y) =
      (fun y ↦ nu • Δ u y - gradient p y) := by
    funext y
    exact openPeriodicSolutionOn_unforced_vector_momentum solution ht y
  have hderivative := congrArg (fun f : InitialVelocity ↦ fderiv ℝ f x) hm
  change fderiv ℝ (fun y ↦ timeJet y + advection y) x =
    fderiv ℝ (fun y ↦ nu • Δ u y - gradient p y) x at hderivative
  rw [fderiv_fun_add (htime.differentiable (by simp) x)
      (hadvection.differentiable (by simp) x),
    fderiv_fun_sub ((hviscous.const_smul nu).differentiable (by simp) x)
      (hpressure.differentiable (by simp) x),
    fderiv_fun_const_smul (hviscous.differentiable (by simp) x) nu] at hderivative
  have happly := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hderivative
  simpa [u, p, timeJet, advection] using happly

/-- Generic mixed time--space commutation for one first-coordinate jet at a genuinely smooth
space--time occurrence.  This is the shared owner used by every differentiated coordinate
layer. -/
theorem eulerianTimeJet_firstCoordinateJet_eq_fderiv_time_of_contDiffAt
    (field : VelocityField) (x : Space) (t : ℝ) (i : Fin 3)
    (hfield : ContDiffAt ℝ 2 (Function.uncurry field) (x, t)) :
    eulerianTimeJet (firstCoordinateJet field i) x t =
      fderiv ℝ (fun y ↦ eulerianTimeJet field y t) x (spatialBasisVector i) := by
  let F : Space × ℝ → Space := Function.uncurry field
  let e : Space × ℝ := jointSpatialBasisDirection i
  let tau : Space × ℝ := timeDirection
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) (x, t) :=
    (hfield.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcoordinate := fderiv_clm_apply hDF (differentiableAt_const e)
  have hcoordinateTime := congrArg
    (fun L : (Space × ℝ) →L[ℝ] Space ↦ L tau) hcoordinate
  have hcoordinateTimeSimple :
      fderiv ℝ (fun z ↦ fderiv ℝ F z e) (x, t) tau =
        fderiv ℝ (fderiv ℝ F) (x, t) tau e := by
    simpa using hcoordinateTime
  have hmixed := fderiv_timeSlice_eq_time_fderiv_spatial field x t hfield
  have hmixedApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i)) hmixed
  change fderiv ℝ
      (fun z : Space × ℝ ↦
        iteratedFDeriv ℝ 1 F z (coordinateWordDirections (firstCoordinateWord i)))
      (x, t) tau =
    fderiv ℝ (fun y ↦ fderiv ℝ F (y, t) timeDirection) x
      (spatialBasisVector i)
  rw [show (fun z : Space × ℝ ↦
      iteratedFDeriv ℝ 1 F z (coordinateWordDirections (firstCoordinateWord i))) =
      (fun z ↦ fderiv ℝ F z e) by
        funext z
        simp [e, coordinateWordDirections, firstCoordinateWord,
          jointSpatialBasisDirection, iteratedFDeriv_one_apply]]
  rw [hcoordinateTimeSimple]
  simpa [e, tau, jointSpatialBasisDirection, timeDirection, spatialInclusion] using
    hmixedApply.symm

/-- The time derivative appearing in the order-one `coordinateH3TimeWork` summand is exactly the
spatial derivative of the actual Eulerian time jet. -/
theorem openPeriodicSolutionOn_eulerianTimeJet_firstCoordinateJet_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i : Fin 3) :
    eulerianTimeJet (firstCoordinateJet velocity i) x t =
      fderiv ℝ (fun y ↦ eulerianTimeJet velocity y t) x (spatialBasisVector i) := by
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity)
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hdomain :
      Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
        nhds (x, t) :=
    prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
  have hfield : ContDiffAt ℝ 2 (Function.uncurry velocity) (x, t) :=
    (hvelocity.contDiffAt hdomain).of_le (WithTop.coe_le_coe.mpr le_top)
  exact eulerianTimeJet_firstCoordinateJet_eq_fderiv_time_of_contDiffAt
    velocity x t i hfield

/-- The differentiated advective product splits into top transport of the first coordinate jet
and its genuine first-order stretching commutator. -/
theorem fderiv_advection_eq_transport_add_stretching
    (u : InitialVelocity) (hu : ContDiff ℝ 2 u)
    (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x (spatialBasisVector i) =
      fderiv ℝ (spatialDirectionalJet u i) x (u x) +
        fderiv ℝ u x (spatialDirectionalJet u i x) := by
  let e : Space := spatialBasisVector i
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have huDiff : DifferentiableAt ℝ u x := hu.differentiable (by norm_num) x
  have hadvection := fderiv_clm_apply hDu huDiff
  have hadvectionApply := congrArg (fun L : Space →L[ℝ] Space ↦ L e) hadvection
  have hcoordinate := fderiv_clm_apply hDu (differentiableAt_const e)
  have hcoordinateApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L (u x)) hcoordinate
  have hadvectionApplySimple :
      fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x e =
        fderiv ℝ u x (fderiv ℝ u x e) +
          fderiv ℝ (fderiv ℝ u) x e (u x) := by
    simpa using hadvectionApply
  have hcoordinateApplySimple :
      fderiv ℝ (fun y ↦ fderiv ℝ u y e) x (u x) =
        fderiv ℝ (fderiv ℝ u) x (u x) e := by
    simpa using hcoordinateApply
  have hsymm : IsSymmSndFDerivAt ℝ u x :=
    hu.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change fderiv ℝ (fun y ↦ fderiv ℝ u y (u y)) x e =
    fderiv ℝ (fun y ↦ fderiv ℝ u y e) x (u x) +
      fderiv ℝ u x (fderiv ℝ u x e)
  rw [hadvectionApplySimple, hcoordinateApplySimple]
  rw [hsymm.eq e (u x)]
  abel

/-- Viscosity commutes with one addressed spatial coordinate derivative. -/
theorem fderiv_laplacian_apply_eq_laplacian_spatialDirectionalJet
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u)
    (x : Space) (i : Fin 3) :
    fderiv ℝ (Δ u) x (spatialBasisVector i) =
      Δ (spatialDirectionalJet u i) x := by
  let e : Space := spatialBasisVector i
  have hcommute := fderiv_laplacian_eq_laplacian_fderiv u hu x
  have hcommuteApply := congrArg
    (fun L : Space →L[ℝ] Space ↦ L e) hcommute
  have hcommuteApplySimple :
      fderiv ℝ (Δ u) x e = Δ (fderiv ℝ u) x e := by
    simpa using hcommuteApply
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  let evaluate : (Space →L[ℝ] Space) →L[ℝ] Space :=
    (ContinuousLinearMap.apply ℝ Space) e
  have hDuTwo : ContDiffAt ℝ 2 (fderiv ℝ u) x :=
    hDu.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlapApply := hDuTwo.laplacian_CLM_comp_left (l := evaluate)
  change fderiv ℝ (Δ u) x e = Δ (fun y ↦ fderiv ℝ u y e) x
  rw [hcommuteApplySimple]
  simpa [evaluate, Function.comp_def] using hlapApply.symm

/-- The exact first-coordinate production equation for the actual joint coordinate jet. -/
theorem openPeriodicSolutionOn_unforced_firstCoordinateProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (x : Space) (i : Fin 3) :
    eulerianTimeJet (firstCoordinateJet velocity i) x t +
        fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x (velocity x t) =
      nu • Δ (fun y ↦ firstCoordinateJet velocity i y t) x -
        gradient (pressureDirectionalJet (fun y ↦ pressure y t) i) x -
        fderiv ℝ (fun y ↦ velocity y t) x (firstCoordinateJet velocity i x t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hm := openPeriodicSolutionOn_unforced_firstSpatialDerivative_momentum
    solution ht x i
  have hadvection := fderiv_advection_eq_transport_add_stretching
    u (hu.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have hviscous := fderiv_laplacian_apply_eq_laplacian_spatialDirectionalJet
    u hu x i
  have hpressure := gradient_pressureDirectionalJet_eq_fderiv_gradient
    p (hp.of_le (WithTop.coe_le_coe.mpr le_top)) x i
  have htime := openPeriodicSolutionOn_eulerianTimeJet_firstCoordinateJet_eq
    solution ht x i
  have hjetfun : (fun y ↦ firstCoordinateJet velocity i y t) =
      spatialDirectionalJet u i := by
    funext y
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht y i
  have hjetpoint : firstCoordinateJet velocity i x t =
      spatialDirectionalJet u i x := congrFun hjetfun x
  dsimp [u, p] at hm htime ⊢
  rw [hadvection, hviscous, ← hpressure] at hm
  rw [hjetfun, hjetpoint, htime]
  apply eq_sub_iff_add_eq.mpr
  simpa [u, p, add_assoc] using hm

/-! ## Periodic pressure, viscosity, and transport faces -/

theorem spatialDirectionalJet_contDiff
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (i : Fin 3) :
    ContDiff ℝ ∞ (spatialDirectionalJet u i) := by
  unfold spatialDirectionalJet
  exact (hu.fderiv_right (by simp)).clm_apply contDiff_const

theorem pressureDirectionalJet_contDiff
    (p : Space → ℝ) (hp : ContDiff ℝ ∞ p) (i : Fin 3) :
    ContDiff ℝ ∞ (pressureDirectionalJet p i) := by
  unfold pressureDirectionalJet
  exact (hp.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialDirectionalJet_isOnePeriodic
    (u : InitialVelocity) (hu : IsOnePeriodic u) (i : Fin 3) :
    IsOnePeriodic (spatialDirectionalJet u i) := by
  intro x j
  exact congrArg (fun L : Space →L[ℝ] Space ↦ L (spatialBasisVector i))
    (fderiv_isOnePeriodic u hu x j)

theorem pressureDirectionalJet_isOnePeriodic
    (p : Space → ℝ) (hp : IsOnePeriodic p) (i : Fin 3) :
    IsOnePeriodic (pressureDirectionalJet p i) := by
  intro x j
  exact congrArg (fun L : Space →L[ℝ] ℝ ↦ L (spatialBasisVector i))
    (fderiv_isOnePeriodic p hp x j)

/-- Exact mixed-derivative pressure cancellation for one first coordinate jet. -/
theorem openPeriodicSolutionOn_integral_firstCoordinatePressureWork_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (gradient (pressureDirectionalJet (fun y ↦ pressure y t) i) x)
        (firstCoordinateJet velocity i x t) = 0 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hjetfun : (fun x ↦ firstCoordinateJet velocity i x t) =
      spatialDirectionalJet u i := by
    funext x
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht x i
  have hjetpoint : ∀ x,
      firstCoordinateJet velocity i x t = spatialDirectionalJet u i x :=
    fun x ↦ congrFun hjetfun x
  simp_rw [hjetpoint]
  apply integral_pressureWork_unitCube_eq_zero
  · exact (spatialDirectionalJet_contDiff u hu i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact (pressureDirectionalJet_contDiff p hp i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact spatialDirectionalJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i
  · exact pressureDirectionalJet_isOnePeriodic p
      (solution.pressurePeriodic t ⟨ht.1.le, ht.2⟩) i
  · exact fun x ↦ divergence_spatialDirectionalJet_eq_zero u
      (hu.of_le (WithTop.coe_le_coe.mpr le_top))
      (fun y ↦ solution.incompressible y t ⟨ht.1.le, ht.2⟩) x i

/-- Exact viscous integration by parts for one actual first coordinate jet. -/
theorem openPeriodicSolutionOn_integral_firstCoordinateViscousWork_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i : Fin 3) :
    ∫ x in unitCube,
      inner ℝ (Δ (fun y ↦ firstCoordinateJet velocity i y t) x)
        (firstCoordinateJet velocity i x t) =
      -∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ firstCoordinateJet velocity i y t component) x‖ ^ 2 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hjetfun : (fun x ↦ firstCoordinateJet velocity i x t) =
      spatialDirectionalJet u i := by
    funext x
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht x i
  have hjetpoint : ∀ x,
      firstCoordinateJet velocity i x t = spatialDirectionalJet u i x :=
    fun x ↦ congrFun hjetfun x
  rw [hjetfun]
  simp_rw [hjetpoint]
  apply integral_inner_laplacian_eq_neg_integral_component_gradient_sq
  · exact (spatialDirectionalJet_contDiff u hu i).of_le
      (WithTop.coe_le_coe.mpr le_top)
  · exact spatialDirectionalJet_isOnePeriodic u
      (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩) i

/-- The top transport face of one actual first coordinate jet cancels on the periodic cube. -/
theorem openPeriodicSolutionOn_integral_firstCoordinateTransport_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i : Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ firstCoordinateJet velocity i y t) x (velocity x t))
        (firstCoordinateJet velocity i x t) = 0 := by
  simpa [firstCoordinateJet, firstCoordinateWord] using
    openPeriodicSolutionOn_integral_coordinateJetTransport_eq_zero
      solution ht 1 (firstCoordinateWord i)

/-! ## The integrated first-coordinate production identity -/

/-- For each of the three actual order-one words, time work is exactly negative viscous
dissipation minus the first-order stretching production. -/
theorem openPeriodicSolutionOn_unforced_integral_firstCoordinateProduction
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (i : Fin 3) :
    (∫ x in unitCube,
        inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t)
          (firstCoordinateJet velocity i x t)) =
      -nu * (∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ firstCoordinateJet velocity i y t component) x‖ ^ 2) -
      ∫ x in unitCube,
        inner ℝ
          (fderiv ℝ (fun y ↦ velocity y t) x (firstCoordinateJet velocity i x t))
          (firstCoordinateJet velocity i x t) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let w : InitialVelocity := fun y ↦ firstCoordinateJet velocity i y t
  let q : Space → ℝ := pressureDirectionalJet (fun y ↦ pressure y t) i
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ (fun y ↦ pressure y t) :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hjetfun : w = spatialDirectionalJet u i := by
    funext x
    exact openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
      solution ht x i
  have hw : ContDiff ℝ ∞ w := by
    rw [hjetfun]
    exact spatialDirectionalJet_contDiff u hu i
  have hq : ContDiff ℝ ∞ q :=
    pressureDirectionalJet_contDiff (fun y ↦ pressure y t) hp i
  have hfield : ContDiffOn ℝ ∞ (Function.uncurry (firstCoordinateJet velocity i))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    simpa [firstCoordinateJet] using
      openPeriodicSolutionOn_coordinateJetField_contDiffOn
        solution 1 (firstCoordinateWord i)
  have htimeContinuous : Continuous (fun x ↦
      inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x)) :=
    (eulerianTimeJet_continuous_of_contDiffOn_openSlab
      (firstCoordinateJet velocity i) hfield ht.1 ht.2).inner hw.continuous
  have htransportContinuous : Continuous (fun x ↦
      inner ℝ (fderiv ℝ w x (u x)) (w x)) := by
    have htransported : Continuous (fun x ↦ fderiv ℝ w x (u x)) :=
      (hw.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hu.continuous)
    exact htransported.inner hw.continuous
  have hstretchingContinuous : Continuous (fun x ↦
      inner ℝ (fderiv ℝ u x (w x)) (w x)) := by
    have hstretched : Continuous (fun x ↦ fderiv ℝ u x (w x)) :=
      (hu.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk hw.continuous)
    exact hstretched.inner hw.continuous
  have hpressureContinuous : Continuous (fun x ↦
      inner ℝ (gradient q x) (w x)) :=
    (gradient_contDiff_one q (hq.of_le (WithTop.coe_le_coe.mpr le_top))).continuous.inner
      hw.continuous
  have htimeInt : IntegrableOn (fun x ↦
      inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x)) unitCube :=
    htimeContinuous.continuousOn.integrableOn_compact hcubeCompact
  have htransportInt : IntegrableOn (fun x ↦
      inner ℝ (fderiv ℝ w x (u x)) (w x)) unitCube :=
    htransportContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hstretchingInt : IntegrableOn (fun x ↦
      inner ℝ (fderiv ℝ u x (w x)) (w x)) unitCube :=
    hstretchingContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hpressureInt : IntegrableOn (fun x ↦
      inner ℝ (gradient q x) (w x)) unitCube :=
    hpressureContinuous.continuousOn.integrableOn_compact hcubeCompact
  have hviscousInt : IntegrableOn (fun x ↦ inner ℝ (Δ w x) (w x)) unitCube :=
    integrableOn_inner_laplacian_unitCube w
      (hw.of_le (WithTop.coe_le_coe.mpr le_top))
  have hpoint : ∀ x,
      inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x) +
          inner ℝ (fderiv ℝ w x (u x)) (w x) =
        nu * inner ℝ (Δ w x) (w x) - inner ℝ (gradient q x) (w x) -
          inner ℝ (fderiv ℝ u x (w x)) (w x) := by
    intro x
    have hpde := openPeriodicSolutionOn_unforced_firstCoordinateProductionIdentity
      solution ht x i
    have hinner := congrArg (fun z : Space ↦ inner ℝ z (w x)) hpde
    simpa [u, w, q, inner_add_left, inner_sub_left, real_inner_smul_left] using hinner
  have hintegrated :
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u x)) (w x) =
        nu * (∫ x in unitCube, inner ℝ (Δ w x) (w x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (w x)) -
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (w x)) (w x) := by
    calc
      (∫ x in unitCube,
          inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x)) +
          ∫ x in unitCube, inner ℝ (fderiv ℝ w x (u x)) (w x) =
        ∫ x in unitCube,
          (inner ℝ (eulerianTimeJet (firstCoordinateJet velocity i) x t) (w x) +
            inner ℝ (fderiv ℝ w x (u x)) (w x)) :=
          (integral_add htimeInt htransportInt).symm
      _ = ∫ x in unitCube,
          ((nu * inner ℝ (Δ w x) (w x) - inner ℝ (gradient q x) (w x)) -
            inner ℝ (fderiv ℝ u x (w x)) (w x)) := by
        apply setIntegral_congr_fun hcubeMeasurable
        intro x _hx
        exact hpoint x
      _ = (∫ x in unitCube,
          (nu * inner ℝ (Δ w x) (w x) - inner ℝ (gradient q x) (w x))) -
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (w x)) (w x) :=
        integral_sub ((hviscousInt.const_mul nu).sub hpressureInt) hstretchingInt
      _ = ((∫ x in unitCube, nu * inner ℝ (Δ w x) (w x)) -
          ∫ x in unitCube, inner ℝ (gradient q x) (w x)) -
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (w x)) (w x) := by
        rw [integral_sub (hviscousInt.const_mul nu) hpressureInt]
      _ = nu * (∫ x in unitCube, inner ℝ (Δ w x) (w x)) -
          (∫ x in unitCube, inner ℝ (gradient q x) (w x)) -
          ∫ x in unitCube, inner ℝ (fderiv ℝ u x (w x)) (w x) := by
        rw [integral_const_mul]
  have htransportZero :=
    openPeriodicSolutionOn_integral_firstCoordinateTransport_eq_zero solution ht i
  have hpressureZero :=
    openPeriodicSolutionOn_integral_firstCoordinatePressureWork_eq_zero solution ht i
  have hviscous :=
    openPeriodicSolutionOn_integral_firstCoordinateViscousWork_eq solution ht i
  dsimp [u, w, q] at hintegrated ⊢
  rw [htransportZero, hpressureZero, hviscous] at hintegrated
  linarith

/-! ## The complete order-one population inside `coordinateH3TimeWork` -/

/-- Exactly the `n = 1` inner summand of `coordinateH3TimeWork`. -/
def coordinateH1TimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 1 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (eulerianTimeJet (coordinateJetField velocity 1 word) x t)
        (coordinateJet velocity 1 word x t)

/-- The componentwise Frobenius gradient-square population for all three order-one words. -/
def coordinateH1Dissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 1 → Fin 3,
    ∫ x in unitCube, ∑ component : Fin 3,
      ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2

/-- The exact first-order stretching commutator population. -/
def coordinateH1StretchingWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ word : Fin 1 → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
        (coordinateJet velocity 1 word x t)

/-- **Exact order-one coordinate production law.**  This closes all three order-one words in the
forty-word quadratic `H³` precursor. -/
theorem openPeriodicSolutionOn_unforced_coordinateH1TimeWork_eq_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH1TimeWork velocity t =
      -nu * coordinateH1Dissipation velocity t -
        coordinateH1StretchingWork velocity t := by
  have hword : ∀ word : Fin 1 → Fin 3,
      (∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 1 word) x t)
            (coordinateJet velocity 1 word x t)) =
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
            (coordinateJet velocity 1 word x t) := by
    intro word
    have hwordEq : word = firstCoordinateWord (word 0) := by
      funext k
      fin_cases k
      rfl
    rw [hwordEq]
    simpa [firstCoordinateJet] using
      openPeriodicSolutionOn_unforced_integral_firstCoordinateProduction
        solution ht (word 0)
  unfold coordinateH1TimeWork coordinateH1Dissipation coordinateH1StretchingWork
  calc
    (∑ word : Fin 1 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 1 word) x t)
            (coordinateJet velocity 1 word x t)) =
      ∑ word : Fin 1 → Fin 3,
        (-nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2) -
        ∫ x in unitCube,
          inner ℝ
            (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
            (coordinateJet velocity 1 word x t)) := by
      apply Finset.sum_congr rfl
      intro word _hword
      exact hword word
    _ = (∑ word : Fin 1 → Fin 3,
        -nu * (∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2)) -
        ∑ word : Fin 1 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
              (coordinateJet velocity 1 word x t) := by
      rw [Finset.sum_sub_distrib]
    _ = -nu * (∑ word : Fin 1 → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity 1 word y t component) x‖ ^ 2) -
        ∑ word : Fin 1 → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (fderiv ℝ (fun y ↦ velocity y t) x (coordinateJet velocity 1 word x t))
              (coordinateJet velocity 1 word x t) := by
      rw [Finset.mul_sum]

section Audit

#print axioms openPeriodicSolutionOn_firstCoordinateJet_eq_spatialDirectionalJet
#print axioms divergence_spatialDirectionalJet_eq_zero
#print axioms gradient_pressureDirectionalJet_eq_fderiv_gradient
#print axioms openPeriodicSolutionOn_unforced_firstCoordinateProductionIdentity
#print axioms openPeriodicSolutionOn_integral_firstCoordinatePressureWork_eq_zero
#print axioms openPeriodicSolutionOn_integral_firstCoordinateViscousWork_eq
#print axioms openPeriodicSolutionOn_unforced_coordinateH1TimeWork_eq_production

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateH1Production

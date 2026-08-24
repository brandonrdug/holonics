import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import ElementaryHolonics.Millennium.NavierStokesVorticityStretchingComb
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A third-directional precursor to the Navier--Stokes H³ production law

**[open]** The order-three receiver in `NavierStokesVorticityStretchingComb` uses the operator norm
of an iterated Fréchet derivative.  Squaring that norm does not supply a differentiable quadratic
form: operator norm is not a Hilbert--Schmidt norm and is not differentiable at every
finite-dimensional operator.  Accordingly this module does not assume a derivative for that
receiver.

**[proved-derived]** Instead it returns the exact local identity which precedes the high-order
energy estimate.  Along an arbitrary affine spatial line, the third derivative of the advective
product is split into:

* the top transport face, where all three derivatives hit the velocity Jacobian; and
* the three genuine commutator faces with binomial coefficients `1, 3, 3`.

**[conditional]** For an actual unforced `OpenPeriodicSolutionOn`, the third-directional momentum
equation then places transport on the left and viscosity, pressure, and the explicit commutator
remainder on the right.  This is a pointwise, single-direction and single-component field identity.
It performs no spatial integration, does not cover the complete mixed multi-index population, and
is not the H³ energy-production inequality or a conclusion-shaped continuation hypothesis.
-/

noncomputable section

open ContDiff Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesH3Production

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityStretchingComb

/-! ## The exact scalar third-order Leibniz commutator -/

/-- At order three, removing the face on which all derivatives hit the first factor leaves the
three lower Leibniz faces with coefficients `1, 3, 3`. -/
theorem iteratedDeriv_three_mul_sub_top
    {f g : ℝ → ℝ} {s : ℝ}
    (hf : ContDiffAt ℝ 3 f s) (hg : ContDiffAt ℝ 3 g s) :
    iteratedDeriv 3 (fun r ↦ f r * g r) s - iteratedDeriv 3 f s * g s =
      f s * iteratedDeriv 3 g s +
        3 * iteratedDeriv 1 f s * iteratedDeriv 2 g s +
          3 * iteratedDeriv 2 f s * iteratedDeriv 1 g s := by
  rw [iteratedDeriv_fun_mul hf hg]
  norm_num [Finset.sum_range_succ]

/-- The corresponding pointwise commutator bound retains each lower Leibniz face separately. -/
theorem norm_iteratedDeriv_three_mul_sub_top_le
    {f g : ℝ → ℝ} {s : ℝ}
    (hf : ContDiffAt ℝ 3 f s) (hg : ContDiffAt ℝ 3 g s) :
    ‖iteratedDeriv 3 (fun r ↦ f r * g r) s - iteratedDeriv 3 f s * g s‖ ≤
      ‖f s‖ * ‖iteratedDeriv 3 g s‖ +
        3 * ‖iteratedDeriv 1 f s‖ * ‖iteratedDeriv 2 g s‖ +
          3 * ‖iteratedDeriv 2 f s‖ * ‖iteratedDeriv 1 g s‖ := by
  rw [iteratedDeriv_three_mul_sub_top hf hg]
  calc
    ‖f s * iteratedDeriv 3 g s +
        3 * iteratedDeriv 1 f s * iteratedDeriv 2 g s +
          3 * iteratedDeriv 2 f s * iteratedDeriv 1 g s‖ ≤
        ‖f s * iteratedDeriv 3 g s‖ +
          ‖3 * iteratedDeriv 1 f s * iteratedDeriv 2 g s‖ +
            ‖3 * iteratedDeriv 2 f s * iteratedDeriv 1 g s‖ := by
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖f s‖ * ‖iteratedDeriv 3 g s‖ +
        3 * ‖iteratedDeriv 1 f s‖ * ‖iteratedDeriv 2 g s‖ +
          3 * ‖iteratedDeriv 2 f s‖ * ‖iteratedDeriv 1 g s‖ := by
      norm_num [norm_mul]

/-- Iterated derivatives commute with a finite sum of smooth scalar functions. -/
theorem iteratedDeriv_finset_sum
    {I : Type*} {n : ℕ} (indices : Finset I) (f : I → ℝ → ℝ)
    (hf : ∀ i ∈ indices, ContDiff ℝ n (f i)) (s : ℝ) :
    iteratedDeriv n (fun r ↦ ∑ i ∈ indices, f i r) s =
      ∑ i ∈ indices, iteratedDeriv n (f i) s := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [iteratedDeriv_const]
  | @insert i indices hi hinduction =>
      have hfi : ContDiff ℝ n (f i) := hf i (Finset.mem_insert_self i indices)
      have hrest : ∀ j ∈ indices, ContDiff ℝ n (f j) :=
        fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)
      simp only [Finset.sum_insert hi]
      rw [iteratedDeriv_fun_add hfi.contDiffAt
        ((ContDiff.sum hrest).contDiffAt), hinduction hrest]

/-! ## Actual velocity and Jacobian faces along a spatial line -/

/-- The standard spatial basis vector in coordinate `i`. -/
def spatialBasisVector (i : Fin 3) : Space :=
  EuclideanSpace.basisFun (Fin 3) ℝ i

/-- An addressed affine spatial line through `x` with direction `direction`. -/
def affineSpatialLine (x direction : Space) (s : ℝ) : Space :=
  x + s • direction

@[simp]
theorem affineSpatialLine_zero (x direction : Space) :
    affineSpatialLine x direction 0 = x := by
  simp [affineSpatialLine]

theorem contDiff_affineSpatialLine (x direction : Space) :
    ContDiff ℝ ∞ (affineSpatialLine x direction) := by
  unfold affineSpatialLine
  fun_prop

/-- Component `component` of a velocity field restricted to an affine spatial line. -/
def velocityComponentLine
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) (s : ℝ) : ℝ :=
  u (affineSpatialLine x direction s) component

/-- The `(component, derivativeCoordinate)` Jacobian coefficient along an affine spatial line. -/
def jacobianComponentLine
    (u : InitialVelocity) (x direction : Space)
    (component derivativeCoordinate : Fin 3) (s : ℝ) : ℝ :=
  fderiv ℝ u (affineSpatialLine x direction s)
    (spatialBasisVector derivativeCoordinate) component

@[simp]
theorem velocityComponentLine_zero
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) :
    velocityComponentLine u x direction component 0 = u x component := by
  simp [velocityComponentLine]

@[simp]
theorem jacobianComponentLine_zero
    (u : InitialVelocity) (x direction : Space)
    (component derivativeCoordinate : Fin 3) :
    jacobianComponentLine u x direction component derivativeCoordinate 0 =
      fderiv ℝ u x (spatialBasisVector derivativeCoordinate) component := by
  simp [jacobianComponentLine]

theorem velocityComponentLine_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    ContDiff ℝ ∞ (velocityComponentLine u x direction component) := by
  exact (EuclideanSpace.proj component).contDiff.comp
    (hu.comp (contDiff_affineSpatialLine x direction))

theorem jacobianComponentLine_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component derivativeCoordinate : Fin 3) :
    ContDiff ℝ ∞
      (jacobianComponentLine u x direction component derivativeCoordinate) := by
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by simp)
  exact (EuclideanSpace.proj component).contDiff.comp
    ((hDu.comp (contDiff_affineSpatialLine x direction)).clm_apply contDiff_const)

/-- The exact third-order commutator for one actual Jacobian--velocity product face. -/
theorem jacobianVelocityProduct_thirdDirectional_commutator
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component derivativeCoordinate : Fin 3) :
    iteratedDeriv 3
          (fun s ↦ jacobianComponentLine u x direction component derivativeCoordinate s *
            velocityComponentLine u x direction derivativeCoordinate s) 0 -
        iteratedDeriv 3
            (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
          u x derivativeCoordinate =
      fderiv ℝ u x (spatialBasisVector derivativeCoordinate) component *
          iteratedDeriv 3
            (velocityComponentLine u x direction derivativeCoordinate) 0 +
        3 * iteratedDeriv 1
            (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
          iteratedDeriv 2
            (velocityComponentLine u x direction derivativeCoordinate) 0 +
        3 * iteratedDeriv 2
            (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
          iteratedDeriv 1
            (velocityComponentLine u x direction derivativeCoordinate) 0 := by
  simpa using iteratedDeriv_three_mul_sub_top (s := 0)
    ((jacobianComponentLine_contDiff hu x direction component derivativeCoordinate).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))
    ((velocityComponentLine_contDiff hu x direction derivativeCoordinate).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))

/-- Component of the actual advective field, exposed as the three Jacobian--velocity product
faces along an affine line. -/
def advectionComponentLine
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) (s : ℝ) : ℝ :=
  ∑ derivativeCoordinate : Fin 3,
    jacobianComponentLine u x direction component derivativeCoordinate s *
      velocityComponentLine u x direction derivativeCoordinate s

/-- The coordinate expansion is exactly the Fréchet-Jacobian action `Du(u)`. -/
theorem advectionComponentLine_eq
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) (s : ℝ) :
    advectionComponentLine u x direction component s =
      fderiv ℝ u (affineSpatialLine x direction s)
        (u (affineSpatialLine x direction s)) component := by
  let y : Space := affineSpatialLine x direction s
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  have hrepr : ∑ i : Fin 3, (u y i) • b i = u y := by
    simpa [b, EuclideanSpace.basisFun_repr] using b.sum_repr (u y)
  rw [← hrepr]
  simp only [map_sum, map_smul]
  simp [advectionComponentLine, jacobianComponentLine, velocityComponentLine, spatialBasisVector,
    EuclideanSpace.basisFun_apply, y, b, mul_comm]

theorem advectionComponentLine_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    ContDiff ℝ ∞ (advectionComponentLine u x direction component) := by
  unfold advectionComponentLine
  apply ContDiff.sum
  intro derivativeCoordinate _hcoordinate
  exact (jacobianComponentLine_contDiff hu x direction component derivativeCoordinate).mul
    (velocityComponentLine_contDiff hu x direction derivativeCoordinate)

/-- The top face of third-order advection: all three line derivatives hit the Jacobian
coefficient, leaving the transported velocity coordinate undifferentiated. -/
def thirdDirectionalTransportFace
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) : ℝ :=
  ∑ derivativeCoordinate : Fin 3,
    iteratedDeriv 3
        (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
      u x derivativeCoordinate

/-- One true order-three commutator face, obtained by removing its top transport term. -/
def thirdDirectionalCommutatorFace
    (u : InitialVelocity) (x direction : Space)
    (component derivativeCoordinate : Fin 3) : ℝ :=
  iteratedDeriv 3
        (fun s ↦ jacobianComponentLine u x direction component derivativeCoordinate s *
          velocityComponentLine u x direction derivativeCoordinate s) 0 -
    iteratedDeriv 3
        (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
      u x derivativeCoordinate

/-- The complete third-directional advective commutator, retaining all three transported
coordinates rather than hiding them in a scalar production constant. -/
def thirdDirectionalCommutatorRemainder
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) : ℝ :=
  ∑ derivativeCoordinate : Fin 3,
    thirdDirectionalCommutatorFace u x direction component derivativeCoordinate

/-- The actual third derivative of advection splits exactly into transport plus commutator. -/
theorem iteratedDeriv_three_advectionComponentLine_eq_transport_add_commutator
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    iteratedDeriv 3 (advectionComponentLine u x direction component) 0 =
      thirdDirectionalTransportFace u x direction component +
        thirdDirectionalCommutatorRemainder u x direction component := by
  have hsmooth : ∀ derivativeCoordinate : Fin 3,
      ContDiff ℝ 3
        (fun s ↦ jacobianComponentLine u x direction component derivativeCoordinate s *
          velocityComponentLine u x direction derivativeCoordinate s) := by
    intro derivativeCoordinate
    exact ((jacobianComponentLine_contDiff hu x direction component derivativeCoordinate).mul
      (velocityComponentLine_contDiff hu x direction derivativeCoordinate)).of_le
        (WithTop.coe_le_coe.mpr le_top)
  have hsum :
      iteratedDeriv 3 (advectionComponentLine u x direction component) 0 =
        ∑ derivativeCoordinate : Fin 3,
          iteratedDeriv 3
            (fun s ↦ jacobianComponentLine u x direction component derivativeCoordinate s *
              velocityComponentLine u x direction derivativeCoordinate s) 0 := by
    exact iteratedDeriv_finset_sum Finset.univ
      (fun derivativeCoordinate s ↦
        jacobianComponentLine u x direction component derivativeCoordinate s *
          velocityComponentLine u x direction derivativeCoordinate s)
      (fun i _hi ↦ hsmooth i) 0
  rw [hsum]
  simp only [thirdDirectionalTransportFace, thirdDirectionalCommutatorRemainder,
    thirdDirectionalCommutatorFace, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro derivativeCoordinate _hcoordinate
  ring

/-- Each actual commutator face is exactly the three lower Leibniz faces. -/
theorem thirdDirectionalCommutatorFace_eq_lowerLeibnizFaces
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component derivativeCoordinate : Fin 3) :
    thirdDirectionalCommutatorFace u x direction component derivativeCoordinate =
      fderiv ℝ u x (spatialBasisVector derivativeCoordinate) component *
          iteratedDeriv 3
            (velocityComponentLine u x direction derivativeCoordinate) 0 +
        3 * iteratedDeriv 1
            (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
          iteratedDeriv 2
            (velocityComponentLine u x direction derivativeCoordinate) 0 +
        3 * iteratedDeriv 2
            (jacobianComponentLine u x direction component derivativeCoordinate) 0 *
          iteratedDeriv 1
            (velocityComponentLine u x direction derivativeCoordinate) 0 := by
  exact jacobianVelocityProduct_thirdDirectional_commutator
    hu x direction component derivativeCoordinate

/-- The commutator remainder is bounded solely by lower Leibniz faces; the fourth spatial
derivative carried by the top transport face is absent. -/
theorem norm_thirdDirectionalCommutatorRemainder_le
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    ‖thirdDirectionalCommutatorRemainder u x direction component‖ ≤
      ∑ derivativeCoordinate : Fin 3,
        (‖fderiv ℝ u x (spatialBasisVector derivativeCoordinate) component‖ *
            ‖iteratedDeriv 3
              (velocityComponentLine u x direction derivativeCoordinate) 0‖ +
          3 * ‖iteratedDeriv 1
              (jacobianComponentLine u x direction component derivativeCoordinate) 0‖ *
            ‖iteratedDeriv 2
              (velocityComponentLine u x direction derivativeCoordinate) 0‖ +
          3 * ‖iteratedDeriv 2
              (jacobianComponentLine u x direction component derivativeCoordinate) 0‖ *
            ‖iteratedDeriv 1
              (velocityComponentLine u x direction derivativeCoordinate) 0‖) := by
  unfold thirdDirectionalCommutatorRemainder
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro derivativeCoordinate _hcoordinate
  unfold thirdDirectionalCommutatorFace
  simpa using norm_iteratedDeriv_three_mul_sub_top_le (s := 0)
    ((jacobianComponentLine_contDiff hu x direction component derivativeCoordinate).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))
    ((velocityComponentLine_contDiff hu x direction derivativeCoordinate).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top))

/-! ## The unforced third-directional momentum production law -/

/-- Eulerian time-jet component of a space--time velocity field along an affine spatial line. -/
def eulerianTimeJetComponentLine
    (velocity : VelocityField) (t : ℝ) (x direction : Space)
    (component : Fin 3) (s : ℝ) : ℝ :=
  eulerianTimeJet velocity (affineSpatialLine x direction s) t component

/-- Viscous Laplacian component of a spatial velocity slice along an affine line. -/
def laplacianComponentLine
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) (s : ℝ) : ℝ :=
  (Δ u) (affineSpatialLine x direction s) component

/-- Pressure-gradient component along an affine spatial line. -/
def pressureGradientComponentLine
    (p : Space → ℝ) (x direction : Space) (component : Fin 3) (s : ℝ) : ℝ :=
  gradient p (affineSpatialLine x direction s) component

/-- The Laplacian of a smooth spatial velocity is smooth.  It is exposed through the exact
orthonormal-basis sum of second Fréchet derivatives used by the periodic energy owner. -/
theorem laplacian_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (Δ u) := by
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) :=
    hu.fderiv_right (by simp)
  have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) :=
    hDu.fderiv_right (by simp)
  have hlapfun : (Δ u) = fun y ↦ ∑ i : Fin 3,
      fderiv ℝ (fderiv ℝ u) y
        (spatialBasisVector i) (spatialBasisVector i) := by
    funext y
    simpa [spatialBasisVector] using laplacian_eq_sum_secondFDeriv u y
  rw [hlapfun]
  apply ContDiff.sum
  intro i _hi
  exact (hD2.clm_apply contDiff_const).clm_apply contDiff_const

theorem laplacianComponentLine_contDiff
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    ContDiff ℝ ∞ (laplacianComponentLine u x direction component) := by
  exact (EuclideanSpace.proj component).contDiff.comp
    ((laplacian_contDiff hu).comp (contDiff_affineSpatialLine x direction))

/-- The gradient of a smooth scalar pressure slice is smooth. -/
theorem gradient_contDiff
    {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (gradient p) := by
  have hDp : ContDiff ℝ ∞ (fderiv ℝ p) :=
    hp.fderiv_right (by simp)
  change ContDiff ℝ ∞ ((InnerProductSpace.toDual ℝ Space).symm ∘ fderiv ℝ p)
  exact (InnerProductSpace.toDual ℝ Space).symm.contDiff.comp hDp

theorem pressureGradientComponentLine_contDiff
    {p : Space → ℝ} (hp : ContDiff ℝ ∞ p)
    (x direction : Space) (component : Fin 3) :
    ContDiff ℝ ∞ (pressureGradientComponentLine p x direction component) := by
  exact (EuclideanSpace.proj component).contDiff.comp
    ((gradient_contDiff hp).comp (contDiff_affineSpatialLine x direction))

/-- Every strict-interior pressure slice of the open solution carrier is spatially smooth. -/
theorem openPeriodicSolutionOn_pressureSlice_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ ∞ (fun x ↦ pressure x t) := by
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [ht.1, ht.2]
  have htS : t < S := by
    dsimp [S]
    linarith [ht.2]
  have hST : S < T := by
    dsimp [S]
    linarith [ht.2]
  exact smoothSolutionOn_pressureSpatialSmooth
    (solution.toClosedInterior hSpos hST).toSmoothSolutionOn ht.1 htS

/-- The actual unforced momentum equation on an affine line, component by component.  Restriction
to an addressed compact slab supplies the ordinary interior time jet without adding a terminal
face to the open lifespan. -/
theorem openPeriodicSolutionOn_unforced_componentLine_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) (s : ℝ) :
    eulerianTimeJetComponentLine velocity t x direction component s +
        advectionComponentLine (fun y ↦ velocity y t) x direction component s =
      nu * laplacianComponentLine (fun y ↦ velocity y t) x direction component s -
        pressureGradientComponentLine (fun y ↦ pressure y t) x direction component s := by
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by
    dsimp [S]
    linarith [ht.1, ht.2]
  have htS : t < S := by
    dsimp [S]
    linarith [ht.2]
  have hST : S < T := by
    dsimp [S]
    linarith [ht.2]
  let closed := solution.toClosedInterior hSpos hST
  let y : Space := affineSpatialLine x direction s
  have hm := closed.momentum y t ⟨ht.1.le, htS.le⟩
  rw [← smoothSolutionOn_eulerianTimeJet_eq_derivWithin
    closed.toSmoothSolutionOn y ht.1 htS] at hm
  have hcomponent := congrArg (fun z : Space ↦ z component) hm
  simpa [eulerianTimeJetComponentLine, laplacianComponentLine,
    pressureGradientComponentLine, advectionComponentLine_eq, y] using hcomponent

/-- In the unforced equation the Eulerian time-jet component line is smooth because the exact
momentum return expresses it through smooth viscosity, pressure, and advection faces. -/
theorem openPeriodicSolutionOn_unforced_eulerianTimeJetComponentLine_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    ContDiff ℝ ∞ (eulerianTimeJetComponentLine velocity t x direction component) := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have hviscous := laplacianComponentLine_contDiff hu x direction component
  have hpressure := pressureGradientComponentLine_contDiff hp x direction component
  have hadvection := advectionComponentLine_contDiff hu x direction component
  have heq : eulerianTimeJetComponentLine velocity t x direction component =
      fun s ↦ nu * laplacianComponentLine u x direction component s -
        pressureGradientComponentLine p x direction component s -
          advectionComponentLine u x direction component s := by
    funext s
    have hm := openPeriodicSolutionOn_unforced_componentLine_momentum
      solution ht x direction component s
    dsimp [u, p] at hm ⊢
    linarith
  rw [heq]
  exact ((contDiff_const.mul hviscous).sub hpressure).sub hadvection

/-- Applying three line derivatives to the actual unforced momentum equation produces the exact
third-order PDE, before any norm, integral, or inequality receiver is taken. -/
theorem openPeriodicSolutionOn_unforced_iteratedDeriv_three_componentLine_momentum
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    iteratedDeriv 3
          (eulerianTimeJetComponentLine velocity t x direction component) 0 +
        iteratedDeriv 3
          (advectionComponentLine (fun y ↦ velocity y t) x direction component) 0 =
      nu * iteratedDeriv 3
          (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
        iteratedDeriv 3
          (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have htime : ContDiff ℝ 3
      (eulerianTimeJetComponentLine velocity t x direction component) :=
    (openPeriodicSolutionOn_unforced_eulerianTimeJetComponentLine_contDiff
      solution ht x direction component).of_le (WithTop.coe_le_coe.mpr le_top)
  have hadvection : ContDiff ℝ 3 (advectionComponentLine u x direction component) :=
    (advectionComponentLine_contDiff hu x direction component).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hviscous : ContDiff ℝ 3 (laplacianComponentLine u x direction component) :=
    (laplacianComponentLine_contDiff hu x direction component).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hpressure : ContDiff ℝ 3 (pressureGradientComponentLine p x direction component) :=
    (pressureGradientComponentLine_contDiff hp x direction component).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have heq :
      (fun s ↦ eulerianTimeJetComponentLine velocity t x direction component s +
        advectionComponentLine u x direction component s) =
      (fun s ↦ nu * laplacianComponentLine u x direction component s -
        pressureGradientComponentLine p x direction component s) := by
    funext s
    exact openPeriodicSolutionOn_unforced_componentLine_momentum
      solution ht x direction component s
  have hthird := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 3 f 0) heq
  change iteratedDeriv 3
      (fun s ↦ eulerianTimeJetComponentLine velocity t x direction component s +
        advectionComponentLine u x direction component s) 0 =
    iteratedDeriv 3
      (fun s ↦ nu * laplacianComponentLine u x direction component s -
        pressureGradientComponentLine p x direction component s) 0 at hthird
  rw [iteratedDeriv_fun_add htime.contDiffAt hadvection.contDiffAt,
    iteratedDeriv_fun_sub (contDiff_const.mul hviscous).contDiffAt hpressure.contDiffAt,
    iteratedDeriv_const_mul hviscous.contDiffAt nu] at hthird
  simpa [u, p] using hthird

/-- **Exact third-directional production law for the actual unforced solution.**  The leading
fourth-derivative face has become transport; every nonlinear remainder term has at most three
line derivatives on either velocity factor. -/
theorem openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    iteratedDeriv 3
          (eulerianTimeJetComponentLine velocity t x direction component) 0 +
        thirdDirectionalTransportFace (fun y ↦ velocity y t) x direction component =
      nu * iteratedDeriv 3
          (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
        iteratedDeriv 3
          (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0 -
        thirdDirectionalCommutatorRemainder
          (fun y ↦ velocity y t) x direction component := by
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hm := openPeriodicSolutionOn_unforced_iteratedDeriv_three_componentLine_momentum
    solution ht x direction component
  have ha := iteratedDeriv_three_advectionComponentLine_eq_transport_add_commutator
    hu x direction component
  rw [ha] at hm
  linarith

/-- The explicit scalar receiver of the three lower Leibniz faces. -/
def thirdDirectionalCommutatorBound
    (u : InitialVelocity) (x direction : Space) (component : Fin 3) : ℝ :=
  ∑ derivativeCoordinate : Fin 3,
    (‖fderiv ℝ u x (spatialBasisVector derivativeCoordinate) component‖ *
        ‖iteratedDeriv 3
          (velocityComponentLine u x direction derivativeCoordinate) 0‖ +
      3 * ‖iteratedDeriv 1
          (jacobianComponentLine u x direction component derivativeCoordinate) 0‖ *
        ‖iteratedDeriv 2
          (velocityComponentLine u x direction derivativeCoordinate) 0‖ +
      3 * ‖iteratedDeriv 2
          (jacobianComponentLine u x direction component derivativeCoordinate) 0‖ *
        ‖iteratedDeriv 1
          (velocityComponentLine u x direction derivativeCoordinate) 0‖)

theorem norm_thirdDirectionalCommutatorRemainder_le_bound
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (x direction : Space) (component : Fin 3) :
    ‖thirdDirectionalCommutatorRemainder u x direction component‖ ≤
      thirdDirectionalCommutatorBound u x direction component := by
  simpa [thirdDirectionalCommutatorBound] using
    norm_thirdDirectionalCommutatorRemainder_le hu x direction component

/-- The difference between the differentiated material derivative and the linear
viscosity--pressure return.  For an actual unforced solution it is exactly the negative
commutator remainder. -/
def unforcedThirdDirectionalProductionDefect
    (nu : ℝ) (velocity : VelocityField) (pressure : PressureField)
    (t : ℝ) (x direction : Space) (component : Fin 3) : ℝ :=
  iteratedDeriv 3
        (eulerianTimeJetComponentLine velocity t x direction component) 0 +
      thirdDirectionalTransportFace (fun y ↦ velocity y t) x direction component -
    (nu * iteratedDeriv 3
        (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
      iteratedDeriv 3
        (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0)

theorem openPeriodicSolutionOn_unforced_thirdDirectionalProductionDefect_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    unforcedThirdDirectionalProductionDefect nu velocity pressure
        t x direction component =
      -thirdDirectionalCommutatorRemainder
        (fun y ↦ velocity y t) x direction component := by
  unfold unforcedThirdDirectionalProductionDefect
  have hproduction := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht x direction component
  linarith

/-- **Actual third-order nonlinear production bound.**  After the top transport face is removed,
the differentiated unforced PDE defect is bounded by the explicit lower Leibniz population; no
fourth derivative remains in this receiver. -/
theorem norm_openPeriodicSolutionOn_unforced_thirdDirectionalProductionDefect_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    ‖unforcedThirdDirectionalProductionDefect nu velocity pressure
        t x direction component‖ ≤
      thirdDirectionalCommutatorBound
        (fun y ↦ velocity y t) x direction component := by
  rw [openPeriodicSolutionOn_unforced_thirdDirectionalProductionDefect_eq
    solution ht x direction component, norm_neg]
  exact norm_thirdDirectionalCommutatorRemainder_le_bound
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht) x direction component

#print axioms openPeriodicSolutionOn_unforced_componentLine_momentum
#print axioms openPeriodicSolutionOn_unforced_iteratedDeriv_three_componentLine_momentum
#print axioms openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
#print axioms norm_openPeriodicSolutionOn_unforced_thirdDirectionalProductionDefect_le

#print axioms iteratedDeriv_three_mul_sub_top
#print axioms norm_iteratedDeriv_three_mul_sub_top_le
#print axioms jacobianVelocityProduct_thirdDirectional_commutator
#print axioms iteratedDeriv_three_advectionComponentLine_eq_transport_add_commutator
#print axioms norm_thirdDirectionalCommutatorRemainder_le

end Soma.Holonics.Millennium.NavierStokesH3Production

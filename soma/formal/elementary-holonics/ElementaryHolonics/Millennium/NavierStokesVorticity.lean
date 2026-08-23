import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.ToLin
import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Millennium.Coupling
import ElementaryHolonics.Millennium.NavierStokes
import ElementaryHolonics.Millennium.Swing

/-!
# The local vorticity passage on the actual three-dimensional Navier–Stokes carrier

This module constructs the first differential bridge out of the official `R³` velocity object.
It keeps three objects separate:

* a continuous-linear velocity Jacobian and its standard matrix chart;
* the antisymmetric curl face of that chart;
* the addressed occurrence joining a field/point to its Jacobian and then to its vorticity.

The local Lamb identity is exact.  The kernel of the matrix-chart curl face is proved to be exactly
the symmetric-matrix population, and that zero composite is installed as the existing additive
`TransportChain`.  This is a local linear-algebra statement, not a global assertion that every
curl-free field is a gradient.  Every `C²` pressure gradient enters the kernel after second-
derivative symmetry is proved; no scalar pressure is used as a governor.

No theorem here derives the vorticity evolution equation, a global Hodge–Leray projection, an
energy estimate, regularity, or any alternative of the official Navier–Stokes problem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesVorticity

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes

/-- The standard real `3 × 3` chart for a spatial derivative. -/
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- Put three real coordinates back on the actual Euclidean-space carrier. -/
def vectorOfCoordinates (v : Fin 3 → ℝ) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm v

@[simp]
theorem vectorOfCoordinates_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    vectorOfCoordinates v i = v i := rfl

/-- A matrix acts on the Euclidean carrier through its standard coordinate chart. -/
def matrixAction (J : Matrix3) (u : Space) : Space :=
  vectorOfCoordinates (Matrix.mulVec J fun i => u i)

@[simp]
theorem matrixAction_apply (J : Matrix3) (u : Space) (i : Fin 3) :
    matrixAction J u i = ∑ j : Fin 3, J i j * u j := by
  simp [matrixAction, Matrix.mulVec, dotProduct]

/-- The oriented three-dimensional cross interaction. -/
def cross (u v : Space) : Space :=
  vectorOfCoordinates (crossProduct (fun i => u i) (fun i => v i))

/-- The curl face of one local Jacobian chart. -/
def curlFromJacobian (J : Matrix3) : Space :=
  vectorOfCoordinates ![
    J 2 1 - J 1 2,
    J 0 2 - J 2 0,
    J 1 0 - J 0 1]

/-- The transpose action `Jᵀu`.  A later calculus theorem may identify it with the gradient of
kinetic energy for an actual differentiable velocity field. -/
def transposeAction (J : Matrix3) (u : Space) : Space :=
  matrixAction J.transpose u

/-- The conventionally oriented Lamb vector `ω × u`. -/
def lambVectorFromJacobian (J : Matrix3) (u : Space) : Space :=
  cross (curlFromJacobian J) u

/-- Exchanging the two incoming rays reverses the cross interaction. -/
theorem cross_swap (u v : Space) : cross v u = -cross u v := by
  ext i
  fin_cases i <;> simp [cross, crossProduct] <;> ring

/-- The exchange of the cross interaction is exactly the frozen-board swing about zero. -/
theorem cross_swap_is_zeroAnchoredSwing (u v : Space) :
    cross v u = Swing.swing 0 (cross u v) := by
  rw [cross_swap]
  ext i
  simp [Swing.swing]

/-- **The pointwise Lamb identity in a Jacobian chart.**

The advective action is the transpose action plus the conventionally oriented Lamb vector `ω × u`.
This is a polynomial identity in the nine entries of `J` and three entries of `u`; it requires no
regularity hypothesis. -/
theorem lambIdentity (J : Matrix3) (u : Space) :
    matrixAction J u = transposeAction J u + lambVectorFromJacobian J u := by
  ext i
  fin_cases i <;>
    simp [matrixAction, transposeAction, lambVectorFromJacobian, cross, crossProduct,
      curlFromJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The same Lamb identity in the equivalent `-u × ω` convention. -/
theorem lambIdentity_velocityCrossVorticity (J : Matrix3) (u : Space) :
    matrixAction J u = transposeAction J u - cross u (curlFromJacobian J) := by
  rw [lambIdentity, lambVectorFromJacobian, cross_swap]
  abel

/-- A Jacobian chart is symmetric under transpose; equivalently, its antisymmetric matrix face
vanishes.  This is not by itself a statement about commuting mixed derivatives. -/
def IsSymmetricJacobian (J : Matrix3) : Prop :=
  ∀ i j, J i j = J j i

/-- Curl annihilates every symmetric Jacobian. -/
theorem curlFromJacobian_eq_zero_of_symmetric {J : Matrix3}
    (hJ : IsSymmetricJacobian J) : curlFromJacobian J = 0 := by
  ext i
  fin_cases i
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 2 1)
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 0 2)
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 1 0)

/-- Curl loses exactly the symmetric part: a zero curl face forces the whole Jacobian to be
symmetric, not merely a selected pair of entries. -/
theorem symmetric_of_curlFromJacobian_eq_zero {J : Matrix3}
    (hJ : curlFromJacobian J = 0) : IsSymmetricJacobian J := by
  have h0 := congrArg (fun v : Space => v 0) hJ
  have h1 := congrArg (fun v : Space => v 1) hJ
  have h2 := congrArg (fun v : Space => v 2) hJ
  simp [curlFromJacobian] at h0 h1 h2
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The complete kernel theorem for the local curl receiver. -/
theorem curlFromJacobian_eq_zero_iff (J : Matrix3) :
    curlFromJacobian J = 0 ↔ IsSymmetricJacobian J :=
  ⟨symmetric_of_curlFromJacobian_eq_zero, curlFromJacobian_eq_zero_of_symmetric⟩

/-- Symmetric Jacobians as the exact incoming population of the local symmetric-curl chain. -/
def symmetricJacobians : AddSubgroup Matrix3 where
  carrier := {J | IsSymmetricJacobian J}
  zero_mem' := by intro i j; rfl
  add_mem' := by
    intro J K hJ hK i j
    simp only [Matrix.add_apply]
    rw [hJ i j, hK i j]
  neg_mem' := by
    intro J hJ i j
    simp only [Matrix.neg_apply]
    rw [hJ i j]

/-- Curl as a linear transport from Jacobian charts to vorticity vectors. -/
def curlLinearMap : Matrix3 →ₗ[ℝ] Space where
  toFun := curlFromJacobian
  map_add' J K := by
    ext i
    fin_cases i <;> simp [curlFromJacobian] <;> ring
  map_smul' c J := by
    ext i
    fin_cases i <;> simp [curlFromJacobian] <;> ring

/-- The additive face of `curlLinearMap`, used by the existing `TransportChain` owner. -/
def curlAddHom : Matrix3 →+ Space :=
  curlLinearMap.toAddMonoidHom

/-- The named kernel artifact: the local matrix curl forgets exactly the symmetric-matrix
population. -/
theorem curlAddHom_ker : curlAddHom.ker = symmetricJacobians := by
  ext J
  exact curlFromJacobian_eq_zero_iff J

/-- The local symmetric-curl chain: symmetric charts enter the full matrix population, then curl
carries them to zero.  The source contains all symmetric matrices, not only realized Hessians. -/
def symmetricCurlChain : Coupling.TransportChain symmetricJacobians Matrix3 Space where
  into := symmetricJacobians.subtype
  outOf := curlAddHom
  composite_zero J := curlFromJacobian_eq_zero_of_symmetric J.property

/-- Every chart retained by the local matrix curl is realized by the symmetric inclusion. -/
theorem symmetricCurlChain_retained_le_realized :
    symmetricCurlChain.retained ≤ symmetricCurlChain.realized := by
  intro J hJ
  change curlFromJacobian J = 0 at hJ
  exact ⟨⟨J, symmetric_of_curlFromJacobian_eq_zero hJ⟩, rfl⟩

/-- The symmetric-curl chain is exact at the matrix population, hence its coupling obstruction
vanishes. -/
theorem symmetricCurlChain_glues : symmetricCurlChain.toPassage.Glues :=
  symmetricCurlChain.theOntoSupplyGlues symmetricCurlChain_retained_le_realized

/-- The standard-basis matrix chart of a continuous-linear spatial derivative. -/
def jacobianMatrix (D : Space →L[ℝ] Space) : Matrix3 :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis D.toLinearMap

/-- A Jacobian-matrix entry is the corresponding standard-basis directional derivative. -/
theorem jacobianMatrix_apply (D : Space →L[ℝ] Space) (i j : Fin 3) :
    jacobianMatrix D i j = D (EuclideanSpace.basisFun (Fin 3) ℝ j) i := by
  simp [jacobianMatrix, LinearMap.toMatrix_apply]

/-- The matrix chart carries the continuous-linear action exactly. -/
theorem matrixAction_jacobianMatrix (D : Space →L[ℝ] Space) (u : Space) :
    matrixAction (jacobianMatrix D) u = D u := by
  ext i
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis D.toLinearMap u
  simpa [matrixAction, jacobianMatrix] using congrFun h i

/-- Coordinate expansion of a continuous-linear action in the Euclidean basis. -/
theorem continuousLinearMap_apply_coordinate (D : Space →L[ℝ] Space) (u : Space)
    (i : Fin 3) :
    D u i = ∑ j : Fin 3, jacobianMatrix D i j * u j := by
  symm
  exact congrArg (fun v : Space => v i) (matrixAction_jacobianMatrix D u)

/-- Curl transported directly from a continuous-linear velocity derivative.  Finite-dimensionality
turns this linear receiver into a continuous-linear map, so it may be composed through `fderiv`
without an untyped coordinate detour. -/
def derivativeCurlLinearMap : (Space →L[ℝ] Space) →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap ({
    toFun := fun D => curlFromJacobian (jacobianMatrix D)
    map_add' := by
      intro D E
      ext i
      fin_cases i <;> simp [curlFromJacobian, jacobianMatrix_apply] <;> ring
    map_smul' := by
      intro c D
      ext i
      fin_cases i <;> simp [curlFromJacobian, jacobianMatrix_apply] <;> ring
  } : (Space →L[ℝ] Space) →ₗ[ℝ] Space)

@[simp]
theorem derivativeCurlLinearMap_apply (D : Space →L[ℝ] Space) :
    derivativeCurlLinearMap D = curlFromJacobian (jacobianMatrix D) := rfl

/-- The totalized spatial-Jacobian chart of a velocity field at a point.  It denotes an actual
derivative occurrence only when accompanied by differentiability testimony. -/
def velocityJacobianAt (u : InitialVelocity) (x : Space) : Matrix3 :=
  jacobianMatrix (fderiv ℝ u x)

/-- The totalized vorticity chart at a field/point pair.  `DifferentiableVelocityOccurrence`
supplies the admission proof for its use as an actual derivative face. -/
def vorticityAt (u : InitialVelocity) (x : Space) : Space :=
  curlFromJacobian (velocityJacobianAt u x)

/-- The actual pointwise Lamb identity for the derivative used by the official Navier–Stokes
object. -/
theorem pointwiseLambIdentity (u : InitialVelocity) (x : Space)
    (_hu : DifferentiableAt ℝ u x) :
    fderiv ℝ u x (u x) =
      transposeAction (velocityJacobianAt u x) (u x) +
        lambVectorFromJacobian (velocityJacobianAt u x) (u x) := by
  rw [← matrixAction_jacobianMatrix]
  exact lambIdentity (velocityJacobianAt u x) (u x)

/-- A differentiable velocity occurrence.  The proof prevents totalized `fderiv` from silently
turning a nondifferentiable source event into a zero jet. -/
structure DifferentiableVelocityOccurrence where
  velocity : InitialVelocity
  point : Space
  differentiableAt : DifferentiableAt ℝ velocity point

/-- The derivative occurrence from an addressed velocity field and point to its Jacobian chart. -/
def velocityToJacobianPassage :
    AddressedPassage (InitialVelocity × Space) Matrix3 where
  Occurrence := DifferentiableVelocityOccurrence
  source occurrence := (occurrence.velocity, occurrence.point)
  target occurrence := velocityJacobianAt occurrence.velocity occurrence.point

/-- The curl occurrence from a Jacobian chart to its vorticity face. -/
def jacobianToVorticityPassage : AddressedPassage Matrix3 Space where
  Occurrence := Matrix3
  source := id
  target := curlFromJacobian

/-- The ordered velocity-to-Jacobian-to-vorticity passage.  Its occurrence population retains the
field/point occurrence, the Jacobian occurrence, and their literal joining equality. -/
def velocityToVorticityPassage :
    AddressedPassage (InitialVelocity × Space) Space :=
  AddressedPassage.comp jacobianToVorticityPassage velocityToJacobianPassage

/-- The canonical composite occurrence carried by one actual field/point event. -/
def velocityToVorticityOccurrence (u : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    velocityToVorticityPassage.Occurrence :=
  ⟨⟨u, x, hu⟩, velocityJacobianAt u x, rfl⟩

/-- The composite occurrence retains its addressed predecessor exactly. -/
theorem velocityToVorticityOccurrence_source (u : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    velocityToVorticityPassage.source (velocityToVorticityOccurrence u x hu) = (u, x) := rfl

/-- The composite occurrence returns the actual vorticity face. -/
theorem velocityToVorticityOccurrence_target (u : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) :
    velocityToVorticityPassage.target (velocityToVorticityOccurrence u x hu) =
      vorticityAt u x := rfl

/-- The inverse Riesz transport evaluated in one standard coordinate is evaluation of the carried
covector on that coordinate direction. -/
theorem toDual_symm_coordinate (φ : StrongDual ℝ Space) (i : Fin 3) :
    (InnerProductSpace.toDual ℝ Space).symm φ i =
      φ (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
  calc
    (InnerProductSpace.toDual ℝ Space).symm φ i =
        inner ℝ ((InnerProductSpace.toDual ℝ Space).symm φ)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) := by
            symm
            exact EuclideanSpace.inner_basisFun_real (Fin 3)
              ((InnerProductSpace.toDual ℝ Space).symm φ) i
    _ = φ (EuclideanSpace.basisFun (Fin 3) ℝ i) :=
      InnerProductSpace.toDual_symm_apply

/-- A `C²` scalar field has a symmetric gradient Jacobian on the actual Euclidean carrier. -/
theorem gradientJacobian_symmetric_of_contDiffAtTwo (p : Space → ℝ) (x : Space)
    (hp : ContDiffAt ℝ 2 p x) :
    IsSymmetricJacobian (velocityJacobianAt (gradient p) x) := by
  have hsecond : IsSymmSndFDerivAt ℝ p x :=
    hp.isSymmSndFDerivAt (by simp)
  have hgradient :
      fderiv ℝ (gradient p) x =
        (InnerProductSpace.toDual ℝ Space).symm.toContinuousLinearMap.comp
          (fderiv ℝ (fderiv ℝ p) x) := by
    change fderiv ℝ ((InnerProductSpace.toDual ℝ Space).symm ∘ fun y => fderiv ℝ p y) x = _
    simpa using (InnerProductSpace.toDual ℝ Space).symm.comp_fderiv
  intro i j
  rw [velocityJacobianAt, jacobianMatrix_apply, jacobianMatrix_apply, hgradient]
  change
    (InnerProductSpace.toDual ℝ Space).symm
          ((fderiv ℝ (fderiv ℝ p) x) (EuclideanSpace.basisFun (Fin 3) ℝ j)) i =
      (InnerProductSpace.toDual ℝ Space).symm
          ((fderiv ℝ (fderiv ℝ p) x) (EuclideanSpace.basisFun (Fin 3) ℝ i)) j
  rw [toDual_symm_coordinate, toDual_symm_coordinate]
  exact hsecond (EuclideanSpace.basisFun (Fin 3) ℝ j)
    (EuclideanSpace.basisFun (Fin 3) ℝ i)

/-- A pressure field enters the curl kernel exactly when the Jacobian of its actual gradient is
symmetric.  The analytic theorem supplying that symmetry from second differentiability is kept as
an explicit hypothesis rather than hidden in the word “pressure”. -/
theorem curl_gradient_eq_zero_of_symmetricDerivative (p : Space → ℝ) (x : Space)
    (hessianSymmetry : IsSymmetricJacobian (velocityJacobianAt (gradient p) x)) :
    vorticityAt (gradient p) x = 0 :=
  curlFromJacobian_eq_zero_of_symmetric hessianSymmetry

/-- **Curl annihilates the gradient of every `C²` pressure field.**

This is the exact local pressure-removal square needed before a vorticity evolution equation can
be derived. -/
theorem curl_gradient_eq_zero (p : Space → ℝ) (x : Space) (hp : ContDiffAt ℝ 2 p x) :
    vorticityAt (gradient p) x = 0 :=
  curl_gradient_eq_zero_of_symmetricDerivative p x
    (gradientJacobian_symmetric_of_contDiffAtTwo p x hp)

/-! ## Attachment to the official smooth-solution carrier -/

/-- A field smooth on the nonnegative space-time half-cylinder has a smooth spatial slice at every
strictly positive time.  The strict inequality keeps this theorem inside the set's neighbourhood;
the boundary time `t = 0` remains a separate within-derivative face. -/
theorem spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞}
    (field : Space → ℝ → F) (x : Space) (t : ℝ)
    (hfield : ContDiffOn ℝ n (Function.uncurry field) (Set.univ ×ˢ Set.Ici 0))
    (ht : 0 < t) : ContDiffAt ℝ n (fun y => field y t) x := by
  have hdomain : Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
    apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
    rintro z ⟨_hzuniv, hztime⟩
    exact ⟨Set.mem_univ z.1, le_of_lt (show 0 < z.2 from hztime)⟩
  have huncurry := hfield.contDiffAt hdomain
  have hpair : ContDiffAt ℝ n (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using huncurry.comp x hpair

/-- The velocity slice of an official smooth solution is genuinely differentiable at every
positive-time event. -/
theorem smoothSolution_velocitySlice_differentiableAt
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ (fun y => velocity y t) x :=
  (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
    solution.velocitySmooth ht).differentiableAt (by simp)

/-- An official smooth solution therefore supplies an admitted addressed
velocity-to-Jacobian-to-vorticity occurrence at every positive-time event. -/
def smoothSolution_velocityToVorticityOccurrence
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) : velocityToVorticityPassage.Occurrence :=
  velocityToVorticityOccurrence (fun y => velocity y t) x
    (smoothSolution_velocitySlice_differentiableAt solution x t ht)

/-- The admitted smooth-solution occurrence returns the solution's actual positive-time vorticity
face while retaining the velocity slice and point in its predecessor address. -/
theorem smoothSolution_velocityToVorticityOccurrence_target
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    velocityToVorticityPassage.target
        (smoothSolution_velocityToVorticityOccurrence solution x t ht) =
      vorticityAt (fun y => velocity y t) x := rfl

/-- The local Lamb decomposition holds on every positive-time velocity occurrence of an official
smooth solution. -/
theorem smoothSolution_pointwiseLambIdentity
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    fderiv ℝ (fun y => velocity y t) x (velocity x t) =
      transposeAction (velocityJacobianAt (fun y => velocity y t) x) (velocity x t) +
        lambVectorFromJacobian (velocityJacobianAt (fun y => velocity y t) x)
          (velocity x t) :=
  pointwiseLambIdentity (fun y => velocity y t) x
    (smoothSolution_velocitySlice_differentiableAt solution x t ht)

/-- The pressure term of an official smooth solution has zero local curl at every positive-time
event.  This attaches the abstract `C²` pressure theorem to the actual `SmoothSolution` port. -/
theorem smoothSolution_pressureCurl_eq_zero
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    vorticityAt (gradient (fun y => pressure y t)) x = 0 := by
  apply curl_gradient_eq_zero
  exact (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime pressure x t
    solution.pressureSmooth ht).of_le (WithTop.coe_le_coe.mpr le_top)

/-! ## The nonlinear vorticity transport at one second-order jet -/

/-- A coordinate chart for the second spatial jet, with convention
`H i j k = ∂ₖ ∂ⱼ uᵢ`. -/
abbrev SecondJet := Fin 3 → Fin 3 → Fin 3 → ℝ

/-- The totalized second spatial jet of a velocity field.  As for `velocityJacobianAt`, this chart
denotes an actual second derivative only when accompanied by `C²` testimony. -/
def secondJetAt (u : InitialVelocity) (x : Space) : SecondJet :=
  fun i j k =>
    fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.basisFun (Fin 3) ℝ k)
      (EuclideanSpace.basisFun (Fin 3) ℝ j) i

/-- The derivative directions of a genuine second jet commute. -/
def HasMixedSpatialSymmetry (H : SecondJet) : Prop :=
  ∀ i j k, H i j k = H i k j

/-- The totalized chart `secondJetAt` has its intended mixed symmetry whenever its source field is
genuinely `C²` at the addressed point. -/
theorem secondJetAt_hasMixedSpatialSymmetry (u : InitialVelocity) (x : Space)
    (hu : ContDiffAt ℝ 2 u x) : HasMixedSpatialSymmetry (secondJetAt u x) := by
  have hsecond : IsSymmSndFDerivAt ℝ u x :=
    hu.isSymmSndFDerivAt (by simp)
  intro i j k
  exact congrArg (fun v : Space => v i)
    (hsecond (EuclideanSpace.basisFun (Fin 3) ℝ k)
      (EuclideanSpace.basisFun (Fin 3) ℝ j))

/-- A twice-differentiable velocity occurrence.  This is the admission witness for the totalized
second-jet chart. -/
structure TwiceDifferentiableVelocityOccurrence where
  velocity : InitialVelocity
  point : Space
  contDiffAtTwo : ContDiffAt ℝ 2 velocity point

/-- The addressed passage from a velocity occurrence to its admitted second spatial jet. -/
def velocityToSecondJetPassage :
    AddressedPassage (InitialVelocity × Space) SecondJet where
  Occurrence := TwiceDifferentiableVelocityOccurrence
  source occurrence := (occurrence.velocity, occurrence.point)
  target occurrence := secondJetAt occurrence.velocity occurrence.point

/-- The canonical admitted second-jet occurrence. -/
def velocityToSecondJetOccurrence (u : InitialVelocity) (x : Space)
    (hu : ContDiffAt ℝ 2 u x) : velocityToSecondJetPassage.Occurrence :=
  ⟨u, x, hu⟩

/-- A positive-time velocity slice of a smooth solution is genuinely `C²`. -/
theorem smoothSolution_velocitySlice_contDiffAtTwo
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    ContDiffAt ℝ 2 (fun y => velocity y t) x :=
  (spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime velocity x t
    solution.velocitySmooth ht).of_le (WithTop.coe_le_coe.mpr le_top)

/-- A smooth solution supplies an admitted second-jet occurrence at every positive-time event. -/
def smoothSolution_velocityToSecondJetOccurrence
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) : velocityToSecondJetPassage.Occurrence :=
  velocityToSecondJetOccurrence (fun y => velocity y t) x
    (smoothSolution_velocitySlice_contDiffAtTwo solution x t ht)

/-- The admitted second jet of a positive-time smooth-solution occurrence has the required mixed
spatial symmetry. -/
theorem smoothSolution_secondJet_hasMixedSpatialSymmetry
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    HasMixedSpatialSymmetry (secondJetAt (fun y => velocity y t) x) :=
  secondJetAt_hasMixedSpatialSymmetry (fun y => velocity y t) x
    (smoothSolution_velocitySlice_contDiffAtTwo solution x t ht)

/-- The trace/divergence face of one Jacobian chart. -/
def divergenceFromJacobian (J : Matrix3) : ℝ :=
  ∑ i : Fin 3, J i i

/-- The coordinate trace of the admitted Jacobian is the basis-independent divergence owner. -/
theorem divergenceFromJacobian_velocityJacobianAt (u : InitialVelocity) (x : Space) :
    divergenceFromJacobian (velocityJacobianAt u x) = divergence u x := by
  rw [divergence, LinearMap.trace_eq_matrix_trace ℝ
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  rfl

/-- The first jet of a smooth solution lies in the incompressible fibre at every nonnegative-time
event. -/
theorem smoothSolution_divergenceFromJacobian_eq_zero
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 ≤ t) :
    divergenceFromJacobian (velocityJacobianAt (fun y => velocity y t) x) = 0 := by
  rw [divergenceFromJacobian_velocityJacobianAt]
  exact solution.incompressible x t ht

/-- The Jacobian of vorticity induced by a second velocity jet. -/
def vorticityJacobianFromSecondJet (H : SecondJet) : Matrix3 := ![
  fun k => H 2 1 k - H 1 2 k,
  fun k => H 0 2 k - H 2 0 k,
  fun k => H 1 0 k - H 0 1 k]

/-- The passage from a second velocity jet to its induced vorticity Jacobian. -/
def secondJetToVorticityJacobianPassage : AddressedPassage SecondJet Matrix3 where
  Occurrence := SecondJet
  source := id
  target := vorticityJacobianFromSecondJet

/-- The ordered velocity-to-second-jet-to-vorticity-Jacobian passage retains the admitted source
occurrence, the second jet, and their joining equality. -/
def velocityToVorticityJacobianPassage :
    AddressedPassage (InitialVelocity × Space) Matrix3 :=
  AddressedPassage.comp secondJetToVorticityJacobianPassage velocityToSecondJetPassage

/-- The canonical composite occurrence from a `C²` velocity event to the vorticity Jacobian
induced by its second jet. -/
def velocityToVorticityJacobianOccurrence (u : InitialVelocity) (x : Space)
    (hu : ContDiffAt ℝ 2 u x) : velocityToVorticityJacobianPassage.Occurrence :=
  ⟨velocityToSecondJetOccurrence u x hu, secondJetAt u x, rfl⟩

/-- A smooth solution supplies the complete ordered second-jet occurrence at positive time. -/
def smoothSolution_velocityToVorticityJacobianOccurrence
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) : velocityToVorticityJacobianPassage.Occurrence :=
  velocityToVorticityJacobianOccurrence (fun y => velocity y t) x
    (smoothSolution_velocitySlice_contDiffAtTwo solution x t ht)

/-- The positive-time composite returns the vorticity Jacobian induced by the solution's admitted
second spatial jet. -/
theorem smoothSolution_velocityToVorticityJacobianOccurrence_target
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    velocityToVorticityJacobianPassage.target
        (smoothSolution_velocityToVorticityJacobianOccurrence solution x t ht) =
      vorticityJacobianFromSecondJet (secondJetAt (fun y => velocity y t) x) := rfl

/-- The second-jet vorticity Jacobian is exactly the derivative chart of the actual vorticity
field for a genuine `C²` velocity occurrence. -/
theorem velocityJacobianAt_vorticity_eq_vorticityJacobianFromSecondJet
    (u : InitialVelocity) (x : Space) (hu : ContDiffAt ℝ 2 u x) :
    velocityJacobianAt (fun y => vorticityAt u y) x =
      vorticityJacobianFromSecondJet (secondJetAt u x) := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hvorticityDerivative :
      fderiv ℝ (fun y => vorticityAt u y) x =
        derivativeCurlLinearMap.comp (fderiv ℝ (fderiv ℝ u) x) := by
    change fderiv ℝ (derivativeCurlLinearMap ∘ fun y => fderiv ℝ u y) x = _
    rw [fderiv_comp x derivativeCurlLinearMap.differentiableAt hDu,
      ContinuousLinearMap.fderiv]
  rw [velocityJacobianAt, hvorticityDerivative]
  ext i k
  rw [jacobianMatrix_apply]
  fin_cases i <;>
    simp [derivativeCurlLinearMap, curlFromJacobian, vorticityJacobianFromSecondJet,
      secondJetAt, jacobianMatrix_apply]

/-- The vorticity-Jacobian compatibility square attached to a positive-time smooth-solution
occurrence. -/
theorem smoothSolution_velocityJacobianAt_vorticity
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    velocityJacobianAt
        (fun y => vorticityAt (fun z => velocity z t) y) x =
      vorticityJacobianFromSecondJet (secondJetAt (fun y => velocity y t) x) :=
  velocityJacobianAt_vorticity_eq_vorticityJacobianFromSecondJet
    (fun y => velocity y t) x
    (smoothSolution_velocitySlice_contDiffAtTwo solution x t ht)

/-- The product-rule Jacobian of the advective field `(u · ∇)u`, expressed entirely in the local
velocity value, first jet, and second jet. -/
def advectionJacobianFromJets (H : SecondJet) (J : Matrix3) (u : Space) : Matrix3 :=
  fun i k => ∑ j : Fin 3, (J j k * J i j + u j * H i j k)

/-- The algebraic advection jet is exactly the derivative of the actual advective field for a
genuine `C²` velocity occurrence.  This closes the product-rule compatibility square without
identifying any time or Laplacian port. -/
theorem velocityJacobianAt_advection_eq_advectionJacobianFromJets
    (u : InitialVelocity) (x : Space) (hu : ContDiffAt ℝ 2 u x) :
    velocityJacobianAt (fun y => fderiv ℝ u y (u y)) x =
      advectionJacobianFromJets (secondJetAt u x) (velocityJacobianAt u x) (u x) := by
  have hDu : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [velocityJacobianAt, fderiv_clm_apply hDu (hu.differentiableAt (by norm_num))]
  ext i k
  rw [jacobianMatrix_apply]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  change
    (fderiv ℝ u x
        (fderiv ℝ u x (EuclideanSpace.basisFun (Fin 3) ℝ k))) i +
      (fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.basisFun (Fin 3) ℝ k) (u x)) i =
      advectionJacobianFromJets (secondJetAt u x)
        (velocityJacobianAt u x) (u x) i k
  rw [continuousLinearMap_apply_coordinate, continuousLinearMap_apply_coordinate]
  simp only [advectionJacobianFromJets, secondJetAt, velocityJacobianAt,
    jacobianMatrix_apply, Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

/-- Vorticity constructed from a mixed-symmetric second jet is divergence-free. -/
theorem divergence_vorticityJacobian_eq_zero (H : SecondJet)
    (hH : HasMixedSpatialSymmetry H) :
    divergenceFromJacobian (vorticityJacobianFromSecondJet H) = 0 := by
  simp [divergenceFromJacobian, vorticityJacobianFromSecondJet, Fin.sum_univ_succ]
  rw [hH 2 1 0, hH 1 2 0, hH 0 2 1]
  ring

/-- The actual positive-time vorticity field of a smooth solution is divergence-free.  The result
passes through the admitted second jet and the derivative/vorticity compatibility square. -/
theorem smoothSolution_divergence_vorticityAt_eq_zero
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    divergence (fun y => vorticityAt (fun z => velocity z t) y) x = 0 := by
  rw [← divergenceFromJacobian_velocityJacobianAt,
    smoothSolution_velocityJacobianAt_vorticity solution x t ht]
  exact divergence_vorticityJacobian_eq_zero _
    (smoothSolution_secondJet_hasMixedSpatialSymmetry solution x t ht)

/-- **The nonlinear vorticity transport identity at one second-order jet.**

Taking curl of the advective Jacobian returns transport of vorticity by velocity, minus stretching
of velocity by vorticity, plus the divergence residue.  This exposes the stretching term; its
vanishing under a planar reduction and the insufficiency of energy control remain separate receiver
statements. -/
theorem curl_advectionJacobian (H : SecondJet) (J : Matrix3) (u : Space)
    (hH : HasMixedSpatialSymmetry H) :
    curlFromJacobian (advectionJacobianFromJets H J u) =
      matrixAction (vorticityJacobianFromSecondJet H) u -
        matrixAction J (curlFromJacobian J) +
          divergenceFromJacobian J • curlFromJacobian J := by
  ext i
  fin_cases i
  · simp [curlFromJacobian, advectionJacobianFromJets, vorticityJacobianFromSecondJet,
      matrixAction, divergenceFromJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rw [hH 2 0 1, hH 1 0 2, hH 1 1 2, hH 2 2 1]
    ring
  · simp [curlFromJacobian, advectionJacobianFromJets, vorticityJacobianFromSecondJet,
      matrixAction, divergenceFromJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rw [hH 0 0 2, hH 0 1 2, hH 2 1 0, hH 2 2 0]
    ring
  · simp [curlFromJacobian, advectionJacobianFromJets, vorticityJacobianFromSecondJet,
      matrixAction, divergenceFromJacobian, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    rw [hH 0 0 1, hH 1 1 0, hH 1 2 0, hH 0 2 1]
    ring

/-- On the incompressible fibre, the divergence residue vanishes and the true three-dimensional
stretching term remains visible. -/
theorem curl_advectionJacobian_of_incompressible (H : SecondJet) (J : Matrix3) (u : Space)
    (hH : HasMixedSpatialSymmetry H) (hdiv : divergenceFromJacobian J = 0) :
    curlFromJacobian (advectionJacobianFromJets H J u) =
      matrixAction (vorticityJacobianFromSecondJet H) u -
        matrixAction J (curlFromJacobian J) := by
  rw [curl_advectionJacobian H J u hH, hdiv, zero_smul, add_zero]

/-- The nonlinear curl identity instantiated on the admitted first and second spatial jets of an
actual smooth solution at positive time.  The following product-rule theorem identifies its
advection chart with the derivative of the actual advective field. -/
theorem smoothSolution_curl_advectionJacobian
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    curlFromJacobian
        (advectionJacobianFromJets
          (secondJetAt (fun y => velocity y t) x)
          (velocityJacobianAt (fun y => velocity y t) x)
          (velocity x t)) =
      matrixAction
          (vorticityJacobianFromSecondJet (secondJetAt (fun y => velocity y t) x))
          (velocity x t) -
        matrixAction (velocityJacobianAt (fun y => velocity y t) x)
          (vorticityAt (fun y => velocity y t) x) := by
  apply curl_advectionJacobian_of_incompressible
  · exact smoothSolution_secondJet_hasMixedSpatialSymmetry solution x t ht
  · exact smoothSolution_divergenceFromJacobian_eq_zero solution x t (le_of_lt ht)

/-- The product-rule compatibility square for the positive-time velocity slice of a smooth
solution. -/
theorem smoothSolution_velocityJacobianAt_advection
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    velocityJacobianAt
        (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
      advectionJacobianFromJets
        (secondJetAt (fun y => velocity y t) x)
        (velocityJacobianAt (fun y => velocity y t) x)
        (velocity x t) :=
  velocityJacobianAt_advection_eq_advectionJacobianFromJets
    (fun y => velocity y t) x
    (smoothSolution_velocitySlice_contDiffAtTwo solution x t ht)

/-- **The actual positive-time nonlinear vorticity transport identity.**

Curl of the solution's advective field is transport of vorticity by velocity minus stretching of
velocity by vorticity.  Every totalized derivative in the statement is admitted by the solution's
positive-time smoothness; no time or viscous commutation is asserted here. -/
theorem smoothSolution_vorticityAt_advection
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) (t : ℝ) (ht : 0 < t) :
    vorticityAt
        (fun y => fderiv ℝ (fun z => velocity z t) y (velocity y t)) x =
      fderiv ℝ (fun y => vorticityAt (fun z => velocity z t) y) x (velocity x t) -
        fderiv ℝ (fun y => velocity y t) x
          (vorticityAt (fun y => velocity y t) x) := by
  rw [vorticityAt, smoothSolution_velocityJacobianAt_advection solution x t ht,
    smoothSolution_curl_advectionJacobian solution x t ht,
    ← smoothSolution_velocityJacobianAt_vorticity solution x t ht,
    velocityJacobianAt, matrixAction_jacobianMatrix,
    velocityJacobianAt, matrixAction_jacobianMatrix]

/-- Applying curl to a differentiated momentum balance removes exactly the symmetric pressure
Jacobian.  The five matrix ports are respectively the time, advection, viscous, pressure, and force
jets; attaching them to an actual solution still owes the corresponding derivative-commutation
receipts. -/
theorem curl_differentiatedMomentum
    (timeJet advectionJet viscousJet pressureJet forceJet : Matrix3) (ν : ℝ)
    (hpressure : IsSymmetricJacobian pressureJet)
    (hmomentum : timeJet + advectionJet = ν • viscousJet - pressureJet + forceJet) :
    curlFromJacobian timeJet + curlFromJacobian advectionJet =
      ν • curlFromJacobian viscousJet + curlFromJacobian forceJet := by
  change curlLinearMap timeJet + curlLinearMap advectionJet =
    ν • curlLinearMap viscousJet + curlLinearMap forceJet
  rw [← curlLinearMap.map_add, hmomentum, curlLinearMap.map_add, curlLinearMap.map_sub,
    curlLinearMap.map_smul, show curlLinearMap pressureJet = 0 from
      curlFromJacobian_eq_zero_of_symmetric hpressure, sub_zero]

/-- **The local incompressible vorticity balance at the second-jet grain.**

Pressure has departed through the symmetric-curl chain.  Vorticity transport and stretching remain
as distinct ordered terms.  An actual PDE theorem must additionally identify `timeJet` with the
time derivative of vorticity and `viscousJet` with its Laplacian jet. -/
theorem localVorticityBalance
    (H : SecondJet) (J timeJet viscousJet pressureJet forceJet : Matrix3)
    (u : Space) (ν : ℝ) (hH : HasMixedSpatialSymmetry H)
    (hdiv : divergenceFromJacobian J = 0)
    (hpressure : IsSymmetricJacobian pressureJet)
    (hmomentum :
      timeJet + advectionJacobianFromJets H J u =
        ν • viscousJet - pressureJet + forceJet) :
    curlFromJacobian timeJet + matrixAction (vorticityJacobianFromSecondJet H) u =
      matrixAction J (curlFromJacobian J) +
        ν • curlFromJacobian viscousJet + curlFromJacobian forceJet := by
  have hcurl := curl_differentiatedMomentum timeJet (advectionJacobianFromJets H J u)
    viscousJet pressureJet forceJet ν hpressure hmomentum
  rw [curl_advectionJacobian_of_incompressible H J u hH hdiv] at hcurl
  have hadd := congrArg (fun z : Space => z + matrixAction J (curlFromJacobian J)) hcurl
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd

end Soma.Holonics.Millennium.NavierStokesVorticity

section Audit
open Soma.Holonics.Millennium.NavierStokesVorticity
#print axioms cross_swap_is_zeroAnchoredSwing
#print axioms lambIdentity
#print axioms curlFromJacobian_eq_zero_iff
#print axioms curlAddHom_ker
#print axioms symmetricCurlChain_glues
#print axioms matrixAction_jacobianMatrix
#print axioms pointwiseLambIdentity
#print axioms velocityToVorticityOccurrence_target
#print axioms gradientJacobian_symmetric_of_contDiffAtTwo
#print axioms curl_gradient_eq_zero_of_symmetricDerivative
#print axioms curl_gradient_eq_zero
#print axioms spatialSlice_contDiffAt_of_contDiffOn_nonnegativeTime
#print axioms smoothSolution_velocitySlice_differentiableAt
#print axioms smoothSolution_velocityToVorticityOccurrence_target
#print axioms smoothSolution_pointwiseLambIdentity
#print axioms smoothSolution_pressureCurl_eq_zero
#print axioms secondJetAt_hasMixedSpatialSymmetry
#print axioms smoothSolution_velocitySlice_contDiffAtTwo
#print axioms smoothSolution_secondJet_hasMixedSpatialSymmetry
#print axioms divergenceFromJacobian_velocityJacobianAt
#print axioms smoothSolution_divergenceFromJacobian_eq_zero
#print axioms smoothSolution_velocityToVorticityJacobianOccurrence_target
#print axioms velocityJacobianAt_vorticity_eq_vorticityJacobianFromSecondJet
#print axioms smoothSolution_velocityJacobianAt_vorticity
#print axioms divergence_vorticityJacobian_eq_zero
#print axioms smoothSolution_divergence_vorticityAt_eq_zero
#print axioms curl_advectionJacobian
#print axioms curl_advectionJacobian_of_incompressible
#print axioms velocityJacobianAt_advection_eq_advectionJacobianFromJets
#print axioms smoothSolution_curl_advectionJacobian
#print axioms smoothSolution_velocityJacobianAt_advection
#print axioms smoothSolution_vorticityAt_advection
#print axioms curl_differentiatedMomentum
#print axioms localVorticityBalance
end Audit

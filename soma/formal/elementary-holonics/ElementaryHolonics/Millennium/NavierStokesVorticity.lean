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

/-! ## The nonlinear vorticity transport at one second-order jet -/

/-- A coordinate chart for the second spatial jet, with convention
`H i j k = ∂ₖ ∂ⱼ uᵢ`. -/
abbrev SecondJet := Fin 3 → Fin 3 → Fin 3 → ℝ

/-- The derivative directions of a genuine second jet commute. -/
def HasMixedSpatialSymmetry (H : SecondJet) : Prop :=
  ∀ i j k, H i j k = H i k j

/-- The trace/divergence face of one Jacobian chart. -/
def divergenceFromJacobian (J : Matrix3) : ℝ :=
  ∑ i : Fin 3, J i i

/-- The Jacobian of vorticity induced by a second velocity jet. -/
def vorticityJacobianFromSecondJet (H : SecondJet) : Matrix3 := ![
  fun k => H 2 1 k - H 1 2 k,
  fun k => H 0 2 k - H 2 0 k,
  fun k => H 1 0 k - H 0 1 k]

/-- The product-rule Jacobian of the advective field `(u · ∇)u`, expressed entirely in the local
velocity value, first jet, and second jet. -/
def advectionJacobianFromJets (H : SecondJet) (J : Matrix3) (u : Space) : Matrix3 :=
  fun i k => ∑ j : Fin 3, (J j k * J i j + u j * H i j k)

/-- Vorticity constructed from a mixed-symmetric second jet is divergence-free. -/
theorem divergence_vorticityJacobian_eq_zero (H : SecondJet)
    (hH : HasMixedSpatialSymmetry H) :
    divergenceFromJacobian (vorticityJacobianFromSecondJet H) = 0 := by
  simp [divergenceFromJacobian, vorticityJacobianFromSecondJet, Fin.sum_univ_succ]
  rw [hH 2 1 0, hH 1 2 0, hH 0 2 1]
  ring

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
#print axioms divergence_vorticityJacobian_eq_zero
#print axioms curl_advectionJacobian
#print axioms curl_advectionJacobian_of_incompressible
#print axioms curl_differentiatedMomentum
#print axioms localVorticityBalance
end Audit

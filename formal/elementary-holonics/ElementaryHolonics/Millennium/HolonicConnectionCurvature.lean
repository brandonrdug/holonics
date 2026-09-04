import ElementaryHolonics.Millennium.HolonicFourForceSectorCarrier
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Curvature itself: `F = dA + A ∧ A`, the covariant derivative, and the Bianchi return

The tree carried curvature only as a returned holonomy defect on an addressed face
(`HolonicComposition.routeComparisonReturn`, `HolonicFourForceSectorCarrier.returnedCurvature`)
and, in Rust, as the abelian `F = da` with the commutator `a ∧ a` measured but never differentiated.
This owner supplies the differential object.

A connection is one component `A_i : ℝⁿ → 𝔤` per coordinate direction, with `𝔤` any normed
algebra over `ℝ` and the bracket the ring commutator `[X, Y] = X Y − Y X`.  Its curvature is

```text
F_ij = ∂_i A_j − ∂_j A_i + [A_i, A_j],
```

its covariant derivative on a `𝔤`-valued section is `D_i X = ∂_i X + [A_i, X]`, and the Bianchi
identity `D_i F_jk + D_j F_ki + D_k F_ij = 0` is proved for every `C²` connection.  The proof spends
exactly two facts: the symmetry of second differential derivatives and the Jacobi identity of the
commutator.  Nothing else enters.  When the components commute the curvature is `dA`, which is the
abelian `F = da` the Rust body already carries.

The discrete face of the same object is gauge covariance of the returned holonomy: transforming
every edge transport by vertex elements `g` conjugates the face return by `g` at the face's
basepoint.  That is proved here on the existing four-force carrier, so the continuum curvature and
the cellular return are two readings of one connection.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicConnectionCurvature

/-! ## The continuum connection -/

section Continuum

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- The base chart: `n` real coordinates. -/
abbrev Base (n : ℕ) := Fin n → ℝ

/-- The unit direction of one coordinate. -/
def direction (i : Fin n) : Base n := Pi.single i 1

/-- The differential along one coordinate direction. -/
def differential (i : Fin n) (f : Base n → 𝔤) : Base n → 𝔤 :=
  fun x => fderiv ℝ f x (direction i)

/-- The ring commutator. -/
def bracket (X Y : 𝔤) : 𝔤 := X * Y - Y * X

/-- A connection: one `𝔤`-valued component per coordinate direction. -/
abbrev Connection (n : ℕ) (𝔤 : Type*) := Fin n → Base n → 𝔤

/-- **Curvature itself.**  `F_ij = ∂_i A_j − ∂_j A_i + [A_i, A_j]`. -/
def curvature (A : Connection n 𝔤) (i j : Fin n) : Base n → 𝔤 :=
  fun x => differential i (A j) x - differential j (A i) x + bracket (A i x) (A j x)

/-- The covariant derivative of a `𝔤`-valued section: `D_i X = ∂_i X + [A_i, X]`. -/
def covariantDerivative (A : Connection n 𝔤) (i : Fin n) (X : Base n → 𝔤) : Base n → 𝔤 :=
  fun x => differential i X x + bracket (A i x) (X x)

theorem curvature_antisymm (A : Connection n 𝔤) (i j : Fin n) (x : Base n) :
    curvature A j i x = -curvature A i j x := by
  simp only [curvature, bracket]; abel

theorem curvature_self (A : Connection n 𝔤) (i : Fin n) (x : Base n) :
    curvature A i i x = 0 := by
  simp [curvature, bracket]

/-- When the two components commute the curvature is the abelian `dA`. -/
theorem curvature_eq_of_commute (A : Connection n 𝔤) (i j : Fin n) (x : Base n)
    (h : Commute (A i x) (A j x)) :
    curvature A i j x = differential i (A j) x - differential j (A i) x := by
  simp [curvature, bracket, h.eq]

/-! ### Derivative lemmas -/

theorem differential_eq_hasFDerivAt {f : Base n → 𝔤} {L : Base n →L[ℝ] 𝔤} {x : Base n}
    (hf : HasFDerivAt f L x) (i : Fin n) : differential i f x = L (direction i) := by
  simp [differential, hf.fderiv]

theorem differentiableAt_of_contDiff {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (x : Base n) :
    DifferentiableAt ℝ f x :=
  (hf.differentiable (by norm_num)).differentiableAt

theorem differentiable_fderiv_of_contDiff {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero

theorem hasFDerivAt_differential {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (j : Fin n)
    (x : Base n) :
    HasFDerivAt (differential j f) ((fderiv ℝ (fderiv ℝ f) x).flip (direction j)) x := by
  have h := ((differentiable_fderiv_of_contDiff hf) x).hasFDerivAt.clm_apply
    (hasFDerivAt_const (direction j) x)
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  exact h

theorem differentiableAt_differential {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (j : Fin n)
    (x : Base n) : DifferentiableAt ℝ (differential j f) x :=
  (hasFDerivAt_differential hf j x).differentiableAt

/-- Second differentials of a `C²` section commute. -/
theorem differential_differential_comm {f : Base n → 𝔤} (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : Base n) :
    differential i (differential j f) x = differential j (differential i f) x := by
  rw [differential_eq_hasFDerivAt (hasFDerivAt_differential hf j x),
    differential_eq_hasFDerivAt (hasFDerivAt_differential hf i x)]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) (direction i) (direction j)

theorem differential_sub {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y - g y) x = differential i f x - differential i g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.sub hg.hasFDerivAt) i).trans ?_
  simp [differential]

theorem differential_add {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y + g y) x = differential i f x + differential i g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.add hg.hasFDerivAt) i).trans ?_
  simp [differential]

/-- The Leibniz law in the noncommutative algebra, hands retained. -/
theorem differential_mul {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => f y * g y) x = f x * differential i g x + differential i f x * g x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.mul' hg.hasFDerivAt) i).trans ?_
  simp [differential, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    add_apply, smul_apply]

theorem differential_bracket {f g : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    differential i (fun y => bracket (f y) (g y)) x =
      bracket (differential i f x) (g x) + bracket (f x) (differential i g x) := by
  simp only [bracket]
  refine (differential_eq_hasFDerivAt ((hf.hasFDerivAt.mul' hg.hasFDerivAt).sub
    (hg.hasFDerivAt.mul' hf.hasFDerivAt)) i).trans ?_
  simp [differential, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    add_apply, sub_apply, smul_apply]
  abel

/-- The differential of the curvature, expanded into second differentials and brackets. -/
theorem differential_curvature (A : Connection n 𝔤) (hA : ∀ i, ContDiff ℝ 2 (A i))
    (i j k : Fin n) (x : Base n) :
    differential i (curvature A j k) x =
      differential i (differential j (A k)) x - differential i (differential k (A j)) x +
        (bracket (differential i (A j) x) (A k x) + bracket (A j x) (differential i (A k) x)) := by
  have hj := differentiableAt_of_contDiff (hA j) x
  have hk := differentiableAt_of_contDiff (hA k) x
  refine (differential_eq_hasFDerivAt
    (((hasFDerivAt_differential (hA k) j x).sub (hasFDerivAt_differential (hA j) k x)).add
      ((hj.hasFDerivAt.mul' hk.hasFDerivAt).sub (hk.hasFDerivAt.mul' hj.hasFDerivAt))) i).trans ?_
  rw [differential_eq_hasFDerivAt (hasFDerivAt_differential (hA k) j x) i,
    differential_eq_hasFDerivAt (hasFDerivAt_differential (hA j) k x) i]
  simp [differential, bracket, smul_eq_mul, ContinuousLinearMap.smulRight_apply,
    add_apply, sub_apply, smul_apply,
    ContinuousLinearMap.flip_apply]
  abel

/-- **The Bianchi return.**  `D_i F_jk + D_j F_ki + D_k F_ij = 0` for every `C²` connection.
The second derivatives cancel by symmetry; the triple brackets cancel by Jacobi. -/
theorem bianchi (A : Connection n 𝔤) (hA : ∀ i, ContDiff ℝ 2 (A i)) (i j k : Fin n)
    (x : Base n) :
    covariantDerivative A i (curvature A j k) x + covariantDerivative A j (curvature A k i) x +
      covariantDerivative A k (curvature A i j) x = 0 := by
  simp only [covariantDerivative]
  rw [differential_curvature A hA i j k, differential_curvature A hA j k i,
    differential_curvature A hA k i j]
  rw [differential_differential_comm (hA k) j i, differential_differential_comm (hA j) k i,
    differential_differential_comm (hA i) k j]
  simp only [curvature, bracket]
  noncomm_ring

end Continuum

/-! ## The discrete face: gauge covariance of the returned curvature -/

section Discrete

open Soma.Holonics.Millennium.HolonicFourForceSectorCarrier
open Soma.Holonics.Millennium.HolonicComposition
open Soma.Holonics.Millennium.HolonicFourTorusCarrier

variable {grain : ℕ}

/-- A vertex gauge: one fibre automorphism per sector and vertex. -/
abbrev VertexGauge (carrier : FourForceCarrier grain) :=
  (sector : ForceSector) → Vertex grain → Equiv.Perm (carrier.InternalFibre sector)

/-- The gauge-transformed carrier: every edge transport is conjugated by the vertex gauge at
its target and source, `U'_e = g(target e) · U_e · g(source e)⁻¹`. -/
def gaugeTransform (carrier : FourForceCarrier grain) (g : VertexGauge carrier) :
    FourForceCarrier grain where
  InternalFibre := carrier.InternalFibre
  connection sector edge :=
    g sector (stepVertex edge.direction edge.base) * carrier.connection sector edge *
      (g sector edge.base)⁻¹

/-- The face identity in any group: conjugating each of the four edge transports by vertex
elements conjugates the ordered face word by the element at the far vertex. -/
theorem gauge_face_identity {G : Type*} [Group G] (a b c d u₁ u₂ u₃ u₄ : G) :
    a * u₁ * b⁻¹ * (b * u₂ * c⁻¹ * ((d * u₃ * c⁻¹)⁻¹ * (a * u₄ * d⁻¹)⁻¹)) =
      a * (u₁ * (u₂ * (u₃⁻¹ * u₄⁻¹))) * a⁻¹ := by
  group

/-- **Curvature is a tensor under rebase.**  The returned holonomy of the transformed carrier is
the original return conjugated by the gauge at the face's far vertex. -/
theorem returnedCurvature_gaugeTransform (carrier : FourForceCarrier grain)
    (g : VertexGauge carrier) (sector : ForceSector) (address : SixPlaneFace grain) :
    returnedCurvature (gaugeTransform carrier g) sector address =
      g sector (stepVertex address.2.directions.2 (stepVertex address.2.directions.1 address.1)) *
        returnedCurvature carrier sector address *
          (g sector (stepVertex address.2.directions.2
            (stepVertex address.2.directions.1 address.1)))⁻¹ := by
  have htop := stepVertex_commute address.2.directions.1 address.2.directions.2 address.1
    address.2.directions_ne
  simp only [returnedCurvature, sectorFaceWord, canonicalFace, gaugeTransform, parallelTransport,
    mul_one]
  rw [htop]
  exact gauge_face_identity _ _ _ _ _ _ _ _

/-- Flatness is gauge-invariant. -/
theorem returnedCurvature_gaugeTransform_eq_one_iff (carrier : FourForceCarrier grain)
    (g : VertexGauge carrier) (sector : ForceSector) (address : SixPlaneFace grain) :
    returnedCurvature (gaugeTransform carrier g) sector address = 1 ↔
      returnedCurvature carrier sector address = 1 := by
  have h := returnedCurvature_gaugeTransform carrier g sector address
  refine ⟨fun h1 => conj_eq_one_iff.mp (h.symm.trans h1), fun h1 => h.trans ?_⟩
  rw [h1, mul_one, mul_inv_cancel]
  rfl

end Discrete

section Audit

#print axioms bianchi
#print axioms differential_differential_comm
#print axioms curvature_eq_of_commute
#print axioms gauge_face_identity
#print axioms returnedCurvature_gaugeTransform
#print axioms returnedCurvature_gaugeTransform_eq_one_iff

end Audit

end Soma.Holonics.Millennium.HolonicConnectionCurvature

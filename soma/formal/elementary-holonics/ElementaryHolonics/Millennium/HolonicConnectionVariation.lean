import ElementaryHolonics.Millennium.HolonicConnectionCurvature

/-!
# The first variation of curvature and the Ricci identity

Two exact identities of the continuum connection, both pointwise and both spent on nothing but
the Leibniz law and the symmetry of second differentials:

* **the first variation of curvature**, `F(A + B)_ij = F(A)_ij + (D_A B)_ij + [B_i, B_j]` with
  `(D_A B)_ij = D_i B_j − D_j B_i`, so a perturbation of the connection moves the curvature by its
  covariant exterior derivative at first order and by its own commutator at second order; and
* **the Ricci identity**, `D_i D_j X − D_j D_i X = [F_ij, X]`: the curvature is exactly the
  failure of covariant derivatives to commute.

These are the two identities the Yang--Mills heat flow spends: the flow direction is a
perturbation, and the evolution of curvature under it is a covariant Laplacian plus commutators
with `F`.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.HolonicConnectionVariation

open Soma.Holonics.Millennium.HolonicConnectionCurvature

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

theorem differential_smul {f : Base n → 𝔤} {x : Base n} (hf : DifferentiableAt ℝ f x) (c : ℝ)
    (i : Fin n) :
    differential i (fun y => c • f y) x = c • differential i f x := by
  refine (differential_eq_hasFDerivAt (hf.hasFDerivAt.const_smul c) i).trans ?_
  simp [differential]

theorem bracket_smul_left (c : ℝ) (X Y : 𝔤) : bracket (c • X) Y = c • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

theorem bracket_smul_right (c : ℝ) (X Y : 𝔤) : bracket X (c • Y) = c • bracket X Y := by
  simp only [bracket, smul_mul_assoc, mul_smul_comm, smul_sub]

/-- The covariant exterior derivative of a perturbation: `(D_A B)_ij = D_i B_j − D_j B_i`. -/
def covariantVariation (A B : Connection n 𝔤) (i j : Fin n) : Base n → 𝔤 :=
  fun x => covariantDerivative A i (B j) x - covariantDerivative A j (B i) x

/-- **The first variation of curvature.**
`F(A + B)_ij = F(A)_ij + (D_A B)_ij + [B_i, B_j]`. -/
theorem curvature_add (A B : Connection n 𝔤) (hA : ∀ i x, DifferentiableAt ℝ (A i) x)
    (hB : ∀ i x, DifferentiableAt ℝ (B i) x) (i j : Fin n) (x : Base n) :
    curvature (fun k y => A k y + B k y) i j x =
      curvature A i j x + covariantVariation A B i j x + bracket (B i x) (B j x) := by
  simp only [curvature, covariantVariation, covariantDerivative]
  rw [differential_add (hA j x) (hB j x), differential_add (hA i x) (hB i x)]
  simp only [bracket]
  noncomm_ring

theorem covariantDerivative_smul (A : Connection n 𝔤) (i : Fin n) {X : Base n → 𝔤}
    (hX : ∀ x, DifferentiableAt ℝ X x) (c : ℝ) (x : Base n) :
    covariantDerivative A i (fun y => c • X y) x = c • covariantDerivative A i X x := by
  simp only [covariantDerivative]
  rw [differential_smul (hX x) c i, bracket_smul_right, smul_add]

/-- **The scaled first variation**: `F(A + εB) = F(A) + ε (D_A B) + ε² [B, B]`. -/
theorem curvature_add_smul (A B : Connection n 𝔤) (hA : ∀ i x, DifferentiableAt ℝ (A i) x)
    (hB : ∀ i x, DifferentiableAt ℝ (B i) x) (ε : ℝ) (i j : Fin n) (x : Base n) :
    curvature (fun k y => A k y + ε • B k y) i j x =
      curvature A i j x + ε • covariantVariation A B i j x +
        (ε * ε) • bracket (B i x) (B j x) := by
  have hεB : ∀ i x, DifferentiableAt ℝ (fun y => ε • B i y) x :=
    fun i x => (hB i x).const_smul ε
  rw [curvature_add A (fun k y => ε • B k y) hA hεB i j x]
  simp only [covariantVariation]
  rw [covariantDerivative_smul A i (fun x => hB j x) ε x, covariantDerivative_smul A j (fun x => hB i x) ε x,
    bracket_smul_left, bracket_smul_right, smul_smul, smul_sub]

/-- **The Ricci identity**: `D_i D_j X − D_j D_i X = [F_ij, X]`. -/
theorem ricci (A : Connection n 𝔤) (hA : ∀ i x, DifferentiableAt ℝ (A i) x) (X : Base n → 𝔤)
    (hX : ContDiff ℝ 2 X) (i j : Fin n) (x : Base n) :
    covariantDerivative A i (covariantDerivative A j X) x -
        covariantDerivative A j (covariantDerivative A i X) x =
      bracket (curvature A i j x) (X x) := by
  unfold covariantDerivative
  have hXd := differentiableAt_of_contDiff hX x
  have hdj := differentiableAt_differential hX j x
  have hdi := differentiableAt_differential hX i x
  have hbj : DifferentiableAt ℝ (fun y => bracket (A j y) (X y)) x :=
    ((hA j x).mul hXd).sub (hXd.mul (hA j x))
  have hbi : DifferentiableAt ℝ (fun y => bracket (A i y) (X y)) x :=
    ((hA i x).mul hXd).sub (hXd.mul (hA i x))
  rw [differential_add hdj hbj, differential_add hdi hbi, differential_bracket (hA j x) hXd,
    differential_bracket (hA i x) hXd, differential_differential_comm hX j i]
  simp only [curvature, bracket]
  noncomm_ring

section Audit

#print axioms curvature_add
#print axioms curvature_add_smul
#print axioms ricci

end Audit

end Soma.Holonics.Millennium.HolonicConnectionVariation

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Hodge receiver: a weighted cochain complex, its Laplacian, and the three-way decomposition

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/hodge_receiver.rs` implements. It is receiver **R3** of
`docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`. Six things are stated here, in
this order.

1. **The weighted complex.** Three consecutive grades of a finite cochain complex over `ℚ`, with
   `d₁ ∘ d₀ = 0` and a **declared positive rational weight per cell** at each grade. The weights
   are fields of the structure and carry their own positivity hypotheses: there is no default
   metric here, and the unit weights are one inhabitant of this structure among others. This is
   exactly the Rust owner's `MetricLaw`, whose `Unit` case is a declaration and not an absence.
2. **The codifferential is the metric adjoint.** `codiff₀ = W₀⁻¹ d₀ᵀ W₁` and
   `codiff₁ = W₁⁻¹ d₁ᵀ W₂`, characterized by `⟪d₀ x, y⟫₁ = ⟪x, codiff₀ y⟫₀` and
   `⟪codiff₁ v, y⟫₁ = ⟪v, d₁ y⟫₂` (`codiff₀_adjoint`, `codiff₁_adjoint`). A bare transpose is
   this object only when every weight is one, which is a declaration nobody has to make.
3. **The Laplacian is self-adjoint and positive semidefinite in the declared inner product.**
   `laplacian_selfAdjoint`, and the exact identity
   `⟪Δ x, x⟫₁ = ⟪codiff₀ x, codiff₀ x⟫₀ + ⟪d₁ x, d₁ x⟫₂` (`laplacian_quadratic`), from which
   positivity is immediate (`laplacian_posSemidef`) and from which
   `ker Δ = ker d₁ ∩ ker codiff₀` follows with no analysis (`mem_harmonic_iff`).
4. **The three-way orthogonal decomposition.** `im d₀`, `im codiff₁` and `ker Δ` are pairwise
   orthogonal (`exact_orthogonal_coexact`, `harmonic_orthogonal_exact`,
   `harmonic_orthogonal_coexact`) and every cochain is their sum, uniquely
   (`hodge_decomposition`, `hodge_decomposition_unique`). `d₁ ∘ d₀ = 0` is what makes the first
   orthogonality hold, and positive definiteness of the declared inner product is what makes the
   three intersect trivially. Mathlib owns the step from "a subspace meets its orthogonal
   complement trivially" to "it is a complement of it"
   (`LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint`), and it is used rather than repeated.
5. **The harmonic space is the cohomology.** Every cocycle is congruent to exactly one harmonic
   cochain modulo the exact ones (`harmonic_meets_every_class`,
   `harmonic_representative_unique`), packaged as the linear equivalence
   `harmonicEquivCohomology`, and counted by
   `finrank_harmonic_add_finrank_exact`. That count is the Betti number the Rust owner checks
   against the Smith normal form over `ℤ` — over `ℚ`, so torsion is invisible to it, which is
   why the Rust reading carries the torsion coefficients separately.
6. **A metric change moves the representative and not the dimension.**
   `harmonic_moves_within_class` says two metrics on one complex return harmonic representatives
   of the *same* cohomology class, and `finrank_harmonic_metric_free` says the harmonic dimension
   does not depend on the weights at all. The Rust test exhibits a change that genuinely moves the
   representative; what is proved here is that it cannot leave the class or change the count.

[proved-derived; formal-checked] Nothing above needs completeness, an analytic limit, or a real
inner product space. The field is `ℚ`, the form is the declared diagonal one, and every statement
is finite linear algebra.

Rust owner: `crates/holonic-engine/src/hodge_receiver.rs`
(`MetricLaw`, `CellMetric`, `BoundaryCondition`, `HodgeOperator::codifferential`,
`HodgeOperator::laplacian`, `hodge_decomposition`, `hodge_reading`, `exact_hodge_spectrum`,
`hodge_family`).
-/

noncomputable section

namespace Soma.Holonics.Foundation.HodgeReceiver

open Matrix Finset Module

variable {n p q r : ℕ}

/-! ## The declared inner product -/

/-- [definition] The inner product declared by a positive weight per cell. The Rust owner's
`HodgeOperator::inner`. -/
def ip (w : Fin n → ℚ) (x y : Fin n → ℚ) : ℚ := ∑ i, w i * (x i * y i)

theorem ip_symm (w x y : Fin n → ℚ) : ip w x y = ip w y x := by
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem ip_add_left (w x y z : Fin n → ℚ) : ip w (x + y) z = ip w x z + ip w y z := by
  simp only [ip, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_smul_left (c : ℚ) (w x y : Fin n → ℚ) : ip w (c • x) y = c * ip w x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_add_right (w x y z : Fin n → ℚ) : ip w x (y + z) = ip w x y + ip w x z := by
  simp only [ip, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_smul_right (c : ℚ) (w x y : Fin n → ℚ) : ip w x (c • y) = c * ip w x y := by
  simp only [ip, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem ip_sub_left (w x y z : Fin n → ℚ) : ip w (x - y) z = ip w x z - ip w y z := by
  simp only [ip, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

@[simp]
theorem ip_zero_left (w y : Fin n → ℚ) : ip w 0 y = 0 := by
  simp [ip]

/-- [proved-derived; formal-checked] A declared positive metric is positive semidefinite. -/
theorem ip_self_nonneg {w : Fin n → ℚ} (hw : ∀ i, 0 < w i) (x : Fin n → ℚ) : 0 ≤ ip w x x :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (mul_self_nonneg _)

/-- [proved-derived; formal-checked] **A declared positive metric is definite.** This is the single
fact that makes every projection below exist and be unique, and it is why a non-positive weight is
refused by name in the Rust owner rather than used. -/
theorem ip_eq_zero {w : Fin n → ℚ} (hw : ∀ i, 0 < w i) {x : Fin n → ℚ} (h : ip w x x = 0) :
    x = 0 := by
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ w i * (x i * x i) := fun i _ =>
    mul_nonneg (hw i).le (mul_self_nonneg _)
  funext i
  have hterm : w i * (x i * x i) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
  have hsq : x i * x i = 0 := by
    rcases mul_eq_zero.mp hterm with h' | h'
    · exact absurd h' (ne_of_gt (hw i))
    · exact h'
  simpa using mul_self_eq_zero.mp hsq

/-! ## The weighted complex -/

/-- [definition] Three consecutive grades of a finite cochain complex over `ℚ` with a **declared**
positive rational weight per cell at each grade.

`d₀ : C^(k−1) → C^k` and `d₁ : C^k → C^(k+1)`, and `dd` is `d ∘ d = 0`, which the Rust owner
re-derives at every founding rather than assuming. -/
structure WeightedComplex (p q r : ℕ) where
  d₀ : Matrix (Fin q) (Fin p) ℚ
  d₁ : Matrix (Fin r) (Fin q) ℚ
  w₀ : Fin p → ℚ
  w₁ : Fin q → ℚ
  w₂ : Fin r → ℚ
  w₀pos : ∀ i, 0 < w₀ i
  w₁pos : ∀ i, 0 < w₁ i
  w₂pos : ∀ i, 0 < w₂ i
  dd : d₁ * d₀ = 0

namespace WeightedComplex

variable (C : WeightedComplex p q r)

/-- [definition] `codiff₀ = W₀⁻¹ d₀ᵀ W₁ : C^k → C^(k−1)`, the metric adjoint of `d₀`. -/
def codiff₀ : Matrix (Fin p) (Fin q) ℚ := fun i j => C.w₁ j * C.d₀ j i / C.w₀ i

/-- [definition] `codiff₁ = W₁⁻¹ d₁ᵀ W₂ : C^(k+1) → C^k`, the metric adjoint of `d₁`. -/
def codiff₁ : Matrix (Fin q) (Fin r) ℚ := fun i j => C.w₂ j * C.d₁ j i / C.w₁ i

/-- [proved-derived; formal-checked] **The adjoint characterization of `codiff₀`.**
`⟪d₀ x, y⟫₁ = ⟪x, codiff₀ y⟫₀`. A bare transpose satisfies this only when every weight is one. -/
theorem codiff₀_adjoint (x : Fin p → ℚ) (y : Fin q → ℚ) :
    ip C.w₁ (C.d₀ *ᵥ x) y = ip C.w₀ x (C.codiff₀ *ᵥ y) := by
  have hL : ip C.w₁ (C.d₀ *ᵥ x) y = ∑ i, ∑ j, C.w₁ i * C.d₀ i j * x j * y i := by
    simp only [ip]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hR : ip C.w₀ x (C.codiff₀ *ᵥ y) = ∑ j, ∑ i, C.w₁ i * C.d₀ i j * x j * y i := by
    simp only [ip]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, codiff₀, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : C.w₀ j ≠ 0 := ne_of_gt (C.w₀pos j)
    field_simp
  rw [hL, hR]
  exact Finset.sum_comm

/-- [proved-derived; formal-checked] **The adjoint characterization of `codiff₁`.**
`⟪codiff₁ v, y⟫₁ = ⟪v, d₁ y⟫₂`. -/
theorem codiff₁_adjoint (v : Fin r → ℚ) (y : Fin q → ℚ) :
    ip C.w₁ (C.codiff₁ *ᵥ v) y = ip C.w₂ v (C.d₁ *ᵥ y) := by
  have hL : ip C.w₁ (C.codiff₁ *ᵥ v) y = ∑ i, ∑ j, C.w₂ j * C.d₁ j i * v j * y i := by
    simp only [ip]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, codiff₁, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : C.w₁ i ≠ 0 := ne_of_gt (C.w₁pos i)
    field_simp
  have hR : ip C.w₂ v (C.d₁ *ᵥ y) = ∑ j, ∑ i, C.w₂ j * C.d₁ j i * v j * y i := by
    simp only [ip]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hL, hR]
  exact Finset.sum_comm

/-- [definition] `Δ_k = d_(k−1) d_(k−1)^* + d_k^* d_k`. -/
def laplacian : Matrix (Fin q) (Fin q) ℚ := C.d₀ * C.codiff₀ + C.codiff₁ * C.d₁

theorem laplacian_mulVec (x : Fin q → ℚ) :
    C.laplacian *ᵥ x = C.d₀ *ᵥ (C.codiff₀ *ᵥ x) + C.codiff₁ *ᵥ (C.d₁ *ᵥ x) := by
  simp [laplacian, Matrix.add_mulVec, Matrix.mulVec_mulVec]

/-- [proved-derived; formal-checked] **The exact quadratic identity.** Nothing is estimated: the
Laplacian's form on a cochain is the sum of two squared norms. -/
theorem laplacian_quadratic (x : Fin q → ℚ) :
    ip C.w₁ (C.laplacian *ᵥ x) x
      = ip C.w₀ (C.codiff₀ *ᵥ x) (C.codiff₀ *ᵥ x) + ip C.w₂ (C.d₁ *ᵥ x) (C.d₁ *ᵥ x) := by
  rw [laplacian_mulVec, ip_add_left, C.codiff₀_adjoint, C.codiff₁_adjoint]

/-- [proved-derived; formal-checked] `Δ` is positive semidefinite in the declared inner product.
This is why the Rust owner may bound the whole spectrum by the trace. -/
theorem laplacian_posSemidef (x : Fin q → ℚ) : 0 ≤ ip C.w₁ (C.laplacian *ᵥ x) x := by
  rw [C.laplacian_quadratic]
  exact add_nonneg (ip_self_nonneg C.w₀pos _) (ip_self_nonneg C.w₂pos _)

/-- [proved-derived; formal-checked] `Δ` is self-adjoint in the declared inner product. Its
spectrum is therefore real, which is what makes the Rust owner's exact isolation complete. -/
theorem laplacian_selfAdjoint (x y : Fin q → ℚ) :
    ip C.w₁ (C.laplacian *ᵥ x) y = ip C.w₁ x (C.laplacian *ᵥ y) := by
  have hx : ip C.w₁ (C.laplacian *ᵥ x) y
      = ip C.w₀ (C.codiff₀ *ᵥ x) (C.codiff₀ *ᵥ y) + ip C.w₂ (C.d₁ *ᵥ x) (C.d₁ *ᵥ y) := by
    rw [laplacian_mulVec, ip_add_left, C.codiff₀_adjoint, C.codiff₁_adjoint]
  have hy : ip C.w₁ x (C.laplacian *ᵥ y)
      = ip C.w₀ (C.codiff₀ *ᵥ x) (C.codiff₀ *ᵥ y) + ip C.w₂ (C.d₁ *ᵥ x) (C.d₁ *ᵥ y) := by
    rw [ip_symm, laplacian_mulVec, ip_add_left, C.codiff₀_adjoint, C.codiff₁_adjoint,
      ip_symm C.w₀, ip_symm C.w₂]
  rw [hx, hy]

/-! ## The three subspaces -/

/-- [definition] `im d_(k−1)`: the exact cochains. -/
def exactPart : Submodule ℚ (Fin q → ℚ) := LinearMap.range (Matrix.mulVecLin C.d₀)

/-- [definition] `im d_k^*`: the coexact cochains. -/
def coexactPart : Submodule ℚ (Fin q → ℚ) := LinearMap.range (Matrix.mulVecLin C.codiff₁)

/-- [definition] `ker Δ_k`: the harmonic cochains. -/
def harmonic : Submodule ℚ (Fin q → ℚ) := LinearMap.ker (Matrix.mulVecLin C.laplacian)

/-- [definition] `ker d_k`: the cocycles. -/
def cocycles : Submodule ℚ (Fin q → ℚ) := LinearMap.ker (Matrix.mulVecLin C.d₁)

theorem mem_exactPart_iff (x : Fin q → ℚ) : x ∈ C.exactPart ↔ ∃ a, C.d₀ *ᵥ a = x := Iff.rfl

theorem mem_coexactPart_iff (x : Fin q → ℚ) : x ∈ C.coexactPart ↔ ∃ b, C.codiff₁ *ᵥ b = x :=
  Iff.rfl

theorem mem_cocycles_iff (x : Fin q → ℚ) : x ∈ C.cocycles ↔ C.d₁ *ᵥ x = 0 := Iff.rfl

/-- [proved-derived; formal-checked] **`ker Δ_k = ker d_k ∩ ker d_(k−1)^*`.** The two conditions
are not assumed separately and then intersected: they are *derived* from the single equation
`Δ x = 0` through the exact quadratic identity and the definiteness of the declared metric. -/
theorem mem_harmonic_iff (x : Fin q → ℚ) :
    x ∈ C.harmonic ↔ C.codiff₀ *ᵥ x = 0 ∧ C.d₁ *ᵥ x = 0 := by
  constructor
  · intro hx
    have hzero : C.laplacian *ᵥ x = 0 := hx
    have hq := C.laplacian_quadratic x
    rw [hzero, ip_zero_left] at hq
    have h₀ := ip_self_nonneg C.w₀pos (C.codiff₀ *ᵥ x)
    have h₂ := ip_self_nonneg C.w₂pos (C.d₁ *ᵥ x)
    exact ⟨ip_eq_zero C.w₀pos (by linarith), ip_eq_zero C.w₂pos (by linarith)⟩
  · rintro ⟨h₀, h₁⟩
    show C.laplacian *ᵥ x = 0
    rw [laplacian_mulVec, h₀, h₁]
    simp

/-- [proved-derived; formal-checked] The exact cochains are cocycles: this is `d ∘ d = 0`. -/
theorem exactPart_le_cocycles : C.exactPart ≤ C.cocycles := by
  rintro _ ⟨a, rfl⟩
  show C.d₁ *ᵥ (C.d₀ *ᵥ a) = 0
  rw [Matrix.mulVec_mulVec, C.dd, Matrix.zero_mulVec]

/-- [proved-derived; formal-checked] The harmonic cochains are cocycles. -/
theorem harmonic_le_cocycles : C.harmonic ≤ C.cocycles := fun _ hx =>
  ((C.mem_harmonic_iff _).mp hx).2

/-! ## Pairwise orthogonality -/

/-- [proved-derived; formal-checked] `im d₀ ⟂ im codiff₁`, and the only input is `d ∘ d = 0`. -/
theorem exact_orthogonal_coexact {a b : Fin q → ℚ} (ha : a ∈ C.exactPart)
    (hb : b ∈ C.coexactPart) : ip C.w₁ a b = 0 := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  simp only [Matrix.mulVecLin_apply]
  rw [ip_symm, C.codiff₁_adjoint, Matrix.mulVec_mulVec, C.dd, Matrix.zero_mulVec]
  simp [ip]

/-- [proved-derived; formal-checked] `ker Δ ⟂ im d₀`. -/
theorem harmonic_orthogonal_exact {h a : Fin q → ℚ} (hh : h ∈ C.harmonic) (ha : a ∈ C.exactPart) :
    ip C.w₁ a h = 0 := by
  obtain ⟨u, rfl⟩ := ha
  simp only [Matrix.mulVecLin_apply]
  rw [C.codiff₀_adjoint, ((C.mem_harmonic_iff h).mp hh).1]
  simp [ip]

/-- [proved-derived; formal-checked] `ker Δ ⟂ im codiff₁`. -/
theorem harmonic_orthogonal_coexact {h b : Fin q → ℚ} (hh : h ∈ C.harmonic)
    (hb : b ∈ C.coexactPart) : ip C.w₁ b h = 0 := by
  obtain ⟨v, rfl⟩ := hb
  simp only [Matrix.mulVecLin_apply]
  rw [C.codiff₁_adjoint, ((C.mem_harmonic_iff h).mp hh).2]
  simp [ip]

/-! ## The declared inner product as a bilinear form -/

/-- [definition] The declared inner product as a `BilinForm`, so that Mathlib's orthogonal
complement machinery applies to it. -/
def form : LinearMap.BilinForm ℚ (Fin q → ℚ) :=
  LinearMap.mk₂ ℚ (fun x y => ip C.w₁ x y) (ip_add_left C.w₁) (fun c x y => ip_smul_left c C.w₁ x y)
    (ip_add_right C.w₁) fun c x y => ip_smul_right c C.w₁ x y

@[simp]
theorem form_apply (x y : Fin q → ℚ) : C.form x y = ip C.w₁ x y := rfl

theorem form_isRefl : C.form.IsRefl := fun x y h => by
  rw [form_apply] at h ⊢
  rwa [ip_symm]

/-- [proved-derived; formal-checked] A subspace meets its orthogonal complement trivially, because
the declared metric is definite. -/
theorem disjoint_orthogonal (W : Submodule ℚ (Fin q → ℚ)) :
    Disjoint W (C.form.orthogonal W) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  exact ip_eq_zero C.w₁pos (by simpa using hx' x hx)

/-- [proved-derived; formal-checked] Hence it is a complement of it. Mathlib owns this step. -/
theorem isCompl_orthogonal (W : Submodule ℚ (Fin q → ℚ)) :
    IsCompl W (C.form.orthogonal W) :=
  (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint C.form_isRefl).mpr (C.disjoint_orthogonal W)

/-- [proved-derived; formal-checked] **The harmonic space is exactly the orthogonal complement of
the exact and coexact parts together.** Both directions are elementary: one is the pairwise
orthogonality above, and the other reads the two kernel conditions back off the quadratic
identity. -/
theorem harmonic_eq_orthogonal :
    C.harmonic = C.form.orthogonal (C.exactPart ⊔ C.coexactPart) := by
  ext h
  simp only [LinearMap.BilinForm.mem_orthogonal_iff, form_apply]
  constructor
  · intro hh n hn
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hn
    rw [ip_add_left, C.harmonic_orthogonal_exact hh ha, C.harmonic_orthogonal_coexact hh hb,
      add_zero]
  · intro hh
    rw [mem_harmonic_iff]
    have hexact : ip C.w₀ (C.codiff₀ *ᵥ h) (C.codiff₀ *ᵥ h) = 0 := by
      rw [← C.codiff₀_adjoint]
      exact hh _ (Submodule.mem_sup_left ⟨_, rfl⟩)
    have hcoexact : ip C.w₂ (C.d₁ *ᵥ h) (C.d₁ *ᵥ h) = 0 := by
      rw [← C.codiff₁_adjoint]
      exact hh _ (Submodule.mem_sup_right ⟨_, rfl⟩)
    exact ⟨ip_eq_zero C.w₀pos hexact, ip_eq_zero C.w₂pos hcoexact⟩

/-! ## The decomposition -/

/-- [proved-derived; formal-checked] **The Hodge decomposition.** Every cochain is an exact part
plus a coexact part plus a harmonic part. -/
theorem hodge_decomposition (x : Fin q → ℚ) :
    ∃ a ∈ C.exactPart, ∃ b ∈ C.coexactPart, ∃ h ∈ C.harmonic, x = a + b + h := by
  have hcompl := C.isCompl_orthogonal (C.exactPart ⊔ C.coexactPart)
  rw [← C.harmonic_eq_orthogonal] at hcompl
  obtain ⟨u, hu, h, hh, rfl⟩ :=
    Submodule.mem_sup.mp (by simpa using (hcompl.sup_eq_top ▸ Submodule.mem_top : x ∈ _))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
  exact ⟨a, ha, b, hb, h, hh, rfl⟩

/-- [proved-derived; formal-checked] **And it is unique.** The three parts are pairwise orthogonal
and the metric is definite, so each difference pairs with itself to zero. -/
theorem hodge_decomposition_unique {a b h a' b' h' : Fin q → ℚ} (ha : a ∈ C.exactPart)
    (hb : b ∈ C.coexactPart) (hh : h ∈ C.harmonic) (ha' : a' ∈ C.exactPart)
    (hb' : b' ∈ C.coexactPart) (hh' : h' ∈ C.harmonic) (heq : a + b + h = a' + b' + h') :
    a = a' ∧ b = b' ∧ h = h' := by
  have hu : a - a' ∈ C.exactPart := C.exactPart.sub_mem ha ha'
  have hv : b - b' ∈ C.coexactPart := C.coexactPart.sub_mem hb hb'
  have hk : h - h' ∈ C.harmonic := C.harmonic.sub_mem hh hh'
  have hsum : (a - a') + (b - b') + (h - h') = 0 := by
    have hz : a + b + h - (a' + b' + h') = 0 := by rw [heq]; ring
    calc (a - a') + (b - b') + (h - h') = a + b + h - (a' + b' + h') := by ring
      _ = 0 := hz
  have hzero : ∀ z : Fin q → ℚ, ip C.w₁ z ((a - a') + (b - b') + (h - h')) = 0 := by
    intro z; rw [hsum]; simp [ip]
  have hA : a - a' = 0 := by
    have := hzero (a - a')
    rw [ip_add_right, ip_add_right, C.exact_orthogonal_coexact hu hv,
      C.harmonic_orthogonal_exact hk hu, add_zero, add_zero] at this
    exact ip_eq_zero C.w₁pos this
  have hB : b - b' = 0 := by
    have := hzero (b - b')
    rw [ip_add_right, ip_add_right, ip_symm, C.exact_orthogonal_coexact hu hv,
      C.harmonic_orthogonal_coexact hk hv, add_zero, zero_add] at this
    exact ip_eq_zero C.w₁pos this
  have hH : h - h' = 0 := by
    have := hzero (h - h')
    rw [ip_add_right, ip_add_right, ip_symm C.w₁ (h - h') (a - a'),
      C.harmonic_orthogonal_exact hk hu, ip_symm C.w₁ (h - h') (b - b'),
      C.harmonic_orthogonal_coexact hk hv, zero_add, zero_add] at this
    exact ip_eq_zero C.w₁pos this
  exact ⟨sub_eq_zero.mp hA, sub_eq_zero.mp hB, sub_eq_zero.mp hH⟩

/-! ## The harmonic space is the cohomology -/

/-- [proved-derived; formal-checked] A coexact cocycle is zero: its own norm is its pairing with
`d₁` of itself. -/
theorem coexact_cocycle_eq_zero {b : Fin q → ℚ} (hb : b ∈ C.coexactPart)
    (hcycle : C.d₁ *ᵥ b = 0) : b = 0 := by
  obtain ⟨v, rfl⟩ := hb
  simp only [Matrix.mulVecLin_apply] at hcycle ⊢
  have hz : ip C.w₁ (C.codiff₁ *ᵥ v) (C.codiff₁ *ᵥ v) = 0 := by
    rw [C.codiff₁_adjoint, hcycle]
    simp [ip]
  exact ip_eq_zero C.w₁pos hz

/-- [proved-derived; formal-checked] **Every cocycle is cohomologous to a harmonic cochain.** -/
theorem harmonic_meets_every_class {z : Fin q → ℚ} (hz : z ∈ C.cocycles) :
    ∃ h ∈ C.harmonic, z - h ∈ C.exactPart := by
  obtain ⟨a, ha, b, hb, h, hh, rfl⟩ := C.hodge_decomposition z
  have hd : C.d₁ *ᵥ b = 0 := by
    have hzero : C.d₁ *ᵥ (a + b + h) = 0 := hz
    have hA : C.d₁ *ᵥ a = 0 := C.exactPart_le_cocycles ha
    have hH : C.d₁ *ᵥ h = 0 := ((C.mem_harmonic_iff h).mp hh).2
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hA, hH, zero_add, add_zero] at hzero
    exact hzero
  refine ⟨h, hh, ?_⟩
  rw [C.coexact_cocycle_eq_zero hb hd]
  simpa using ha

/-- [proved-derived; formal-checked] **And to exactly one.** -/
theorem harmonic_representative_unique {h h' : Fin q → ℚ} (hh : h ∈ C.harmonic)
    (hh' : h' ∈ C.harmonic) (hd : h - h' ∈ C.exactPart) : h = h' := by
  have hk : h - h' ∈ C.harmonic := C.harmonic.sub_mem hh hh'
  have : ip C.w₁ (h - h') (h - h') = 0 := C.harmonic_orthogonal_exact hk hd
  exact sub_eq_zero.mp (ip_eq_zero C.w₁pos this)

/-- [proved-derived; formal-checked] `ker d₁ = im d₀ ⊕ ker Δ`: the cocycles split into the exact
ones and the harmonic ones. -/
theorem cocycles_eq_sup : C.cocycles = C.exactPart ⊔ C.harmonic := by
  apply le_antisymm
  · intro z hz
    obtain ⟨h, hh, hd⟩ := C.harmonic_meets_every_class hz
    have hz' : z = (z - h) + h := by ring
    rw [hz']
    exact Submodule.add_mem_sup hd hh
  · exact sup_le C.exactPart_le_cocycles C.harmonic_le_cocycles

theorem disjoint_exact_harmonic : Disjoint C.exactPart C.harmonic := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  exact ip_eq_zero C.w₁pos (C.harmonic_orthogonal_exact hx' hx)

/-- [proved-derived; formal-checked] **The harmonic dimension is the Betti number.**
`dim ker Δ_k + dim im d_(k−1) = dim ker d_k`, which is the count the Rust owner checks against the
Smith normal form over `ℤ`. Over `ℚ`, so torsion contributes nothing to it. -/
theorem finrank_harmonic_add_finrank_exact :
    finrank ℚ C.harmonic + finrank ℚ C.exactPart = finrank ℚ C.cocycles := by
  have hdisj : C.exactPart ⊓ C.harmonic = ⊥ := disjoint_iff.mp C.disjoint_exact_harmonic
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq C.exactPart C.harmonic
  rw [hdisj, finrank_bot, add_zero, ← C.cocycles_eq_sup] at hsum
  omega

/-- [proved-derived; formal-checked] The two complementary pieces of `ker d₁`, seen inside it. -/
theorem isCompl_in_cocycles :
    IsCompl (C.exactPart.comap C.cocycles.subtype) (C.harmonic.comap C.cocycles.subtype) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro ⟨x, hx⟩ h₁ h₂
    have hx₁ : x ∈ C.exactPart := by simpa using h₁
    have hx₂ : x ∈ C.harmonic := by simpa using h₂
    exact Subtype.ext (Submodule.disjoint_def.mp C.disjoint_exact_harmonic x hx₁ hx₂)
  · rw [codisjoint_iff, eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ C.exactPart ⊔ C.harmonic := C.cocycles_eq_sup ▸ hx
    obtain ⟨a, ha, h, hh, hadd⟩ := Submodule.mem_sup.mp hx'
    have haC : a ∈ C.cocycles := C.exactPart_le_cocycles ha
    have hhC : h ∈ C.cocycles := C.harmonic_le_cocycles hh
    have hsplit : (⟨x, hx⟩ : C.cocycles) = ⟨a, haC⟩ + ⟨h, hhC⟩ := Subtype.ext hadd.symm
    rw [hsplit]
    exact Submodule.add_mem_sup (by simpa using ha) (by simpa using hh)

/-- [proved-derived; formal-checked] **The harmonic space *is* the cohomology, over `ℚ`.**
`H^k = ker d_k / im d_(k−1) ≃ ker Δ_k`. -/
def harmonicEquivCohomology :
    (C.cocycles ⧸ C.exactPart.comap C.cocycles.subtype) ≃ₗ[ℚ]
      C.harmonic.comap C.cocycles.subtype :=
  Submodule.quotientEquivOfIsCompl _ _ C.isCompl_in_cocycles

/-! ## What a metric change moves -/

/-- [proved-derived; formal-checked] **A metric change moves the representative inside its class.**
Two declared metrics on one complex return harmonic representatives of the same cohomology class:
their difference is exact. The Rust owner exhibits a change that genuinely moves it; what is proved
here is that it cannot leave the class. -/
theorem harmonic_moves_within_class (C' : WeightedComplex p q r) (hd₀ : C'.d₀ = C.d₀)
    {z h h' : Fin q → ℚ} (hzh : z - h ∈ C.exactPart) (hzh' : z - h' ∈ C'.exactPart) :
    h - h' ∈ C.exactPart := by
  have hexact : C'.exactPart = C.exactPart := by
    unfold exactPart; rw [hd₀]
  rw [hexact] at hzh'
  have hsplit : h - h' = (z - h') - (z - h) := by ring
  rw [hsplit]
  exact C.exactPart.sub_mem hzh' hzh

/-- [proved-derived; formal-checked] **And it does not move the dimension.** The harmonic dimension
is determined by `d₀` and `d₁` alone: the weights do not appear in `ker d₁` or in `im d₀`, and the
count above pins `dim ker Δ` between them. -/
theorem finrank_harmonic_metric_free (C' : WeightedComplex p q r) (hd₀ : C'.d₀ = C.d₀)
    (hd₁ : C'.d₁ = C.d₁) : finrank ℚ C'.harmonic = finrank ℚ C.harmonic := by
  have hexact : C'.exactPart = C.exactPart := by unfold exactPart; rw [hd₀]
  have hcocycles : C'.cocycles = C.cocycles := by unfold cocycles; rw [hd₁]
  have h := C'.finrank_harmonic_add_finrank_exact
  have h' := C.finrank_harmonic_add_finrank_exact
  rw [hexact, hcocycles] at h
  omega

end WeightedComplex

/-! ## The unit metric is one declaration among others -/

/-- [definition] The unit metric, **declared**. It is an inhabitant of the same structure as every
other metric, carrying its own positivity proofs; nothing in this file reaches it by default. -/
def unitMetric (d₀ : Matrix (Fin q) (Fin p) ℚ) (d₁ : Matrix (Fin r) (Fin q) ℚ)
    (dd : d₁ * d₀ = 0) : WeightedComplex p q r where
  d₀ := d₀
  d₁ := d₁
  w₀ := fun _ => 1
  w₁ := fun _ => 1
  w₂ := fun _ => 1
  w₀pos := fun _ => one_pos
  w₁pos := fun _ => one_pos
  w₂pos := fun _ => one_pos
  dd := dd

/-- [proved-derived; formal-checked] Under the unit metric, and only there, the codifferential is
the bare transpose. -/
theorem unitMetric_codiff₀ (d₀ : Matrix (Fin q) (Fin p) ℚ) (d₁ : Matrix (Fin r) (Fin q) ℚ)
    (dd : d₁ * d₀ = 0) : (unitMetric d₀ d₁ dd).codiff₀ = d₀ᵀ := by
  funext i j
  simp [unitMetric, WeightedComplex.codiff₀, Matrix.transpose_apply]

end Soma.Holonics.Foundation.HodgeReceiver

namespace Soma.Holonics.Foundation.HodgeReceiver

section Audit

#print axioms ip_symm
#print axioms ip_eq_zero
#print axioms WeightedComplex.codiff₀_adjoint
#print axioms WeightedComplex.codiff₁_adjoint
#print axioms WeightedComplex.laplacian_quadratic
#print axioms WeightedComplex.laplacian_posSemidef
#print axioms WeightedComplex.laplacian_selfAdjoint
#print axioms WeightedComplex.mem_harmonic_iff
#print axioms WeightedComplex.exactPart_le_cocycles
#print axioms WeightedComplex.exact_orthogonal_coexact
#print axioms WeightedComplex.harmonic_orthogonal_exact
#print axioms WeightedComplex.harmonic_orthogonal_coexact
#print axioms WeightedComplex.harmonic_eq_orthogonal
#print axioms WeightedComplex.hodge_decomposition
#print axioms WeightedComplex.hodge_decomposition_unique
#print axioms WeightedComplex.harmonic_meets_every_class
#print axioms WeightedComplex.harmonic_representative_unique
#print axioms WeightedComplex.cocycles_eq_sup
#print axioms WeightedComplex.finrank_harmonic_add_finrank_exact
#print axioms WeightedComplex.isCompl_in_cocycles
#print axioms WeightedComplex.harmonicEquivCohomology
#print axioms WeightedComplex.harmonic_moves_within_class
#print axioms WeightedComplex.finrank_harmonic_metric_free
#print axioms unitMetric_codiff₀

end Audit

end Soma.Holonics.Foundation.HodgeReceiver

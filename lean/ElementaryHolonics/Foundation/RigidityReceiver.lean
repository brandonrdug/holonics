import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The rigidity receiver: a constraint system, its Jacobian, and the two null spaces

[definition] This owner states the law the Rust module
`crates/holonic-engine/src/rigidity_receiver.rs` implements. The physical ontology of
`research/records/2026-08-21_THE_FOLD_IS_A_CONSTRAINT_ECOLOGY…` §5 represents a structure at one
grain as `P_eta = (V, C_eta, q, F_eta, J_eta, G, E_eta, R_eta, Gamma_eta)` with `F_eta(q) = 0` the
constraint system and `J_eta = D F_eta(q)` its rigidity Jacobian. Five things are stated here, in
this order.

1. **The constraint system.** A finite occurrence population in `d` rational coordinates, a finite
   constraint population, and for each constraint the pair of occurrences it joins. The constraint
   map is `F_c(q) = |q_i − q_j|² − ℓ_c²` with `ℓ_c` the length the *presented* configuration
   already realizes, so `F(place) = 0` holds by construction (`constraintMap_place`).
2. **The Jacobian as the differential.** `rigidityMatrix` carries `2(q_i − q_j)` in block `i` and
   its negative in block `j`. That this *is* `D F(q)` needs no analysis and no completeness of the
   field: the exact algebraic expansion `constraint_expansion` exhibits
   `F_c(q + t v) = F_c(q) + t·(J v)_c + t²·|δv|²`, so the coefficient of `t` is the Jacobian row
   applied to `v` and nothing else (`jacobian_is_the_differential`).
3. **The two null spaces.** `infinitesimalMotions = ker J` and `selfStresses = ker Jᵀ`. A
   self-stress annihilates every constraint reading the structure can produce
   (`self_stress_pairing`): it is a constraint reaction, not a motion.
4. **The counts.** `rank J + dim ker J = d·n` (`rank_nullity`), `rank J + dim ker Jᵀ = m`
   (`self_stress_dimension`), and their difference, the exact Maxwell relation
   `dim ker J − dim ker Jᵀ = d·n − m` (`maxwell_relation`). The Maxwell *count* `d·n − m` is
   therefore the motion dimension only when the self-stress space vanishes.
5. **The rigid motions lie in the kernel.** For any translation `t` and any antisymmetric `Ω`, the
   motion `v_i = t + Ω q_i` satisfies `J v = 0` (`rigid_motion_mem_ker`), because
   `δv = Ω δq` and `⟨x, Ω x⟩ = 0` for antisymmetric `Ω`. Their span is a submodule of the kernel
   (`rigidMotionSpace_le_motions`), which is what makes "internal motion dimension" a
   subtraction of one dimension from a larger one and never a subtraction of an assumed constant.

[proved-derived; formal-checked] Nothing above assumes the trivial motion count is `d(d+1)/2`.
Two degenerate cases are stated exactly: a coincident configuration turns every rotation
generator into a translation (`rotation_is_a_translation_of_coincident`), and a constraint whose
two occurrences coincide has an identically zero Jacobian row
(`rigidityMatrix_row_eq_zero_of_coincident`). The Rust owner measures the trivial dimension as an
exact rank for exactly this reason.

[proved-derived; formal-checked] `motions_antitone` is the open family's law: founding more
constraints on the same occurrences can only shrink `ker J`, so the refusing and admitting members
of `physical_constraint_grading`'s family bracket the motion dimension of every member.

Rust owner: `crates/holonic-engine/src/rigidity_receiver.rs`
(`RigidityJacobian`, `rigidity_reading`, `TrivialMotionReading`, `MaxwellCount`,
`rigid_clusters`, `removal_sensitivity`, `rigidity_family`).
-/

noncomputable section

namespace Soma.Holonics.Foundation.RigidityReceiver

open Matrix Finset

universe u

variable {d n m : ℕ}

/-! ## The configuration space -/

/-- [definition] The flattened configuration space: one rational per occurrence and axis. This is
the column index of the Rust owner's `ExactRatMatrix`, whose width is `d·n`. -/
abbrev Flat (n d : ℕ) := Fin n × Fin d → ℚ

/-- [definition] A covector supported on one occurrence block. The Jacobian row of a distance
constraint is a difference of two of these. -/
def bump (i : Fin n) (w : Fin d → ℚ) : Flat n d := fun p => if p.1 = i then w p.2 else 0

/-- [proved-derived; formal-checked] Pairing a block-supported covector with a configuration reads
only that block. -/
theorem sum_bump (i : Fin n) (w : Fin d → ℚ) (v : Flat n d) :
    ∑ p : Fin n × Fin d, bump i w p * v p = ∑ a, w a * v (i, a) := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · simp [bump]
  · intro b _ hb
    simp [bump, hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The constraint system -/

/-- [definition] `P_eta`'s discrete part: which occurrences each constraint joins, and the
configuration the differential is taken at. -/
structure ConstraintSystem (d n m : ℕ) where
  left : Fin m → Fin n
  right : Fin m → Fin n
  place : Flat n d

namespace ConstraintSystem

variable (S : ConstraintSystem d n m)

/-- [definition] The relative reading of a configuration or a velocity across one constraint. -/
def delta (c : Fin m) (v : Flat n d) (a : Fin d) : ℚ := v (S.left c, a) - v (S.right c, a)

@[simp]
theorem delta_add_smul (c : Fin m) (q v : Flat n d) (t : ℚ) (a : Fin d) :
    S.delta c (q + t • v) a = S.delta c q a + t * S.delta c v a := by
  simp [delta]
  ring

/-- [definition] `F_c(q) = |q_i − q_j|² − ℓ_c²`, with `ℓ_c` the length the presented configuration
realizes. The Rust owner reads `ℓ_c²` from the configuration for the same reason: the receiver's
question is the differential at a presented structure, not agreement with an exterior target. -/
def constraintMap (c : Fin m) (q : Flat n d) : ℚ :=
  (∑ a, S.delta c q a ^ 2) - ∑ a, S.delta c S.place a ^ 2

/-- [proved-derived; formal-checked] `F(place) = 0`: the presentation solves its own system. -/
@[simp]
theorem constraintMap_place (c : Fin m) : S.constraintMap c S.place = 0 := by
  simp [constraintMap]

/-! ## The Jacobian -/

/-- [definition] `J_eta = D F_eta(q)`: `2(q_i − q_j)` in block `i` and its negative in block `j`.

When `left c = right c` the two bumps coincide and the row is identically zero, which is the
correct differential of a constant. -/
def rigidityMatrix : Matrix (Fin m) (Fin n × Fin d) ℚ := fun c p =>
  bump (S.left c) (fun a => 2 * S.delta c S.place a) p
    - bump (S.right c) (fun a => 2 * S.delta c S.place a) p

/-- [proved-derived; formal-checked] **The row law.** `(J v)_c = 2 ⟨q_i − q_j, v_i − v_j⟩`. -/
theorem rigidityMatrix_mulVec (v : Flat n d) :
    S.rigidityMatrix *ᵥ v = fun c => 2 * ∑ a, S.delta c S.place a * S.delta c v a := by
  funext c
  show ∑ p : Fin n × Fin d, S.rigidityMatrix c p * v p = _
  have split : ∀ p : Fin n × Fin d, S.rigidityMatrix c p * v p
      = bump (S.left c) (fun a => 2 * S.delta c S.place a) p * v p
        - bump (S.right c) (fun a => 2 * S.delta c S.place a) p * v p := by
    intro p
    simp [rigidityMatrix, sub_mul]
  rw [Finset.sum_congr rfl fun p _ => split p, Finset.sum_sub_distrib,
    sum_bump, sum_bump, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [delta]
  ring

/-- [definition] The Jacobian as a linear map on the configuration space. -/
def rigidityLin : Flat n d →ₗ[ℚ] (Fin m → ℚ) := Matrix.mulVecLin S.rigidityMatrix

/-- [definition] `ker J_eta`: the infinitesimal motions. -/
def infinitesimalMotions : Submodule ℚ (Flat n d) := LinearMap.ker S.rigidityLin

/-- [definition] `ker J_eta^T`: the self-stresses, equivalently the constraint reactions. -/
def selfStresses : Submodule ℚ (Fin m → ℚ) :=
  LinearMap.ker (Matrix.mulVecLin S.rigidityMatrixᵀ)

/-- [proved-derived; formal-checked] Membership in the motion space is exactly the first-order
constancy of every constrained separation. -/
theorem mem_infinitesimalMotions_iff (v : Flat n d) :
    v ∈ S.infinitesimalMotions ↔ ∀ c, ∑ a, S.delta c S.place a * S.delta c v a = 0 := by
  constructor
  · intro hv c
    have h : S.rigidityMatrix *ᵥ v = 0 := hv
    rw [S.rigidityMatrix_mulVec v] at h
    have := congrFun h c
    simpa using this
  · intro h
    show S.rigidityMatrix *ᵥ v = 0
    rw [S.rigidityMatrix_mulVec v]
    funext c
    simp [h c]

/-- [proved-derived; formal-checked] **A self-stress is a constraint reaction.** It annihilates
every constraint reading the structure can produce, for every velocity at once. -/
theorem self_stress_pairing {w : Fin m → ℚ} (hw : w ∈ S.selfStresses) (v : Flat n d) :
    w ⬝ᵥ (S.rigidityMatrix *ᵥ v) = 0 := by
  have h : S.rigidityMatrixᵀ *ᵥ w = 0 := hw
  rw [Matrix.mulVec_transpose] at h
  rw [Matrix.dotProduct_mulVec, h]
  simp

/-! ## The Jacobian is the differential -/

/-- [proved-derived; formal-checked] **The exact expansion.** No limit, no completeness, no
analysis: the linear coefficient in `t` is the Jacobian row applied to `v`, and the remainder is
exactly one quadratic term. -/
theorem constraint_expansion (c : Fin m) (q v : Flat n d) (t : ℚ) :
    S.constraintMap c (q + t • v)
      = S.constraintMap c q + 2 * t * (∑ a, S.delta c q a * S.delta c v a)
        + t ^ 2 * ∑ a, S.delta c v a * S.delta c v a := by
  simp only [constraintMap, delta_add_smul]
  have expand : ∀ a : Fin d, (S.delta c q a + t * S.delta c v a) ^ 2
      = S.delta c q a ^ 2 + 2 * t * (S.delta c q a * S.delta c v a)
        + t ^ 2 * (S.delta c v a * S.delta c v a) := by
    intro a; ring
  rw [Finset.sum_congr rfl fun a _ => expand a, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- [proved-derived; formal-checked] **`J = D F(place)`.** At the presented configuration the
constraint map's increment along `v` is `t·(J v)_c` plus one exactly named quadratic remainder. -/
theorem jacobian_is_the_differential (c : Fin m) (v : Flat n d) (t : ℚ) :
    S.constraintMap c (S.place + t • v)
      = t * (S.rigidityMatrix *ᵥ v) c + t ^ 2 * ∑ a, S.delta c v a * S.delta c v a := by
  rw [S.constraint_expansion c S.place v t, S.rigidityMatrix_mulVec v, constraintMap_place]
  ring

/-! ## The rigid motions -/

/-- [definition] An antisymmetric generator of an infinitesimal rotation. -/
def IsSkew (Ω : Fin d → Fin d → ℚ) : Prop := ∀ a b, Ω b a = -Ω a b

/-- [definition] The infinitesimal rigid motion generated by a translation `t` and an
antisymmetric `Ω`, **linearized about this configuration**: `v_i = t + Ω q_i`. It depends on
`place`, which is why the Rust owner measures the trivial dimension rather than assuming one. -/
def rigidMotion (t : Fin d → ℚ) (Ω : Fin d → Fin d → ℚ) : Flat n d := fun p =>
  t p.2 + ∑ b, Ω p.2 b * S.place (p.1, b)

/-- [proved-derived; formal-checked] A rigid motion's relative velocity across a constraint is
`Ω` applied to the relative position. The translation cancels. -/
theorem delta_rigidMotion (t : Fin d → ℚ) (Ω : Fin d → Fin d → ℚ) (c : Fin m) (a : Fin d) :
    S.delta c (S.rigidMotion t Ω) a = ∑ b, Ω a b * S.delta c S.place b := by
  simp only [delta, rigidMotion, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] An antisymmetric double sum vanishes. -/
theorem skew_double_sum_eq_zero {f : Fin d → Fin d → ℚ} (hf : ∀ a b, f b a = -f a b) :
    ∑ a, ∑ b, f a b = 0 := by
  have hcomm : (∑ a, ∑ b, f a b) = ∑ a, ∑ b, f b a := Finset.sum_comm
  have hneg : (∑ a, ∑ b, f b a) = -∑ a, ∑ b, f a b := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun b _ => hf a b
  have := hcomm.trans hneg
  linarith

/-- [proved-derived; formal-checked] An antisymmetric form vanishes on the diagonal. -/
theorem skew_quadratic_form_eq_zero {Ω : Fin d → Fin d → ℚ} (hΩ : IsSkew Ω)
    (x : Fin d → ℚ) : ∑ a, x a * ∑ b, Ω a b * x b = 0 := by
  have hsplit : (∑ a, x a * ∑ b, Ω a b * x b) = ∑ a, ∑ b, x a * (Ω a b * x b) :=
    Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _
  rw [hsplit]
  refine skew_double_sum_eq_zero (fun a b => ?_)
  rw [hΩ a b]
  ring

/-- [proved-derived; formal-checked] **A rigid motion of the whole configuration lies in
`ker J`.** This is the theorem the Rust owner certifies generator by generator rather than
asserting, and it holds for every constraint population and every configuration. -/
theorem rigid_motion_mem_ker (t : Fin d → ℚ) {Ω : Fin d → Fin d → ℚ} (hΩ : IsSkew Ω) :
    S.rigidMotion t Ω ∈ S.infinitesimalMotions := by
  rw [mem_infinitesimalMotions_iff]
  intro c
  simp only [delta_rigidMotion]
  exact skew_quadratic_form_eq_zero hΩ (S.delta c S.place)

/-- [proved-derived; formal-checked] The `d` translation generators. -/
theorem translation_mem_ker (t : Fin d → ℚ) :
    S.rigidMotion t (fun _ _ => 0) ∈ S.infinitesimalMotions :=
  S.rigid_motion_mem_ker t (by intro a b; simp)

/-- [proved-derived; formal-checked] The `d(d−1)/2` rotation generators. -/
theorem rotation_mem_ker {Ω : Fin d → Fin d → ℚ} (hΩ : IsSkew Ω) :
    S.rigidMotion 0 Ω ∈ S.infinitesimalMotions :=
  S.rigid_motion_mem_ker 0 hΩ

/-- [definition] The span of the rigid motions: the trivial motion space at this configuration. -/
def rigidMotionSpace : Submodule ℚ (Flat n d) :=
  Submodule.span ℚ
    (Set.range fun x : (Fin d → ℚ) × {Ω : Fin d → Fin d → ℚ // IsSkew Ω} =>
      S.rigidMotion x.1 x.2.1)

/-- [proved-derived; formal-checked] The trivial space is a subspace of the motion space, so the
internal motion dimension is a difference of two measured dimensions and never a subtraction of an
assumed constant. -/
theorem rigidMotionSpace_le_motions : S.rigidMotionSpace ≤ S.infinitesimalMotions := by
  rw [rigidMotionSpace, Submodule.span_le, Set.range_subset_iff]
  rintro ⟨t, Ω, hΩ⟩
  exact S.rigid_motion_mem_ker t hΩ

/-- [definition] Infinitesimal rigidity **at this configuration**: every motion is a rigid motion.
This is not generic rigidity and not finite rigidity. -/
def InfinitesimallyRigid : Prop := S.infinitesimalMotions ≤ S.rigidMotionSpace

theorem infinitesimallyRigid_iff_eq :
    S.InfinitesimallyRigid ↔ S.infinitesimalMotions = S.rigidMotionSpace :=
  ⟨fun h => le_antisymm h S.rigidMotionSpace_le_motions, fun h => h.le⟩

/-! ## The degenerate configurations -/

/-- [proved-derived; formal-checked] **A coincident configuration loses its rotations.** Every
rotation generator becomes a translation, so the trivial space collapses to the `d` translations.
It is *not* the zero vector, which is why a vanishing test would be the wrong receiver and the
Rust owner measures an exact rank instead. -/
theorem rotation_is_a_translation_of_coincident {p : Fin d → ℚ}
    (h : ∀ x : Fin n × Fin d, S.place x = p x.2) (Ω : Fin d → Fin d → ℚ) :
    S.rigidMotion 0 Ω = S.rigidMotion (fun a => ∑ b, Ω a b * p b) (fun _ _ => 0) := by
  funext x
  simp [rigidMotion, h]

/-- [proved-derived; formal-checked] **A constraint between coincident occurrences is no
constraint.** Its Jacobian row is identically zero, so it restricts nothing to first order and is
dependent on every other row. -/
theorem rigidityMatrix_row_eq_zero_of_coincident (c : Fin m)
    (h : ∀ a, S.delta c S.place a = 0) (x : Fin n × Fin d) : S.rigidityMatrix c x = 0 := by
  simp [rigidityMatrix, bump, h]

/-! ## The counts -/

theorem finrank_flat : Module.finrank ℚ (Flat n d) = n * d := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

/-- [proved-derived; formal-checked] **Rank–nullity on the configuration space:**
`rank J + dim ker J = d·n`. -/
theorem rank_nullity :
    S.rigidityMatrix.rank + Module.finrank ℚ S.infinitesimalMotions = n * d := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin S.rigidityMatrix)
  rw [finrank_flat] at h
  exact h

/-- [proved-derived; formal-checked] **Rank–nullity on the constraint space:**
`dim ker Jᵀ = m − rank J`. -/
theorem self_stress_dimension :
    S.rigidityMatrix.rank + Module.finrank ℚ S.selfStresses = m := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin S.rigidityMatrixᵀ)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  have hrank : S.rigidityMatrixᵀ.rank = S.rigidityMatrix.rank := Matrix.rank_transpose _
  rw [show Module.finrank ℚ (LinearMap.range (Matrix.mulVecLin S.rigidityMatrixᵀ))
      = S.rigidityMatrixᵀ.rank from rfl, hrank] at h
  exact h

/-- [proved-derived; formal-checked] **The exact Maxwell relation.** The count `d·n − m` is the
motion dimension *minus the self-stress dimension*, so a count alone under-reports the motion
space by exactly the redundancy and decides no rigidity question by itself. -/
theorem maxwell_relation :
    (Module.finrank ℚ S.infinitesimalMotions : ℤ) - Module.finrank ℚ S.selfStresses
      = (n * d : ℤ) - m := by
  have h1 := S.rank_nullity
  have h2 := S.self_stress_dimension
  omega

/-- [proved-derived; formal-checked] The count is the motion dimension exactly when there is no
self-stress. -/
theorem motion_dimension_eq_count_of_no_self_stress (h : S.selfStresses = ⊥) :
    (Module.finrank ℚ S.infinitesimalMotions : ℤ) = (n * d : ℤ) - m := by
  have := S.maxwell_relation
  rw [h] at this
  simpa using this

/-! ## The open family -/

/-- [proved-derived; formal-checked] **Founding more constraints can only shrink the motion
space.** This is why the refusing and admitting members of the graded family bracket `dim ker J`
over the whole family, and why an `Open` contact is a rigidity question rather than bookkeeping.

Rust owner: `rigidity_receiver::rigidity_family`, whose refusal
`MotionDimensionNotAntitone` is this theorem's contrapositive. -/
theorem motions_antitone {m' : ℕ} (S' : ConstraintSystem d n m') (ι : Fin m → Fin m')
    (hleft : ∀ c, S'.left (ι c) = S.left c) (hright : ∀ c, S'.right (ι c) = S.right c)
    (hplace : S'.place = S.place) :
    S'.infinitesimalMotions ≤ S.infinitesimalMotions := by
  intro v hv
  rw [mem_infinitesimalMotions_iff] at hv ⊢
  intro c
  have h := hv (ι c)
  simpa [delta, hleft c, hright c, hplace] using h

end ConstraintSystem

section Audit

#print axioms sum_bump
#print axioms ConstraintSystem.constraintMap_place
#print axioms ConstraintSystem.rigidityMatrix_mulVec
#print axioms ConstraintSystem.mem_infinitesimalMotions_iff
#print axioms ConstraintSystem.self_stress_pairing
#print axioms ConstraintSystem.constraint_expansion
#print axioms ConstraintSystem.jacobian_is_the_differential
#print axioms ConstraintSystem.delta_rigidMotion
#print axioms ConstraintSystem.skew_double_sum_eq_zero
#print axioms ConstraintSystem.skew_quadratic_form_eq_zero
#print axioms ConstraintSystem.rigid_motion_mem_ker
#print axioms ConstraintSystem.translation_mem_ker
#print axioms ConstraintSystem.rotation_mem_ker
#print axioms ConstraintSystem.rigidMotionSpace_le_motions
#print axioms ConstraintSystem.infinitesimallyRigid_iff_eq
#print axioms ConstraintSystem.rotation_is_a_translation_of_coincident
#print axioms ConstraintSystem.rigidityMatrix_row_eq_zero_of_coincident
#print axioms ConstraintSystem.finrank_flat
#print axioms ConstraintSystem.rank_nullity
#print axioms ConstraintSystem.self_stress_dimension
#print axioms ConstraintSystem.maxwell_relation
#print axioms ConstraintSystem.motion_dimension_eq_count_of_no_self_stress
#print axioms ConstraintSystem.motions_antitone

end Audit

end Soma.Holonics.Foundation.RigidityReceiver

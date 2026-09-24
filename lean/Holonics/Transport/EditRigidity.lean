import Holonics.Foundation.RigidityReceiver
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Knot friction and edit torque: the kept receivers of an artifact as a rigidity framework

[definition] This file is the formal owner of item **T4** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Its executable
counterpart is `crates/holonic-engine/src/edit_rigidity.rs`. **It founds no second Jacobian.**
`Foundation/RigidityReceiver.lean` owns the constraint Jacobian, its two null spaces and the
rank–nullity identities; `Transport/ArtifactRelease.lean` owns the discrete edited family, its
release law and the three relations that "independent versus entangled" conflates. What is new
here is the *edit side* of that one Jacobian: which edits are invisible, which need compensating
work, which are obstructed, and what the unresolved receiver residual does to the available
generators.

## 1. The kept-receiver constraint map is a rigidity Jacobian

[definition] An artifact `A` sits in an exact linear(ized) chart with coordinates in `ℚ^n`
(token-slot coordinates, embedding-placement coordinates, or a constraint complex's configuration).
A declared kept receiver family `R_keep` has an exact Jacobian `J_keep = D(ρ)_{ρ ∈ R_keep}(A)`, one
row per kept face coordinate. When the kept faces are declared squared separations that map **is**
`RigidityReceiver.rigidityMatrix`: `the_kept_face_differential_is_the_rigidity_jacobian` is
`jacobian_is_the_differential` at the kept family, cited rather than restated, and
`kept_rank_nullity` / `kept_self_stress_dimension` are that owner's `rank_nullity` and
`self_stress_dimension`. When a kept face is an exact **linear** form of the chart coordinates its
differential is the form itself (`linear_face_is_its_own_differential`), so a chart mixing declared
separations with declared role-agreement forms is one matrix and not two receivers.

## 2. Free edits, compensable edits, obstruction

[definition] `Free J g` is `J *ᵥ g = 0`: the first-order edit directions **no kept receiver sees**.
That is `ker J_keep` (`free_iff_mem_ker`) — `dog ⟶ cat` when the surrounding grammar keeps only
"singular animal noun". A proposed edit `g` is *compensable* over a declared allowed compensation
subspace `im A` exactly when the linear system `(J A) c = −(J g)` is consistent
(`compensating_iff_solves`); the compensating family is an affine set
(`compensating_family_is_affine`) and is empty exactly when a left-null covector certifies the
inconsistency (`obstructed_iff_certificate`, which is the Fredholm alternative
`mem_range_iff_annihilators_vanish` proved here over `ℚ`). That certificate is the `is ⟶ why` case:
an obstruction is a **return**, exhibited, not a failure to find one.

[proved-derived; formal-checked] **Entanglement is self-stress support.** For a kept face `c` the
three statements *some self-stress is supported at `c`*, *row `c` is a combination of the other
rows*, and *dropping `c` loses no first-order restriction* are equivalent
(`entanglement_is_self_stress_support`). R4's Rust owner reads its removal sensitivity off exactly
this equivalence and its Lean owner does not carry it; it is proved here, from the Fredholm
alternative, and R4's `selfStresses` and `rigidityMatrix` are the objects it is proved about.

[established-bounded; formal-checked] **Which of T3's three relations this captures.**
`Transport/ArtifactRelease.lean` proves "independent versus entangled" is three relations —
commuting on the family, chartwise locality, and constraint entanglement — and that Brandon's
`dog ⟶ cat` / `is ⟶ why` pair is separated only by the third. The linear notion here **is** the
third, at first order. It is not the first: `first_order_edits_always_commute` says every pair of
first-order edits commutes in a linear chart, so commuting separates nothing here at all. It is not
the second either: a first-order direction has no read/write distinction, which is a property of
the discrete edit action and not of its differential.

## 3. Rethreading work is the minimizer of a declared metric

[definition] `W_knot(g | A)² = inf { ‖δ‖²_M : δ compensating }` for a **declared** exact
positive-definite `M`. The unit metric is one declaration and not a default. The minimizer over an
affine subspace is characterized exactly by the normal equation `M δ* ⟂ allowed`
(`normal_equation_gives_the_unique_minimizer`), so `W²` is an exact rational and never a root; and
`work_zero_iff_free` proves `W² = 0` exactly when the edit is free, so the two arms of the verdict
are discriminated by the metric and not by a threshold. `positive_definite_of_ldl` is the exact
certificate the Rust owner checks before accepting a declared Gram matrix as a metric.

## 4. Edit torque

[definition] `τ = J_g^† r` pulls the unresolved receiver residual back to the generators.
`torque_zero_iff_residual_annihilates_image` and `stationary_iff_torque_zero` are the same
statement read twice: the torque vanishes exactly when no first-order edit changes the squared
residual to first order. `the_exact_descent_step` gives the exact rational step and the exact
decrease when it does not vanish — `torque_nonzero_has_nonzero_image` is why that step exists.

[established-bounded; formal-checked] **First-order stationarity is necessary and not sufficient.**
`stationarity_is_not_cancellation` constructs a kept face whose Jacobian row vanishes — R4's
`rigidityMatrix_row_eq_zero_of_coincident` — at which every torque is zero and a second-order edit
still moves the face by exactly `t²`, which is R4's own `jacobian_is_the_differential` remainder.
So `τ = 0` is not `ArtifactRelease.the_rotation_tube_carries_no_holonomy`'s identity holonomy, and
"the intentions cancel" at first order is strictly weaker than cancellation.

[definition] **The adjoint uses the morphology that produced the forward carriers.** A bare
transpose is the adjoint only under declared identity metrics;
`metric_adjoint_pairs_the_residual_with_the_generators` is the characterization a claimed adjoint
must satisfy.

## 5. The knot

[definition] A knot is what holds a structure at equilibrium for the window in which it exists: the
rigid, self-stressed subframework of kept faces. Read at a declared region ladder, `ImpliedBy`
records that a pair's separation is held by the faces **induced inside** a region. The nesting
direction that is true is the **ascending** one: `impliedBy_mono` — what a subregion's induced
faces hold, the region's induced faces hold too. The descending direction is false, and
`induced_implication_does_not_descend` is the counterexample: three occurrences on a line with
consecutive separations kept, where the outer pair is held at the whole region and by nothing at
all inside the subregion carrying only its two endpoints. Read at the **ambient** motions instead,
knot-ness is downward closed (`ambient_knot_is_downward_closed`) — the two readings nest in
opposite directions and are not interchangeable.

[interpretation] That `W²`, `τ` and the per-scale self-stress dimension together are a *knot
friction moment* in the sense of an electromagnetic moment is Brandon's picture and is graded as
interpretation. What is defined here is exact and finite: a squared rethreading work in a declared
metric, an adjoint pullback of a declared residual, and a self-stress dimension per declared scale.

Rust owner: `crates/holonic-engine/src/edit_rigidity.rs`.
-/

noncomputable section

namespace Holonics.Transport.EditRigidity

open Matrix Finset
open Holonics.Foundation.RigidityReceiver

universe u v

variable {d n m : ℕ}
variable {μ ι κ ρ : Type*}

/-! ## 0. The Fredholm alternative over `ℚ`

[proved-derived; formal-checked] Everything below that decides *obstruction* rests on one fact:
a target is reached by an exact rational map exactly when every covector annihilating the map's
image annihilates the target. The forward half is one line; the converse is the duality
`Subspace.dualAnnihilator_dualCoannihilator_eq`, with every functional on a finite coordinate space
written as a dot product. -/

/-- [proved-derived; formal-checked] Every functional on a finite coordinate space is the dot
product with the vector of its values on the unit coordinates. -/
theorem dual_is_dotProduct [Fintype μ] [DecidableEq μ] (φ : Module.Dual ℚ (μ → ℚ)) (u : μ → ℚ) :
    φ u = u ⬝ᵥ (fun i => φ (Pi.single i 1)) := by
  classical
  have hu : u = ∑ i, u i • (Pi.single i (1 : ℚ)) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  rw [hu]
  simp [map_sum, dotProduct, Finset.sum_apply, Pi.single_apply]

/-- [proved-derived; formal-checked] **The Fredholm alternative, exactly.** `M x = y` has a
solution exactly when every left-null covector of `M` annihilates `y`. The obstruction is therefore
a *returnable object* and not the absence of a search result. -/
theorem mem_range_iff_annihilators_vanish [Fintype μ] [DecidableEq μ] [Fintype ι]
    (M : Matrix μ ι ℚ) (y : μ → ℚ) :
    (∃ x : ι → ℚ, M *ᵥ x = y) ↔ ∀ w : μ → ℚ, Mᵀ *ᵥ w = 0 → w ⬝ᵥ y = 0 := by
  classical
  constructor
  · rintro ⟨x, rfl⟩ w hw
    rw [dotProduct_mulVec, ← mulVec_transpose, hw, zero_dotProduct]
  · intro h
    set W : Submodule ℚ (μ → ℚ) := LinearMap.range (Matrix.mulVecLin M) with hW
    have hy : y ∈ W.dualAnnihilator.dualCoannihilator := by
      rw [Submodule.mem_dualCoannihilator]
      intro φ hφ
      set w : μ → ℚ := fun i => φ (Pi.single i 1) with hwdef
      have hann : Mᵀ *ᵥ w = 0 := by
        funext j
        have hall : ∀ x : ι → ℚ, (M *ᵥ x) ⬝ᵥ w = 0 := by
          intro x
          have hmem := (Submodule.mem_dualAnnihilator φ).mp hφ (M *ᵥ x) ⟨x, rfl⟩
          rw [dual_is_dotProduct φ (M *ᵥ x)] at hmem
          exact hmem
        have hx := hall (Pi.single j 1)
        rw [dotProduct_comm, dotProduct_mulVec, dotProduct_single, mul_one] at hx
        rw [mulVec_transpose]
        simpa using hx
      have hzero := h w hann
      rw [dual_is_dotProduct φ y]
      simpa [dotProduct_comm] using hzero
    rw [Subspace.dualAnnihilator_dualCoannihilator_eq] at hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, hx⟩

/-- [proved-derived; formal-checked] The transpose is the adjoint of the coordinate pairing. Every
torque statement below is this one identity read at a declared residual. -/
theorem mulVec_dotProduct_transpose [Fintype ι] [Fintype ρ] (A : Matrix ρ ι ℚ) (y : ι → ℚ)
    (z : ρ → ℚ) : (A *ᵥ y) ⬝ᵥ z = y ⬝ᵥ (Aᵀ *ᵥ z) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  exact dotProduct_comm _ _

/-! ## 1. The kept-receiver constraint map is R4's rigidity Jacobian -/

/-- [definition] The kept-receiver Jacobian of a declared family of squared separations **is**
R4's rigidity matrix. No second Jacobian is founded; this is a name for that one. -/
def keptJacobian (S : ConstraintSystem d n m) : Matrix (Fin m) (Fin n × Fin d) ℚ :=
  S.rigidityMatrix

/-- [proved-derived; formal-checked] **The identification.** The kept-face map's differential at
the presented artifact is the constraint Jacobian of the framework whose constraints are the kept
faces. This is `RigidityReceiver.jacobian_is_the_differential`, cited at `keptJacobian`. -/
theorem the_kept_face_differential_is_the_rigidity_jacobian (S : ConstraintSystem d n m)
    (c : Fin m) (v : Flat n d) (t : ℚ) :
    S.constraintMap c (S.place + t • v)
      = t * (keptJacobian S *ᵥ v) c + t ^ 2 * ∑ a, S.delta c v a * S.delta c v a :=
  S.jacobian_is_the_differential c v t

/-- [proved-derived; formal-checked] The kept reading's rank–nullity identity is R4's, cited. -/
theorem kept_rank_nullity (S : ConstraintSystem d n m) :
    (keptJacobian S).rank + Module.finrank ℚ S.infinitesimalMotions = n * d :=
  S.rank_nullity

/-- [proved-derived; formal-checked] The kept reading's self-stress count is R4's, cited. -/
theorem kept_self_stress_dimension (S : ConstraintSystem d n m) :
    (keptJacobian S).rank + Module.finrank ℚ S.selfStresses = m :=
  S.self_stress_dimension

/-- [proved-derived; formal-checked] A kept face that is an exact **linear** form of the chart
coordinates is its own differential: the increment carries no remainder at all. A chart mixing
declared separations with declared role-agreement forms is therefore one matrix. -/
theorem linear_face_is_its_own_differential [Fintype ι] (row x v : ι → ℚ) (t : ℚ) :
    row ⬝ᵥ (x + t • v) = row ⬝ᵥ x + t * (row ⬝ᵥ v) := by
  simp [dotProduct_add, dotProduct_smul, smul_eq_mul]

/-! ## 2. Free edits, compensable edits, obstruction -/

/-- [definition] A **free edit**: a first-order change invisible to every kept receiver. -/
def Free [Fintype ι] (J : Matrix μ ι ℚ) (g : ι → ℚ) : Prop := J *ᵥ g = 0

/-- [proved-derived; formal-checked] The free edits are exactly `ker J_keep`. -/
theorem free_iff_mem_ker [Fintype ι] (J : Matrix μ ι ℚ) (g : ι → ℚ) :
    Free J g ↔ g ∈ LinearMap.ker (Matrix.mulVecLin J) := Iff.rfl

/-- [definition] A **compensation** is a coefficient vector of the declared allowed subspace
`im A` whose displacement restores every kept face to first order. -/
def Compensating [Fintype ι] [Fintype κ] (J : Matrix μ ι ℚ) (A : Matrix ι κ ℚ)
    (g : ι → ℚ) (c : κ → ℚ) : Prop := J *ᵥ (g + A *ᵥ c) = 0

/-- [proved-derived; formal-checked] Compensation is exactly solving one exact linear system. -/
theorem compensating_iff_solves [Fintype ι] [Fintype κ] (J : Matrix μ ι ℚ) (A : Matrix ι κ ℚ)
    (g : ι → ℚ) (c : κ → ℚ) :
    Compensating J A g c ↔ (J * A) *ᵥ c = -(J *ᵥ g) := by
  unfold Compensating
  rw [mulVec_add, ← mulVec_mulVec]
  constructor
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
    linarith
  · intro h
    funext i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
    linarith

/-- [proved-derived; formal-checked] **The compensating family is an affine subspace.** Every
affine combination of two compensations compensates. -/
theorem compensating_family_is_affine [Fintype ι] [Fintype κ] (J : Matrix μ ι ℚ)
    (A : Matrix ι κ ℚ) (g : ι → ℚ) {c₁ c₂ : κ → ℚ} (s : ℚ)
    (h₁ : Compensating J A g c₁) (h₂ : Compensating J A g c₂) :
    Compensating J A g ((1 - s) • c₁ + s • c₂) := by
  rw [compensating_iff_solves] at h₁ h₂ ⊢
  rw [mulVec_add, mulVec_smul, mulVec_smul, h₁, h₂, ← add_smul]
  simp

/-- [proved-derived; formal-checked] An edit is free exactly when the zero compensation suffices. -/
theorem free_iff_zero_compensates [Fintype ι] [Fintype κ] (J : Matrix μ ι ℚ) (A : Matrix ι κ ℚ)
    (g : ι → ℚ) : Free J g ↔ Compensating J A g 0 := by
  unfold Free Compensating
  rw [mulVec_zero, add_zero]

/-- [proved-derived; formal-checked] **The obstruction certificate is complete.** No compensation
exists exactly when some covector annihilates every compensable defect and reads the edit's defect
as nonzero. This is what `exact_linear::cokernel_annihilator` returns on an inconsistent system. -/
theorem obstructed_iff_certificate [Fintype μ] [DecidableEq μ] [Fintype ι] [Fintype κ]
    (J : Matrix μ ι ℚ) (A : Matrix ι κ ℚ) (g : ι → ℚ) :
    (¬ ∃ c : κ → ℚ, Compensating J A g c)
      ↔ ∃ w : μ → ℚ, (J * A)ᵀ *ᵥ w = 0 ∧ w ⬝ᵥ (J *ᵥ g) ≠ 0 := by
  classical
  have hrange := mem_range_iff_annihilators_vanish (J * A) (-(J *ᵥ g))
  constructor
  · intro h
    have hno : ¬ ∃ c : κ → ℚ, (J * A) *ᵥ c = -(J *ᵥ g) := by
      rintro ⟨c, hc⟩
      exact h ⟨c, (compensating_iff_solves J A g c).mpr hc⟩
    rw [hrange] at hno
    simp only [not_forall] at hno
    obtain ⟨w, hw, hne⟩ := hno
    refine ⟨w, hw, ?_⟩
    intro hzero
    exact hne (by rw [dotProduct_neg, hzero, neg_zero])
  · rintro ⟨w, hw, hne⟩ ⟨c, hc⟩
    rw [compensating_iff_solves] at hc
    have hvanish := (mem_range_iff_annihilators_vanish (J * A) (-(J *ᵥ g))).mp ⟨c, hc⟩ w hw
    rw [dotProduct_neg, neg_eq_zero] at hvanish
    exact hne hvanish

/-! ### Entanglement is self-stress support -/

/-- [definition] The self-stress space of a kept Jacobian: `ker J_keepᵀ`. For a rigidity Jacobian
this is R4's `selfStresses`, by definition and not by analogy. -/
def selfStressSpace [Fintype μ] (J : Matrix μ ι ℚ) : Submodule ℚ (μ → ℚ) :=
  LinearMap.ker (Matrix.mulVecLin Jᵀ)

/-- [proved-derived; formal-checked] For a rigidity Jacobian, `selfStressSpace` is R4's own
`selfStresses`. -/
theorem selfStressSpace_rigidity (S : ConstraintSystem d n m) :
    selfStressSpace (keptJacobian S) = S.selfStresses := rfl

/-- [definition] A kept face is **entangled** when some self-stress is supported at it: it is held
redundantly, and an edit touching it propagates to the faces that share the stress. -/
def Entangled [Fintype μ] (J : Matrix μ ι ℚ) (c : μ) : Prop :=
  ∃ w ∈ selfStressSpace J, w c ≠ 0

/-- [definition] A kept face is **dependent** when its row is a combination of the others. -/
def Dependent [Fintype μ] (J : Matrix μ ι ℚ) (c : μ) : Prop :=
  ∃ lam : μ → ℚ, lam c = 0 ∧ J c = ∑ j, lam j • J j

/-- [definition] Dropping a kept face **loses nothing**: every direction the other faces admit,
this one admits too. -/
def DroppingLosesNothing [Fintype ι] (J : Matrix μ ι ℚ) (c : μ) : Prop :=
  ∀ v : ι → ℚ, (∀ j, j ≠ c → (J *ᵥ v) j = 0) → (J *ᵥ v) c = 0

/-- The kept Jacobian with one row zeroed: the system with that face dropped. -/
def dropRow [DecidableEq μ] (J : Matrix μ ι ℚ) (c : μ) : Matrix μ ι ℚ :=
  fun j => if j = c then 0 else J j

theorem dropRow_apply_ne [DecidableEq μ] {J : Matrix μ ι ℚ} {c j : μ} (h : j ≠ c) :
    dropRow J c j = J j := by simp [dropRow, h]

theorem transpose_mulVec_eq_sum [Fintype μ] (J : Matrix μ ι ℚ) (lam : μ → ℚ) :
    Jᵀ *ᵥ lam = ∑ j, lam j • J j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem sum_indicator_smul_row [Fintype μ] [DecidableEq μ] (J : Matrix μ ι ℚ) (c : μ) :
    ∑ j, (if j = c then (1 : ℚ) else 0) • J j = J c := by
  classical
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb; simp [hb]
  · intro hc; exact absurd (Finset.mem_univ c) hc

/-- [proved-derived; formal-checked] **Entanglement is dependence.** A self-stress supported at a
face is exactly a presentation of that face's row by the others. -/
theorem entangled_iff_dependent [Fintype μ] [DecidableEq μ] (J : Matrix μ ι ℚ) (c : μ) :
    Entangled J c ↔ Dependent J c := by
  classical
  constructor
  · rintro ⟨w, hw, hwc⟩
    have hsum : ∑ j, w j • J j = 0 := by
      have hker : Jᵀ *ᵥ w = 0 := hw
      rw [transpose_mulVec_eq_sum] at hker
      exact hker
    refine ⟨fun j => if j = c then 0 else -(w c)⁻¹ * w j, by simp, ?_⟩
    have hcombine : ∀ j : μ,
        ((if j = c then (0 : ℚ) else -(w c)⁻¹ * w j) + (w c)⁻¹ * w j)
          = (if j = c then (1 : ℚ) else 0) := by
      intro j
      by_cases hj : j = c
      · subst hj
        rw [if_pos rfl, if_pos rfl, zero_add, inv_mul_cancel₀ hwc]
      · simp [hj]
    have hkey : (∑ j, (if j = c then (0 : ℚ) else -(w c)⁻¹ * w j) • J j)
        + (w c)⁻¹ • (∑ j, w j • J j) = J c := by
      rw [Finset.smul_sum, ← Finset.sum_add_distrib]
      have hstep : ∀ j : μ,
          (if j = c then (0 : ℚ) else -(w c)⁻¹ * w j) • J j + (w c)⁻¹ • (w j • J j)
            = (if j = c then (1 : ℚ) else 0) • J j := by
        intro j
        rw [smul_smul, ← add_smul, hcombine j]
      rw [Finset.sum_congr rfl fun j _ => hstep j, sum_indicator_smul_row]
    rw [hsum, smul_zero, add_zero] at hkey
    exact hkey.symm
  · rintro ⟨lam, hlamc, hrow⟩
    refine ⟨fun j => if j = c then 1 else -lam j, ?_, by simp⟩
    show Jᵀ *ᵥ (fun j => if j = c then (1 : ℚ) else -lam j) = 0
    rw [transpose_mulVec_eq_sum]
    have hstep : ∀ j : μ, (if j = c then (1 : ℚ) else -lam j) • J j
        = (if j = c then (1 : ℚ) else 0) • J j - lam j • J j := by
      intro j
      by_cases hj : j = c
      · subst hj; simp [hlamc]
      · simp [hj, neg_smul]
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_sub_distrib,
      sum_indicator_smul_row, ← hrow, sub_self]

/-- [proved-derived; formal-checked] **Dependence is exactly losing nothing by dropping the face.**
This is the edit-side reading of R4's removal sensitivity, and it is the equivalence R4's Rust
owner reads its `RemovalSensitivity` off. The Fredholm alternative supplies both directions. -/
theorem dependent_iff_droppingLosesNothing [Fintype μ] [DecidableEq μ] [Fintype ι]
    (J : Matrix μ ι ℚ) (c : μ) :
    Dependent J c ↔ DroppingLosesNothing J c := by
  classical
  have hrange : (∃ lam : μ → ℚ, (dropRow J c)ᵀ *ᵥ lam = J c)
      ↔ ∀ v : ι → ℚ, ((dropRow J c)ᵀ)ᵀ *ᵥ v = 0 → v ⬝ᵥ (J c) = 0 :=
    mem_range_iff_annihilators_vanish _ _
  rw [transpose_transpose] at hrange
  have hdrop : ∀ v : ι → ℚ,
      (dropRow J c *ᵥ v = 0) ↔ (∀ j, j ≠ c → (J *ᵥ v) j = 0) := by
    intro v
    constructor
    · intro h j hj
      have hj' := congrFun h j
      simpa [Matrix.mulVec, dropRow_apply_ne hj] using hj'
    · intro h
      funext j
      by_cases hj : j = c
      · subst hj; simp [Matrix.mulVec, dropRow]
      · simpa [Matrix.mulVec, dropRow_apply_ne hj] using h j hj
  have hdot : ∀ v : ι → ℚ, v ⬝ᵥ (J c) = (J *ᵥ v) c := by
    intro v; rw [dotProduct_comm]; rfl
  constructor
  · rintro ⟨lam, hlamc, hrow⟩ v hv
    rw [← hdot]
    have hsol : (dropRow J c)ᵀ *ᵥ lam = J c := by
      rw [transpose_mulVec_eq_sum, hrow]
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hj : j = c
      · subst hj; simp [hlamc]
      · rw [dropRow_apply_ne hj]
    exact hrange.mp ⟨lam, hsol⟩ v ((hdrop v).mpr hv)
  · intro h
    have hann : ∀ v : ι → ℚ, dropRow J c *ᵥ v = 0 → v ⬝ᵥ (J c) = 0 := by
      intro v hv
      rw [hdot]
      exact h v ((hdrop v).mp hv)
    obtain ⟨lam, hlam⟩ := hrange.mpr hann
    refine ⟨fun j => if j = c then 0 else lam j, by simp, ?_⟩
    rw [← hlam, transpose_mulVec_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hj : j = c
    · subst hj; simp [dropRow]
    · simp [hj, dropRow_apply_ne hj]

/-- [proved-derived; formal-checked] **Entanglement is self-stress support**, in all three of its
readings at once. A kept face in the support of a self-stress is redundantly held; the edits its
removal would free are exactly the edits the other faces already forbid. -/
theorem entanglement_is_self_stress_support [Fintype μ] [DecidableEq μ] [Fintype ι]
    (J : Matrix μ ι ℚ) (c : μ) :
    (Entangled J c ↔ Dependent J c) ∧ (Dependent J c ↔ DroppingLosesNothing J c) :=
  ⟨entangled_iff_dependent J c, dependent_iff_droppingLosesNothing J c⟩

/-- [proved-derived; formal-checked] **A face carrying no self-stress forbids an edit of its own.**
When no self-stress is supported at `c`, some edit direction is free at every other kept face and
not at `c`. That direction is what the face carries, and it is exhibited. -/
theorem a_face_carrying_no_self_stress_forbids_an_edit_of_its_own [Fintype μ] [DecidableEq μ]
    [Fintype ι] (J : Matrix μ ι ℚ) (c : μ) (h : ¬ Entangled J c) :
    ∃ v : ι → ℚ, (∀ j, j ≠ c → (J *ᵥ v) j = 0) ∧ (J *ᵥ v) c ≠ 0 := by
  classical
  rw [entangled_iff_dependent, dependent_iff_droppingLosesNothing] at h
  unfold DroppingLosesNothing at h
  simp only [not_forall] at h
  obtain ⟨v, hv, hne⟩ := h
  exact ⟨v, hv, hne⟩

/-! ### Which of T3's three relations this captures -/

/-- [proved-derived; formal-checked] In a linear chart **every** pair of first-order edits
commutes, so commuting separates nothing at all here. This is
`ArtifactRelease.commuting_does_not_separate_the_independent_from_the_entangled` again, at first
order, in its sharpest form. -/
theorem first_order_edits_always_commute (g₁ g₂ : ι → ℚ) : g₁ + g₂ = g₂ + g₁ := add_comm g₁ g₂

/-! ## 3. Rethreading work: the minimizer of a declared positive-definite metric -/

/-- [definition] The squared length of a displacement in a declared metric. -/
def sqNorm [Fintype ι] (M : Matrix ι ι ℚ) (x : ι → ℚ) : ℚ := x ⬝ᵥ (M *ᵥ x)

/-- [definition] An exact positive-definite metric: symmetric on the coordinate pairing, and
strictly positive off zero. **The unit metric is one declaration and not a default.** -/
structure PosDef [Fintype ι] (M : Matrix ι ι ℚ) : Prop where
  symm : ∀ x y : ι → ℚ, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x)
  pos : ∀ x : ι → ℚ, x ≠ 0 → 0 < sqNorm M x

theorem sqNorm_zero [Fintype ι] (M : Matrix ι ι ℚ) : sqNorm M 0 = 0 := by
  simp [sqNorm]

theorem sqNorm_nonneg [Fintype ι] {M : Matrix ι ι ℚ} (hM : PosDef M) (x : ι → ℚ) :
    0 ≤ sqNorm M x := by
  classical
  by_cases hx : x = 0
  · subst hx; simp [sqNorm_zero]
  · exact le_of_lt (hM.pos x hx)

/-- [proved-derived; formal-checked] **`W² = 0` exactly at zero displacement.** A positive-definite
metric discriminates the free arm from the compensable one; no threshold is involved. -/
theorem sqNorm_eq_zero_iff [Fintype ι] {M : Matrix ι ι ℚ} (hM : PosDef M) (x : ι → ℚ) :
    sqNorm M x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact absurd h (ne_of_gt (hM.pos x hx))
  · rintro rfl; exact sqNorm_zero M

/-- [proved-derived; formal-checked] **The exact `LDLᵀ` certificate of positive definiteness.**
A declared Gram matrix whose exact rational `LDLᵀ` factorization reconstructs it, whose pivots are
all strictly positive, and whose triangular factor is injective, is positive definite. This is the
certificate the Rust owner checks before accepting a metric; no eigenvalue and no float is
involved. -/
theorem positive_definite_of_ldl [Fintype ι] (M L : Matrix ι ι ℚ) (dg : ι → ℚ)
    (hsym : ∀ x y : ι → ℚ, x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x))
    (hfact : ∀ x : ι → ℚ, sqNorm M x = ∑ j, dg j * ((Lᵀ *ᵥ x) j) ^ 2)
    (hpos : ∀ j, 0 < dg j) (hinj : ∀ x : ι → ℚ, Lᵀ *ᵥ x = 0 → x = 0) : PosDef M := by
  classical
  refine ⟨hsym, ?_⟩
  intro x hx
  rw [hfact x]
  have hne : Lᵀ *ᵥ x ≠ 0 := fun h => hx (hinj x h)
  obtain ⟨j, hj⟩ : ∃ j, (Lᵀ *ᵥ x) j ≠ 0 := by
    by_contra hall
    exact hne (funext fun j => by simpa using not_not.mp (not_exists.mp hall j))
  refine Finset.sum_pos' (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
  · exact mul_nonneg (le_of_lt (hpos i)) (sq_nonneg _)
  · exact mul_pos (hpos j) (by positivity)

/-- [proved-derived; formal-checked] **The normal equation gives the unique minimizer.** If the
metric image of a compensation is orthogonal to every allowed direction, every other compensation
in the affine family is strictly longer. This is why `W²` is exact rational linear algebra and
never a search. -/
theorem normal_equation_gives_the_unique_minimizer [Fintype ι] [Fintype κ]
    {M : Matrix ι ι ℚ} (hM : PosDef M) (A : Matrix ι κ ℚ) (delta : ι → ℚ)
    (hnormal : ∀ y : κ → ℚ, (A *ᵥ y) ⬝ᵥ (M *ᵥ delta) = 0)
    (y : κ → ℚ) (hy : A *ᵥ y ≠ 0) :
    sqNorm M delta < sqNorm M (delta + A *ᵥ y) := by
  have hexp : sqNorm M (delta + A *ᵥ y)
      = sqNorm M delta + 2 * ((A *ᵥ y) ⬝ᵥ (M *ᵥ delta)) + sqNorm M (A *ᵥ y) := by
    unfold sqNorm
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
    have hcross : delta ⬝ᵥ (M *ᵥ (A *ᵥ y)) = (A *ᵥ y) ⬝ᵥ (M *ᵥ delta) := hM.symm _ _
    rw [hcross]
    ring
  rw [hexp, hnormal y]
  have hpos := hM.pos _ hy
  linarith

/-- [proved-derived; formal-checked] **The rethreading work of a free edit is zero, and only of a
free edit.** The zero compensation is admissible exactly when the edit is free, and a
positive-definite metric makes the minimum vanish exactly there. -/
theorem work_zero_iff_free [Fintype ι] [Fintype κ] [Fintype μ] {M : Matrix ι ι ℚ}
    (hM : PosDef M) (J : Matrix μ ι ℚ) (A : Matrix ι κ ℚ) (g : ι → ℚ) (c : κ → ℚ)
    (hcomp : Compensating J A g c)
    (hmin : ∀ e : κ → ℚ, Compensating J A g e → sqNorm M (A *ᵥ c) ≤ sqNorm M (A *ᵥ e)) :
    sqNorm M (A *ᵥ c) = 0 ↔ Free J g := by
  constructor
  · intro h
    have hzero : A *ᵥ c = 0 := (sqNorm_eq_zero_iff hM _).mp h
    unfold Free
    unfold Compensating at hcomp
    rw [hzero, add_zero] at hcomp
    exact hcomp
  · intro hfree
    have hzero : Compensating J A g 0 := (free_iff_zero_compensates J A g).mp hfree
    have hle := hmin 0 hzero
    rw [mulVec_zero, sqNorm_zero] at hle
    exact le_antisymm hle (sqNorm_nonneg hM _)

/-! ## 4. Edit torque -/

/-- [definition] `τ = J_gᵀ r` under **declared identity metrics**: the adjoint pulls the unresolved
receiver residual back to the generator coordinates. -/
def torque [Fintype ρ] (Jg : Matrix ρ κ ℚ) (res : ρ → ℚ) : κ → ℚ := Jgᵀ *ᵥ res

/-- [proved-derived; formal-checked] **`τ = 0` exactly when the residual annihilates the image.** -/
theorem torque_zero_iff_residual_annihilates_image [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (Jg : Matrix ρ κ ℚ) (res : ρ → ℚ) :
    torque Jg res = 0 ↔ ∀ y : κ → ℚ, (Jg *ᵥ y) ⬝ᵥ res = 0 := by
  classical
  have hpair : ∀ y : κ → ℚ, (Jg *ᵥ y) ⬝ᵥ res = y ⬝ᵥ torque Jg res :=
    fun y => mulVec_dotProduct_transpose Jg y res
  constructor
  · intro h y
    rw [hpair y, h, dotProduct_zero]
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [hpair, single_dotProduct, one_mul] at hj
    simpa using hj

/-- [proved-derived; formal-checked] **The exact first-order expansion of the squared residual.**
The linear coefficient is exactly the pairing of the edit coefficients with the torque. -/
theorem residual_expansion [Fintype ρ] [Fintype κ] (Jg : Matrix ρ κ ℚ) (res : ρ → ℚ)
    (y : κ → ℚ) (t : ℚ) :
    (res + t • (Jg *ᵥ y)) ⬝ᵥ (res + t • (Jg *ᵥ y))
      = res ⬝ᵥ res + 2 * t * (y ⬝ᵥ torque Jg res)
        + t ^ 2 * ((Jg *ᵥ y) ⬝ᵥ (Jg *ᵥ y)) := by
  have hpair : (Jg *ᵥ y) ⬝ᵥ res = y ⬝ᵥ torque Jg res :=
    mulVec_dotProduct_transpose Jg y res
  rw [add_dotProduct, dotProduct_add, dotProduct_add, smul_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct]
  rw [dotProduct_comm res (Jg *ᵥ y), hpair]
  simp only [smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **Stationarity is the vanishing of the torque.** No first-order
edit changes the squared residual to first order exactly when `τ = 0`. -/
theorem stationary_iff_torque_zero [Fintype ρ] [Fintype κ] [DecidableEq κ]
    (Jg : Matrix ρ κ ℚ) (res : ρ → ℚ) :
    (∀ y : κ → ℚ, y ⬝ᵥ torque Jg res = 0) ↔ torque Jg res = 0 := by
  classical
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rwa [single_dotProduct, one_mul] at hj
  · intro h y
    rw [h, dotProduct_zero]

/-- [proved-derived; formal-checked] A nonzero torque has a nonzero image, so the descent step
below always exists. -/
theorem torque_nonzero_has_nonzero_image [Fintype ρ] [Fintype κ] (Jg : Matrix ρ κ ℚ)
    (res : ρ → ℚ) (h : torque Jg res ≠ 0) : Jg *ᵥ torque Jg res ≠ 0 := by
  intro himage
  apply h
  have hzero : (torque Jg res) ⬝ᵥ (torque Jg res) = 0 := by
    have hpair : (Jg *ᵥ torque Jg res) ⬝ᵥ res = (torque Jg res) ⬝ᵥ torque Jg res :=
      mulVec_dotProduct_transpose Jg (torque Jg res) res
    rw [← hpair, himage, zero_dotProduct]
  exact dotProduct_self_eq_zero.mp hzero

theorem dotProduct_self_nonneg [Fintype ι] (v : ι → ℚ) : 0 ≤ v ⬝ᵥ v := by
  simpa [dotProduct] using Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (v i)

/-- [proved-derived; formal-checked] **The exact descent step.** When the torque does not vanish the
exact rational step `‖τ‖² / ‖J_g τ‖²` along `−τ` drops the squared residual by exactly
`‖τ‖⁴ / ‖J_g τ‖²`. Nothing here is approximate and no line search is run. -/
theorem the_exact_descent_step [Fintype ρ] [Fintype κ] (Jg : Matrix ρ κ ℚ) (res : ρ → ℚ)
    (h : torque Jg res ≠ 0) :
    ∃ t : ℚ, 0 < t ∧
      (res + t • (Jg *ᵥ (-(torque Jg res)))) ⬝ᵥ (res + t • (Jg *ᵥ (-(torque Jg res))))
        = res ⬝ᵥ res
          - ((torque Jg res) ⬝ᵥ (torque Jg res)) ^ 2
            / ((Jg *ᵥ torque Jg res) ⬝ᵥ (Jg *ᵥ torque Jg res)) := by
  classical
  set tau := torque Jg res with htau
  have himage : Jg *ᵥ tau ≠ 0 := torque_nonzero_has_nonzero_image Jg res h
  have hden : 0 < (Jg *ᵥ tau) ⬝ᵥ (Jg *ᵥ tau) :=
    lt_of_le_of_ne (dotProduct_self_nonneg _) fun heq =>
      himage (dotProduct_self_eq_zero.mp heq.symm)
  have hnum : 0 < tau ⬝ᵥ tau :=
    lt_of_le_of_ne (dotProduct_self_nonneg _) fun heq => h (dotProduct_self_eq_zero.mp heq.symm)
  refine ⟨(tau ⬝ᵥ tau) / ((Jg *ᵥ tau) ⬝ᵥ (Jg *ᵥ tau)), div_pos hnum hden, ?_⟩
  have hneg : Jg *ᵥ (-tau) = -(Jg *ᵥ tau) := by rw [mulVec_neg]
  have hexp := residual_expansion Jg res (-tau)
    ((tau ⬝ᵥ tau) / ((Jg *ᵥ tau) ⬝ᵥ (Jg *ᵥ tau)))
  rw [hneg] at hexp ⊢
  rw [hexp]
  have hpair : (-tau) ⬝ᵥ tau = -(tau ⬝ᵥ tau) := by rw [neg_dotProduct]
  rw [← htau, hpair]
  have hsq : (-(Jg *ᵥ tau)) ⬝ᵥ (-(Jg *ᵥ tau)) = (Jg *ᵥ tau) ⬝ᵥ (Jg *ᵥ tau) := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg]
  rw [hsq]
  field_simp
  ring

/-! ### The adjoint uses the morphology that produced the forward carriers -/

/-- [proved-derived; formal-checked] **The adjoint characterization.** A claimed adjoint `D` of
`J_g` between a declared domain metric `M` and codomain metric `N` satisfies `M D = J_gᵀ N` exactly
when it pairs the residual with the generators the way the metrics do. A bare transpose is this
object only when both metrics are the identity, which is a declaration and not a default. -/
theorem metric_adjoint_pairs_the_residual_with_the_generators [Fintype ρ] [Fintype κ]
    (Jg : Matrix ρ κ ℚ) (M : Matrix κ κ ℚ) (N : Matrix ρ ρ ℚ) (D : Matrix κ ρ ℚ)
    (hD : M * D = Jgᵀ * N) (y : κ → ℚ) (res : ρ → ℚ) :
    (Jg *ᵥ y) ⬝ᵥ (N *ᵥ res) = y ⬝ᵥ (M *ᵥ (D *ᵥ res)) := by
  rw [mulVec_mulVec, hD, ← mulVec_mulVec]
  exact mulVec_dotProduct_transpose Jg y (N *ᵥ res)

/-! ## 5. The knot -/

/-- [definition] The Jacobian row of the *virtual* kept face joining two occurrences: the separation
whose first-order constancy is what "held together" means. -/
def pairRow (q : Flat n d) (i j : Fin n) : Flat n d := fun x =>
  bump i (fun a => 2 * (q (i, a) - q (j, a))) x - bump j (fun a => 2 * (q (i, a) - q (j, a))) x

/-- [proved-derived; formal-checked] The pair row, paired with a velocity, is exactly the
first-order change of the separation. -/
theorem pairRow_pairing (q : Flat n d) (i j : Fin n) (v : Flat n d) :
    ∑ x : Fin n × Fin d, pairRow q i j x * v x
      = ∑ a, 2 * (q (i, a) - q (j, a)) * (v (i, a) - v (j, a)) := by
  classical
  have hsplit : ∀ x : Fin n × Fin d, pairRow q i j x * v x
      = bump i (fun a => 2 * (q (i, a) - q (j, a))) x * v x
        - bump j (fun a => 2 * (q (i, a) - q (j, a))) x * v x := by
    intro x; simp [pairRow, sub_mul]
  rw [Finset.sum_congr rfl fun x _ => hsplit x, Finset.sum_sub_distrib, sum_bump, sum_bump,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/-- [definition] A pair is **implied by** a declared set of kept faces when its row is an exact
rational combination of their rows. This is the executable criterion: the combination is exhibited,
never inferred from a dimension count. -/
def ImpliedBy (S : ConstraintSystem d n m) (C : Finset (Fin m)) (i j : Fin n) : Prop :=
  ∃ lam : Fin m → ℚ, (∀ c, c ∉ C → lam c = 0) ∧
    pairRow S.place i j = ∑ c, lam c • S.rigidityMatrix c

/-- [proved-derived; formal-checked] **Knots ascend under region coarsening.** What a subregion's
induced kept faces hold, the region's induced faces hold too: the combination that certified it is
still a combination. This is the nesting direction that is true. -/
theorem impliedBy_mono {S : ConstraintSystem d n m} {C C' : Finset (Fin m)} (h : C ⊆ C')
    {i j : Fin n} (himp : ImpliedBy S C i j) : ImpliedBy S C' i j := by
  obtain ⟨lam, hsupp, hrow⟩ := himp
  exact ⟨lam, fun c hc => hsupp c fun hmem => hc (h hmem), hrow⟩

/-- [proved-derived; formal-checked] An implied pair's separation is first-order constant under
every admitted infinitesimal motion. -/
theorem impliedBy_annihilates_motions {S : ConstraintSystem d n m} {C : Finset (Fin m)}
    {i j : Fin n} (himp : ImpliedBy S C i j) {v : Flat n d} (hv : v ∈ S.infinitesimalMotions) :
    ∑ x : Fin n × Fin d, pairRow S.place i j x * v x = 0 := by
  classical
  obtain ⟨lam, -, hrow⟩ := himp
  have hker : S.rigidityMatrix *ᵥ v = 0 := hv
  rw [hrow]
  have hstep : ∀ x : Fin n × Fin d, (∑ c, lam c • S.rigidityMatrix c) x * v x
      = ∑ c, lam c * (S.rigidityMatrix c x * v x) := by
    intro x
    rw [Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by simp [mul_assoc]
  rw [Finset.sum_congr rfl fun x _ => hstep x, Finset.sum_comm]
  refine Finset.sum_eq_zero fun c _ => ?_
  have hrowzero : ∑ x : Fin n × Fin d, S.rigidityMatrix c x * v x = 0 := by
    have hc := congrFun hker c
    simpa [Matrix.mulVec, dotProduct] using hc
  rw [← Finset.mul_sum, hrowzero, mul_zero]

/-- [definition] An **ambient knot**: a set of occurrences every pair of which is first-order rigid
under every motion the whole framework admits. This is R4's rigid-cluster criterion. -/
def AmbientKnot (S : ConstraintSystem d n m) (K : Finset (Fin n)) : Prop :=
  ∀ i ∈ K, ∀ j ∈ K, ∀ v ∈ S.infinitesimalMotions,
    ∑ x : Fin n × Fin d, pairRow S.place i j x * v x = 0

/-- [proved-derived; formal-checked] **Ambient knots nest downward.** Every subregion of an ambient
knot is an ambient knot — the opposite direction to `impliedBy_mono`, and the reason the two
readings are not interchangeable. -/
theorem ambient_knot_is_downward_closed {S : ConstraintSystem d n m} {K K' : Finset (Fin n)}
    (h : K' ⊆ K) (hK : AmbientKnot S K) : AmbientKnot S K' :=
  fun i hi j hj v hv => hK i (h hi) j (h hj) v hv

/-- [proved-derived; formal-checked] Every pair implied by the faces induced at a region is an
ambient knot pair of that region. The two readings meet here and part in their nesting. -/
theorem impliedBy_gives_ambient_pair {S : ConstraintSystem d n m} {C : Finset (Fin m)}
    {i j : Fin n} (himp : ImpliedBy S C i j) {v : Flat n d}
    (hv : v ∈ S.infinitesimalMotions) :
    ∑ a, 2 * (S.place (i, a) - S.place (j, a)) * (v (i, a) - v (j, a)) = 0 := by
  rw [← pairRow_pairing]
  exact impliedBy_annihilates_motions himp hv

/-! ### The counterexample: induced implication does not descend

[counterexample; formal-checked] Three occurrences on a line at `0`, `1`, `2`, with the two
consecutive separations kept. The outer pair is held by the region's own faces; the subregion
carrying only the two outer occurrences induces **no** kept face at all and holds nothing. -/

/-- The one-dimensional three-occurrence chain: places `0`, `1`, `2`, faces `(0,1)` and `(1,2)`. -/
def lineChain : ConstraintSystem 1 3 2 where
  left := ![0, 1]
  right := ![1, 2]
  place := fun x => ((x.1 : ℕ) : ℚ)

theorem the_outer_pair_is_implied_at_the_whole_region :
    ImpliedBy lineChain Finset.univ 0 2 := by
  refine ⟨![2, 2], fun c hc => absurd (Finset.mem_univ c) hc, ?_⟩
  funext x
  obtain ⟨i, a⟩ := x
  fin_cases i <;> fin_cases a <;>
    simp [pairRow, bump, lineChain, ConstraintSystem.rigidityMatrix, ConstraintSystem.delta,
      Fin.sum_univ_two, Fin.ext_iff] <;> ring

theorem the_outer_pair_is_not_implied_at_the_subregion :
    ¬ ImpliedBy lineChain (∅ : Finset (Fin 2)) 0 2 := by
  rintro ⟨lam, hsupp, hrow⟩
  have hzero : ∀ c, lam c = 0 := fun c => hsupp c (Finset.notMem_empty c)
  have hx := congrFun hrow (0, 0)
  simp [hzero, pairRow, bump, lineChain] at hx

/-- [counterexample; formal-checked] **Induced implication does not descend.** The pair is held at
the region and not at the subregion, so "rigidity of a region implies rigidity of a subregion's
induced framework" is false; only the ascending direction, `impliedBy_mono`, holds. -/
theorem induced_implication_does_not_descend :
    ImpliedBy lineChain Finset.univ 0 2 ∧ ¬ ImpliedBy lineChain (∅ : Finset (Fin 2)) 0 2 :=
  ⟨the_outer_pair_is_implied_at_the_whole_region, the_outer_pair_is_not_implied_at_the_subregion⟩

/-! ### First-order stationarity is not cancellation -/

/-- A kept face between two occurrences at coincident places. Its Jacobian row vanishes — R4's
`rigidityMatrix_row_eq_zero_of_coincident` — so every torque at it is zero. -/
def coincidentFace : ConstraintSystem 1 2 1 where
  left := ![0]
  right := ![1]
  place := fun _ => 0

theorem the_coincident_face_has_a_zero_row (x : Fin 2 × Fin 1) :
    coincidentFace.rigidityMatrix 0 x = 0 := by
  refine coincidentFace.rigidityMatrix_row_eq_zero_of_coincident 0 ?_ x
  intro a
  simp [ConstraintSystem.delta, coincidentFace]

/-- The separating second-order edit: it moves the first occurrence and not the second. -/
def coincidentEdit : Flat 2 1 := fun x => if x.1 = 0 then (1 : ℚ) else 0

/-- [proved-derived; formal-checked] **`τ = 0` is necessary and not sufficient.** At a kept face
whose Jacobian row vanishes every torque is zero for every residual, and yet the separating
second-order edit moves the face by exactly `t²`. That remainder is R4's own
`jacobian_is_the_differential`, so this is the honest relation between first-order stationarity and
`ArtifactRelease.the_rotation_tube_carries_no_holonomy`'s identity holonomy: the first does not
imply the second. -/
theorem stationarity_is_not_cancellation :
    (∀ res : Fin 1 → ℚ, torque coincidentFace.rigidityMatrix res = 0) ∧
      ∀ t : ℚ, coincidentFace.constraintMap 0 (coincidentFace.place + t • coincidentEdit)
        = t ^ 2 := by
  constructor
  · intro res
    funext x
    unfold torque
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, the_coincident_face_has_a_zero_row]
  · intro t
    rw [coincidentFace.jacobian_is_the_differential 0 coincidentEdit t]
    have hrow : (coincidentFace.rigidityMatrix *ᵥ coincidentEdit) 0 = 0 := by
      simp [Matrix.mulVec, dotProduct, the_coincident_face_has_a_zero_row]
    rw [hrow]
    simp [ConstraintSystem.delta, coincidentFace, coincidentEdit]

/-! ## Audit

[definition] Every headline declaration's axiom dependencies, printed by the kernel. Only
`propext`, `Classical.choice` and `Quot.sound` are acceptable; `sorryAx` appears nowhere. -/

namespace Audit

#print axioms dual_is_dotProduct
#print axioms mem_range_iff_annihilators_vanish
#print axioms the_kept_face_differential_is_the_rigidity_jacobian
#print axioms kept_rank_nullity
#print axioms kept_self_stress_dimension
#print axioms linear_face_is_its_own_differential
#print axioms free_iff_mem_ker
#print axioms compensating_iff_solves
#print axioms compensating_family_is_affine
#print axioms free_iff_zero_compensates
#print axioms obstructed_iff_certificate
#print axioms selfStressSpace_rigidity
#print axioms entangled_iff_dependent
#print axioms dependent_iff_droppingLosesNothing
#print axioms entanglement_is_self_stress_support
#print axioms a_face_carrying_no_self_stress_forbids_an_edit_of_its_own
#print axioms first_order_edits_always_commute
#print axioms sqNorm_eq_zero_iff
#print axioms positive_definite_of_ldl
#print axioms normal_equation_gives_the_unique_minimizer
#print axioms work_zero_iff_free
#print axioms torque_zero_iff_residual_annihilates_image
#print axioms residual_expansion
#print axioms stationary_iff_torque_zero
#print axioms torque_nonzero_has_nonzero_image
#print axioms the_exact_descent_step
#print axioms metric_adjoint_pairs_the_residual_with_the_generators
#print axioms pairRow_pairing
#print axioms impliedBy_mono
#print axioms impliedBy_annihilates_motions
#print axioms ambient_knot_is_downward_closed
#print axioms impliedBy_gives_ambient_pair
#print axioms the_outer_pair_is_implied_at_the_whole_region
#print axioms the_outer_pair_is_not_implied_at_the_subregion
#print axioms induced_implication_does_not_descend
#print axioms the_coincident_face_has_a_zero_row
#print axioms stationarity_is_not_cancellation

end Audit

end Holonics.Transport.EditRigidity

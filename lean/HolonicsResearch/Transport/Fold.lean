import Holonics.Foundation.ContinuingTower
import Holonics.Transport.ContinuingTube
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# The fold: a reflection applied to one side of a crease

[definition] This owner states the law the Rust module `crates/holonic-engine/src/fold.rs`
implements. It is the fold/cut half of item **T7** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Eight things are
stated here, in this order.

1. **A fold is a reflection applied to one side of a crease.** With `H` a hyperplane of `ℚ^d`
   given by an exact rational normal and offset, `fold x = x` on the closed positive side and
   `reflect x = x − 2 σ(x) n / ⟨n,n⟩` on the negative side. Everything is exact over `ℚ`:
   the reflection needs `⟨n,n⟩` and never a square root. `reflect` is an involution
   (`reflect_involutive`) fixing the crease pointwise (`reflect_eq_self_of_side_zero`) and
   preserving every squared distance (`reflect_distSq`). **The fold is a piecewise isometry and
   not an isometry**: `fold_distSq_same_side` preserves every squared distance inside one closed
   side, and `fold_distSq_opposite_side` gives the exact defect across the crease,
   `4 σ(x) σ(y) / ⟨n,n⟩`, which `fold_brings_the_two_sides_together` reads as a strict decrease.
   That defect **is** the content of folding: each half stays rigid and the two halves move
   relative to each other.
2. **A bounce is that fold read in the trajectory.** `side_segment` makes the signed side affine
   along a segment, `crossing_side_eq_zero` locates the crossing exactly over `ℚ`, and
   `fold_segment_before` / `fold_segment_after` say the folded straight segment is the reflected
   path. Equal angles need no angle: `linReflect_fixes_tangential` and `linReflect_normal` say the
   tangential component of the direction is fixed and the normal component negated, which
   `bounce_direction` states in one line.
3. **Reversibility is the residual.** `foldTransition` is a
   `Foundation/ContinuingTower.lean::Transition` whose residual is one bit — the side — and whose
   `reopen_apply` is exact. `fold_fibre` proves the map is two-to-one off the crease: the fibre of
   `fold` through `x` is `{x, reflect x}`, so the fold **is** the quotient of the sheet by the
   reflection onto the closed positive half-space as a fundamental domain
   (`fold_mem_positive_side`, `fold_eq_self_iff`). `k` folds carry `k` bits and `2 ^ k` layers
   (`sideWord_card`), which is the dyadic tube's branching cross-section at `p = 2`
   (`k_folds_branch_dyadically`, cited from `ContinuingTube.padicTube_crossSection_branching`).
   `residual_injective_on_fibre` is the comparison a cut loses: a transition's residual separates
   every element of one fibre, so **the residual is at least as large as the largest fibre** — one
   bit for a fold, the whole gluing pattern for a cut.
4. **Rotation is two reflections, exactly over `ℚ`.** In the plane, writing a direction as a
   Gaussian rational, `lineReflect_comp_eq_rotBy` proves `R_v ∘ R_u = rot(v ū)` with no angle and
   no square root, and `rotBy_eq_id_iff` decides when a rotation is the identity by one rational
   equation. **Kawasaki's condition is that equation**: `kawasaki_iff` proves the ordered product
   of the `2n` crease reflections at a vertex is the identity exactly when the accumulated turn
   `∏ (d_{2k} d̄_{2k−1})` has zero imaginary part. `plusVertexIsFlatFoldable` and
   `skewVertexIsNotFlatFoldable` are the two exact degree-four instances.
   **Maekawa** is `maekawa_iff_mountain_count`: `M − V = ±2` is exactly `M = n + 1 ∨ M = n − 1` at
   a degree-`2n` vertex, decided by `maekawa_degree_four` on all sixteen assignments.
5. **A shear is not a fold.** `shear_changes_a_squared_distance_at_every_point_and_scale` proves a
   nonzero shear changes a squared distance in every neighbourhood of every point, so
   `no_isometry_is_a_shear`: a shear is not a composition of reflections and deforms the lattice
   rather than folding it. **Inversion** is the other member of Brandon's triple:
   `inversion_distSq` is exact over `ℚ` and `inversion_preserves_cross_ratio` follows from it with
   every factor cancelling.
6. **A fold preserves homology; a cut does not.** `fold_preserves_betti` is the statement this
   file can actually prove: a **cellular automorphism** — a relabelling of cells by bijections
   commuting with the boundary — leaves every rank and therefore every Betti number unchanged,
   through `Matrix.rank_submatrix`. The **quotient** statement is the two-to-one `fold_fibre`
   above, and the worked cut instances (an annulus cut to a disc, a disc cut in two) are the Rust
   owner's, computed by the existing Smith-normal-form owner. `fold_preserves_intrinsic_length` is
   the metric half: an edge with both endpoints on one closed side keeps its exact length.
7. **Unfolding at a tolerance is the fold catastrophe.** `foldEquilibria_iff` proves `V_a(x) =
   x³/3 − a x` has an equilibrium exactly when `0 ≤ a`, two when `0 < a`
   (`foldEquilibria_two_of_pos`) and none below (`no_equilibrium_of_neg`), with stability decided
   by the sign of `V''` (`positiveRoot_is_stable`, `negativeRoot_is_unstable`). The declared crease
   model `creaseTorque` puts a gravity load against a polynomial hinge torque and
   `held_equilibrium_iff_load_le_threshold` gives the exact threshold `κ u₀²` at which the held
   state disappears. Brandon's lever arm is `displacementSq_scales_with_lever`: under the rational
   parametrization of a rotation the displacement of a point at distance `ℓ` from the crease is
   exactly proportional to `ℓ`, with no square root anywhere (`rationalRotation_orthogonal`).
8. **The backbone is rigid origami of a one-dimensional linkage.** `backboneBarCount` itemizes the
   bars a fixed-bond-length, fixed-bond-angle, planar-`ω` chain carries and
   `backbone_internal_dof` is the exact prediction `2(r − 1)` the Rust owner measures against the
   real M5 presentations. A dihedral needs an angle, so none is taken: `lagrange_identity` makes
   `dihedralCosSq` an exact rational in `[0,1]` (`dihedralCosSq_nonneg`, `dihedralCosSq_le_one`),
   and a Ramachandran region is a *declared* partition of the `(sign, cos²)` chart with a ground.
   A lattice-protein pivot is `pivot_preserves_squared_lengths` with `pivot_fixes_the_axis`.

[definition] What this file does **not** do: it states no milestone, schedules nothing, and founds
no second reflection algebra. `Millennium/Swing.lean`'s frozen-board point reflection `A ↦ 2B − A`
and `Millennium/Seam.lean`'s `conjugateReflection` remain their own owners; this file is the
*hyperplane* reflection of `ℚ^d` and its one-sided application, which neither of those carries.

Rust owner: `crates/holonic-engine/src/fold.rs`.
-/

noncomputable section

namespace Holonics.Transport.Fold

open Holonics.Foundation.ContinuingTower
open Finset

universe u

/-! ## 1. The exact bilinear form on `ℚ^d` -/

/-- [definition] The standard bilinear form, exact over `ℚ`. No norm is taken anywhere in this
file: every statement is about the *squared* quantity, which is why nothing needs a square root. -/
def dot {d : ℕ} (x y : Fin d → ℚ) : ℚ := ∑ a, x a * y a

/-- [definition] The squared distance. -/
def distSq {d : ℕ} (x y : Fin d → ℚ) : ℚ := dot (fun a => x a - y a) (fun a => x a - y a)

variable {d : ℕ}

theorem dot_comm (x y : Fin d → ℚ) : dot x y = dot y x :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem dot_sub_right (x y z : Fin d → ℚ) :
    dot x (fun a => y a - z a) = dot x y - dot x z := by
  simp only [dot, mul_sub, Finset.sum_sub_distrib]

theorem dot_smul_right (c : ℚ) (x y : Fin d → ℚ) :
    dot x (fun a => c * y a) = c * dot x y := by
  simp only [dot, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem dot_sub_left (x y z : Fin d → ℚ) :
    dot (fun a => x a - y a) z = dot x z - dot y z := by
  rw [dot_comm, dot_sub_right, dot_comm x z, dot_comm y z]

/-- [proved-derived; formal-checked] **The expansion of the form on an affine pair.** Every
distance computation below is one instance of this identity, so no sum manipulation is repeated. -/
theorem dot_pair (u v : Fin d → ℚ) (c e : ℚ) :
    dot (fun a => c * u a + e * v a) (fun a => c * u a + e * v a)
      = c * c * dot u u + 2 * (c * e) * dot u v + e * e * dot v v := by
  simp only [dot]
  rw [show (∑ a, (c * u a + e * v a) * (c * u a + e * v a))
      = ∑ a, ((c * c) * (u a * u a) + (2 * (c * e)) * (u a * v a) + (e * e) * (v a * v a)) from
    Finset.sum_congr rfl fun _ _ => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

/-- [proved-derived; formal-checked] The same expansion with a shift along a common vector. -/
theorem dot_shift (u v w : Fin d → ℚ) (c e : ℚ) :
    dot (fun a => u a + c * w a) (fun a => v a + e * w a)
      = dot u v + e * dot u w + c * dot w v + c * e * dot w w := by
  simp only [dot]
  rw [show (∑ a, (u a + c * w a) * (v a + e * w a))
      = ∑ a, (u a * v a + e * (u a * w a) + c * (w a * v a) + (c * e) * (w a * w a)) from
    Finset.sum_congr rfl fun _ _ => by ring]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

theorem dot_self_nonneg (x : Fin d → ℚ) : 0 ≤ dot x x :=
  Finset.sum_nonneg fun _ _ => mul_self_nonneg _

/-- [proved-derived; formal-checked] Over `ℚ` the form is definite: a sum of squares vanishes only
at zero. This is why a crease may be declared by `⟨n,n⟩ ≠ 0` and never needs a norm. -/
theorem dot_self_eq_zero_iff (x : Fin d → ℚ) : dot x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext a
    have hnn : ∀ b ∈ (Finset.univ : Finset (Fin d)), 0 ≤ x b * x b := fun _ _ => mul_self_nonneg _
    have h0 : ∑ b, x b * x b = 0 := h
    have hb := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 a (Finset.mem_univ a)
    simpa using mul_self_eq_zero.mp hb
  · rintro rfl; simp [dot]

/-! ## 2. The crease, the reflection and the fold -/

/-- [definition] An exact rational crease: a hyperplane `⟨n, x⟩ = b` of `ℚ^d`. The nondegeneracy
field is `⟨n,n⟩ ≠ 0`, which over `ℚ` is exactly `n ≠ 0` (`dot_self_eq_zero_iff`); it is carried in
that form because it is the denominator every reflection divides by.

Rust counterpart: `crates/holonic-engine/src/fold.rs::Crease`. -/
structure Crease (d : ℕ) where
  /-- The exact rational normal. -/
  normal : Fin d → ℚ
  /-- The exact rational offset: the crease is `⟨normal, x⟩ = offset`. -/
  offset : ℚ
  /-- `⟨n,n⟩ ≠ 0`. -/
  nondegenerate : dot normal normal ≠ 0

namespace Crease

variable (H : Crease d)

/-- [definition] The **signed side**: `σ(x) = ⟨n, x⟩ − b`. Zero exactly on the crease. -/
def side (x : Fin d → ℚ) : ℚ := dot H.normal x - H.offset

/-- [definition] The linear part of the reflection: `v ↦ v − 2⟨n,v⟩ n / ⟨n,n⟩`. -/
def linReflect (v : Fin d → ℚ) : Fin d → ℚ :=
  fun a => v a - 2 * dot H.normal v / dot H.normal H.normal * H.normal a

/-- [definition] The **reflection across the crease**: `R x = x − 2 σ(x) n / ⟨n,n⟩`. Exact over
`ℚ`; the only division is by `⟨n,n⟩`, which the constructor keeps nonzero. -/
def reflect (x : Fin d → ℚ) : Fin d → ℚ :=
  fun a => x a - 2 * H.side x / dot H.normal H.normal * H.normal a

/-- [definition] **The fold**: the reflection applied to one side. The closed positive side is the
fundamental domain and is fixed; the negative side is carried onto it. -/
def fold (x : Fin d → ℚ) : Fin d → ℚ := if 0 ≤ H.side x then x else H.reflect x

/-- [definition] The **side bit**: the residual of the fold. `true` means the point was reflected. -/
def sideBit (x : Fin d → ℚ) : Bool := decide (H.side x < 0)

/-- [definition] Reopening: undo the reflection exactly when the bit says it happened. -/
def reopen (y : Fin d → ℚ) (bit : Bool) : Fin d → ℚ := if bit then H.reflect y else y

theorem dot_normal_reflect (x : Fin d → ℚ) :
    dot H.normal (H.reflect x) = dot H.normal x - 2 * H.side x := by
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  show dot H.normal (fun a => x a - 2 * H.side x / dot H.normal H.normal * H.normal a) = _
  rw [dot_sub_right, dot_smul_right]
  field_simp

/-- [proved-derived; formal-checked] **The reflection flips the side.** -/
@[simp] theorem side_reflect (x : Fin d → ℚ) : H.side (H.reflect x) = - H.side x := by
  have h := H.dot_normal_reflect x
  simp only [side] at h ⊢
  linarith

/-- [proved-derived; formal-checked] **The reflection is an involution.** -/
@[simp] theorem reflect_involutive (x : Fin d → ℚ) : H.reflect (H.reflect x) = x := by
  funext a
  simp only [reflect, side_reflect]
  ring

/-- [proved-derived; formal-checked] **The crease is fixed pointwise.** -/
theorem reflect_eq_self_of_side_zero {x : Fin d → ℚ} (h : H.side x = 0) : H.reflect x = x := by
  funext a; simp [reflect, h]

/-- [proved-derived; formal-checked] The reflection's difference is its linear part: the reflection
is affine and its linear part is what carries every metric statement. -/
theorem reflect_sub (x y : Fin d → ℚ) :
    (fun a => H.reflect x a - H.reflect y a) = H.linReflect (fun a => x a - y a) := by
  funext a
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  simp only [reflect, linReflect, side, dot_sub_right]
  field_simp
  ring

theorem linReflect_eq (u : Fin d → ℚ) :
    H.linReflect u
      = fun a => u a + (-(2 * dot H.normal u / dot H.normal H.normal)) * H.normal a := by
  funext a; simp only [linReflect]; ring

/-- [proved-derived; formal-checked] **The linear reflection preserves the form.** -/
theorem linReflect_dot (u v : Fin d → ℚ) :
    dot (H.linReflect u) (H.linReflect v) = dot u v := by
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  rw [linReflect_eq, linReflect_eq, dot_shift, dot_comm u H.normal]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The tangential component is fixed.** No angle is needed to
say the incoming and outgoing rays of a bounce make equal angles with the crease: the component
along the crease is untouched. -/
theorem linReflect_fixes_tangential {v : Fin d → ℚ} (h : dot H.normal v = 0) :
    H.linReflect v = v := by
  funext a; simp [linReflect, h]

/-- [proved-derived; formal-checked] **The normal component is negated.** That is the other half of
"equal angles". -/
theorem linReflect_normal : H.linReflect H.normal = fun a => - H.normal a := by
  funext a
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  simp only [linReflect]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The reflection is an isometry**: every squared distance is
preserved, exactly. -/
theorem reflect_distSq (x y : Fin d → ℚ) : distSq (H.reflect x) (H.reflect y) = distSq x y := by
  simp only [distSq, reflect_sub, linReflect_dot]

/-! ### The fold is a piecewise isometry and not an isometry -/

/-- [proved-derived; formal-checked] **Each half stays rigid.** Two points on the same closed side
keep their exact squared distance under the fold. -/
theorem fold_distSq_same_side {x y : Fin d → ℚ}
    (h : (0 ≤ H.side x ∧ 0 ≤ H.side y) ∨ (H.side x < 0 ∧ H.side y < 0)) :
    distSq (H.fold x) (H.fold y) = distSq x y := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rw [fold, fold, if_pos hx, if_pos hy]
  · rw [fold, fold, if_neg (not_le.mpr hx), if_neg (not_le.mpr hy), reflect_distSq]

/-- [proved-derived; formal-checked] **The two halves move relative to each other, by exactly this
much.** Across the crease the fold changes the squared distance by `4 σ(x) σ(y) / ⟨n,n⟩`. That
defect is the whole content of folding, and it is exact. -/
theorem fold_distSq_opposite_side {x y : Fin d → ℚ}
    (hx : 0 ≤ H.side x) (hy : H.side y < 0) :
    distSq (H.fold x) (H.fold y)
      = distSq x y + 4 * H.side x * H.side y / dot H.normal H.normal := by
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  rw [fold, fold, if_pos hx, if_neg (not_le.mpr hy)]
  have hsplit : (fun a => x a - H.reflect y a)
      = (fun a => (x a - y a) + (2 * H.side y / dot H.normal H.normal) * H.normal a) := by
    funext a; simp only [reflect]; ring
  have hnx : dot (fun a => x a - y a) H.normal = H.side x - H.side y := by
    rw [dot_sub_left, dot_comm x H.normal, dot_comm y H.normal]
    simp only [side]; ring
  have hxn : dot H.normal (fun a => x a - y a) = H.side x - H.side y := by
    rw [dot_comm]; exact hnx
  show dot (fun a => x a - H.reflect y a) (fun a => x a - H.reflect y a) = _
  rw [hsplit, dot_shift, hnx, hxn]
  simp only [distSq]
  field_simp
  ring

/-- [proved-derived; formal-checked] **A fold brings the two sides strictly together.** With `x`
strictly positive and `y` strictly negative the squared distance strictly decreases: the fold is
not an isometry, and this is the exact sense in which it is not. -/
theorem fold_brings_the_two_sides_together {x y : Fin d → ℚ}
    (hx : 0 < H.side x) (hy : H.side y < 0) :
    distSq (H.fold x) (H.fold y) < distSq x y := by
  have hN : 0 < dot H.normal H.normal :=
    lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm H.nondegenerate)
  rw [fold_distSq_opposite_side H (le_of_lt hx) hy]
  have hnum : 4 * H.side x * H.side y < 0 := by nlinarith
  have : 4 * H.side x * H.side y / dot H.normal H.normal < 0 := div_neg_of_neg_of_pos hnum hN
  linarith

/-! ### The fold is the quotient onto a fundamental domain -/

/-- [proved-derived; formal-checked] **The fold lands in the closed positive side**, which is
therefore a fundamental domain for the reflection. -/
theorem fold_mem_positive_side (x : Fin d → ℚ) : 0 ≤ H.side (H.fold x) := by
  by_cases h : 0 ≤ H.side x
  · rw [fold, if_pos h]; exact h
  · rw [fold, if_neg h, side_reflect]
    linarith [not_le.mp h]

/-- [proved-derived; formal-checked] The fold fixes exactly the closed positive side. -/
theorem fold_eq_self_iff (x : Fin d → ℚ) : H.fold x = x ↔ 0 ≤ H.side x := by
  constructor
  · intro h
    by_contra hx
    rw [fold, if_neg hx] at h
    have hside := H.side_reflect x
    rw [h] at hside
    linarith [not_le.mp hx]
  · intro hx; rw [fold, if_pos hx]

/-- [proved-derived; formal-checked] **The fold is two-to-one off the crease.** Its fibre through
`x` is exactly `{x, reflect x}`: folding in half is the quotient of the sheet by the reflection,
and the side bit is the remainder. -/
theorem fold_fibre {x y : Fin d → ℚ} (h : H.fold y = H.fold x) : y = x ∨ y = H.reflect x := by
  by_cases hx : 0 ≤ H.side x <;> by_cases hy : 0 ≤ H.side y
  · rw [fold, if_pos hy, fold, if_pos hx] at h; exact Or.inl h
  · rw [fold, if_neg hy, fold, if_pos hx] at h
    have h2 := congrArg H.reflect h
    rw [reflect_involutive] at h2
    exact Or.inr h2
  · rw [fold, if_pos hy, fold, if_neg hx] at h
    exact Or.inr h
  · rw [fold, if_neg hy, fold, if_neg hx] at h
    have h2 := congrArg H.reflect h
    rw [reflect_involutive, reflect_involutive] at h2
    exact Or.inl h2

/-- [proved-derived; formal-checked] **Reopening is exact.** -/
theorem reopen_apply_fold (x : Fin d → ℚ) : H.reopen (H.fold x) (H.sideBit x) = x := by
  by_cases hx : 0 ≤ H.side x
  · have hbit : H.sideBit x = false := by simp [sideBit, not_lt.mpr hx]
    rw [fold, if_pos hx, reopen, hbit, if_neg (by simp)]
  · have hlt : H.side x < 0 := not_le.mp hx
    have hbit : H.sideBit x = true := by simp [sideBit, hlt]
    rw [fold, if_neg hx, reopen, hbit, if_pos (by simp), reflect_involutive]

/-- [definition] **The fold as a transition whose residual is the side bit.**

Rust counterpart: `fold.rs::FoldTransition`, which implements
`continuing_tower.rs::Transition` with `Residual = Side`. -/
def foldTransition : Transition (Fin d → ℚ) (Fin d → ℚ) where
  Residual := Bool
  apply := H.fold
  residual := H.sideBit
  reopen := H.reopen
  reopen_apply := H.reopen_apply_fold

@[simp] theorem foldTransition_apply (x : Fin d → ℚ) :
    (H.foldTransition).apply x = H.fold x := rfl

@[simp] theorem foldTransition_residual (x : Fin d → ℚ) :
    (H.foldTransition).residual x = H.sideBit x := rfl

/-! ### The bounce: the billiard unfolding -/

/-- [definition] The straight segment from `a` to `b`. -/
def segment (a b : Fin d → ℚ) (t : ℚ) : Fin d → ℚ := fun i => a i + t * (b i - a i)

/-- [proved-derived; formal-checked] **The signed side is affine along a straight segment.** -/
theorem side_segment (a b : Fin d → ℚ) (t : ℚ) :
    H.side (segment a b t) = (1 - t) * H.side a + t * H.side b := by
  have hsplit : segment a b t = fun i => a i + t * (b i - a i) := rfl
  show dot H.normal (segment a b t) - H.offset = _
  rw [hsplit]
  have : dot H.normal (fun i => a i + t * (b i - a i))
      = dot H.normal a + t * dot H.normal (fun i => b i - a i) := by
    simp only [dot]
    rw [show (∑ i, H.normal i * (a i + t * (b i - a i)))
        = ∑ i, (H.normal i * a i + t * (H.normal i * (b i - a i))) from
      Finset.sum_congr rfl fun _ _ => by ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [this, dot_sub_right]
  simp only [side]
  ring

/-- [definition] The exact rational crossing parameter of a segment that changes side. -/
def crossing (a b : Fin d → ℚ) : ℚ := H.side a / (H.side a - H.side b)

/-- [proved-derived; formal-checked] **The crossing is exact over `ℚ`.** No root is taken: a
straight segment meets a hyperplane at a rational parameter. -/
theorem crossing_side_eq_zero {a b : Fin d → ℚ} (h : H.side a ≠ H.side b) :
    H.side (segment a b (H.crossing a b)) = 0 := by
  have hd : H.side a - H.side b ≠ 0 := sub_ne_zero.mpr h
  rw [side_segment, crossing]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Before the crossing the folded trajectory is the straight
one.** -/
theorem fold_segment_before {a b : Fin d → ℚ} {t : ℚ}
    (h : 0 ≤ H.side (segment a b t)) : H.fold (segment a b t) = segment a b t := by
  rw [fold, if_pos h]

/-- [proved-derived; formal-checked] **After it the folded trajectory is the reflected one**: the
billiard path off the wall is the image of a straight segment under the fold. -/
theorem fold_segment_after {a b : Fin d → ℚ} {t : ℚ}
    (h : H.side (segment a b t) < 0) :
    H.fold (segment a b t) = H.reflect (segment a b t) := by
  rw [fold, if_neg (not_le.mpr h)]

/-- [proved-derived; formal-checked] **The bounce reverses only the normal component of the
direction.** Writing the direction as a tangential part plus a multiple of the normal, the
tangential part survives and the normal part is negated — which is "equal angles" with no angle
taken. -/
theorem bounce_direction (v : Fin d → ℚ) (c : ℚ) (hv : dot H.normal v = 0) :
    H.linReflect (fun a => v a + c * H.normal a) = fun a => v a - c * H.normal a := by
  have hN : dot H.normal H.normal ≠ 0 := H.nondegenerate
  have hsum : dot H.normal (fun j => v j + c * H.normal j) = c * dot H.normal H.normal := by
    simp only [dot]
    rw [show (∑ j, H.normal j * (v j + c * H.normal j))
        = ∑ j, (H.normal j * v j + c * (H.normal j * H.normal j)) from
      Finset.sum_congr rfl fun _ _ => by ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simpa [dot] using hv
  funext a
  simp only [linReflect, hsum]
  field_simp
  ring

end Crease

/-! ## 3. `k` folds: the dyadic tube -/

/-- [proved-derived; formal-checked] **`k` folds carry `k` bits and `2 ^ k` layers.** -/
theorem sideWord_card (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by simp

/-- [proved-derived; formal-checked] **The layers of `k` folds are the dyadic tube's branching
cross-section.** This is `Transport/ContinuingTube.lean::padicTube_crossSection_branching` at
`p = 2`, cited and not rebuilt: refining `k` steps branches exactly `2 ^ k` ways, which is exactly
the layer count of `k` folds. -/
theorem k_folds_branch_dyadically (Station : Type u) [Preorder Station] (s : Station)
    (m k : ℕ) (face : ZMod (2 ^ m)) :
    Nat.card { x : ZMod (2 ^ (m + k)) //
        ((ContinuingTube.padicTube 2 Station).station s).restrict (Nat.le_add_right m k) x
          = face } = 2 ^ k :=
  ContinuingTube.padicTube_crossSection_branching 2 Station s m k face

/-- [proved-derived; formal-checked] **A transition's residual separates every element of one
fibre.** So the residual is at least as large as the largest fibre: one bit for a fold, whose
fibres have two elements, and the whole gluing pattern for a cut, whose fibre is as large as the
set of cells it identified. This is the exact comparison T7 asks for, and it is
`Transition.apply_residual_injective` read on a fibre. -/
theorem residual_injective_on_fibre {Source : Type u} {Target : Type u}
    (f : Transition Source Target) (t : Target) :
    Function.Injective (fun x : { x : Source // f.apply x = t } => f.residual x.1) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  exact Subtype.ext (f.apply_residual_injective (hx.trans hy.symm) h)

/-! ## 4. Rotation is two reflections, exactly over `ℚ` -/

/-- [definition] Gaussian-rational multiplication on `ℚ × ℚ`. The plane's reflections and rotations
are exactly rational in this chart, which is why no angle and no square root appears below. -/
def cmul (u v : ℚ × ℚ) : ℚ × ℚ := (u.1 * v.1 - u.2 * v.2, u.1 * v.2 + u.2 * v.1)

/-- [definition] Conjugation. -/
def cconj (u : ℚ × ℚ) : ℚ × ℚ := (u.1, -u.2)

/-- [definition] The squared modulus. -/
def cnormSq (u : ℚ × ℚ) : ℚ := u.1 ^ 2 + u.2 ^ 2

/-- [definition] Scaling. -/
def cscale (a : ℚ) (u : ℚ × ℚ) : ℚ × ℚ := (a * u.1, a * u.2)

theorem cmul_comm (u v : ℚ × ℚ) : cmul u v = cmul v u := by
  simp only [cmul, Prod.mk.injEq]
  constructor <;> ring

/-- [proved-derived; formal-checked] The Brahmagupta–Fibonacci identity: the squared modulus is
multiplicative, exactly over `ℚ`. -/
theorem cnormSq_cmul (u v : ℚ × ℚ) : cnormSq (cmul u v) = cnormSq u * cnormSq v := by
  simp only [cnormSq, cmul]; ring

theorem cnormSq_eq_zero_iff (u : ℚ × ℚ) : cnormSq u = 0 ↔ u = 0 := by
  simp only [cnormSq, Prod.ext_iff, Prod.fst_zero, Prod.snd_zero]
  constructor
  · intro h
    exact ⟨by nlinarith [sq_nonneg u.1, sq_nonneg u.2], by nlinarith [sq_nonneg u.1, sq_nonneg u.2]⟩
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

theorem cnormSq_ne_zero {u : ℚ × ℚ} (h : u ≠ 0) : cnormSq u ≠ 0 :=
  fun hc => h ((cnormSq_eq_zero_iff u).mp hc)

theorem cnormSq_cconj (u : ℚ × ℚ) : cnormSq (cconj u) = cnormSq u := by
  simp only [cnormSq, cconj]; ring

theorem cmul_ne_zero {u v : ℚ × ℚ} (hu : u ≠ 0) (hv : v ≠ 0) : cmul u v ≠ 0 := by
  intro hc
  have h : cnormSq (cmul u v) = 0 := by rw [hc]; simp [cnormSq]
  rw [cnormSq_cmul] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact cnormSq_ne_zero hu h'
  · exact cnormSq_ne_zero hv h'

theorem cconj_ne_zero {u : ℚ × ℚ} (hu : u ≠ 0) : cconj u ≠ 0 := by
  intro hc
  have h : cnormSq (cconj u) = 0 := by rw [hc]; simp [cnormSq]
  rw [cnormSq_cconj] at h
  exact cnormSq_ne_zero hu h

/-- [definition] **The reflection across the line through the origin with direction `u`**, written
in the Gaussian chart: `z ↦ u² z̄ / |u|²`. -/
def lineReflect (u z : ℚ × ℚ) : ℚ × ℚ := cscale (1 / cnormSq u) (cmul (cmul u u) (cconj z))

/-- [definition] **The rotation by twice the angle of `w`**: `z ↦ w² z / |w|²`. -/
def rotBy (w z : ℚ × ℚ) : ℚ × ℚ := cscale (1 / cnormSq w) (cmul (cmul w w) z)

/-- [proved-derived; formal-checked] A line reflection is an involution. -/
theorem lineReflect_involutive {u : ℚ × ℚ} (hu : u ≠ 0) (z : ℚ × ℚ) :
    lineReflect u (lineReflect u z) = z := by
  have hN : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by simpa [cnormSq] using cnormSq_ne_zero hu
  simp only [lineReflect, cscale, cmul, cconj, cnormSq, Prod.ext_iff]
  constructor <;> (field_simp; try ring)

/-- [proved-derived; formal-checked] **It is a reflection of a line and not of a ray**: rescaling
the direction by any nonzero rational, including a negative one, leaves it unchanged. -/
theorem lineReflect_cscale {u : ℚ × ℚ} (hu : u ≠ 0) {c : ℚ} (hc : c ≠ 0) (z : ℚ × ℚ) :
    lineReflect (cscale c u) z = lineReflect u z := by
  have hN : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by simpa [cnormSq] using cnormSq_ne_zero hu
  simp only [lineReflect, cscale, cmul, cconj, cnormSq, Prod.ext_iff]
  constructor <;> (field_simp; try ring)

/-- [proved-derived; formal-checked] The direction of the line is fixed. -/
theorem lineReflect_fixes_direction {u : ℚ × ℚ} (hu : u ≠ 0) : lineReflect u u = u := by
  have hN : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by simpa [cnormSq] using cnormSq_ne_zero hu
  simp only [lineReflect, cscale, cmul, cconj, cnormSq, Prod.ext_iff]
  constructor <;> (field_simp; try ring)

/-- [proved-derived; formal-checked] A line reflection preserves the squared modulus. -/
theorem lineReflect_cnormSq {u : ℚ × ℚ} (hu : u ≠ 0) (z : ℚ × ℚ) :
    cnormSq (lineReflect u z) = cnormSq z := by
  have hN : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by simpa [cnormSq] using cnormSq_ne_zero hu
  simp only [lineReflect, cscale, cmul, cconj, cnormSq]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Rotation is two reflections.** The composite of the
reflections across two lines through the origin is the rotation whose turn is the Gaussian-rational
quotient `v ū`. Exact over `ℚ`, with no angle and no square root. -/
theorem lineReflect_comp_eq_rotBy {u v : ℚ × ℚ} (hu : u ≠ 0) (hv : v ≠ 0) (z : ℚ × ℚ) :
    lineReflect v (lineReflect u z) = rotBy (cmul v (cconj u)) z := by
  have hNu : cnormSq u ≠ 0 := cnormSq_ne_zero hu
  have hNv : cnormSq v ≠ 0 := cnormSq_ne_zero hv
  have hturn : cnormSq (cmul v (cconj u)) = cnormSq v * cnormSq u := by
    rw [cnormSq_cmul, cnormSq_cconj]
  have hrot : rotBy (cmul v (cconj u)) z
      = cscale (1 / (cnormSq v * cnormSq u))
        (cmul (cmul (cmul v (cconj u)) (cmul v (cconj u))) z) := by
    unfold rotBy; rw [hturn]
  rw [hrot]
  simp only [lineReflect, cscale, cmul, cconj, Prod.ext_iff]
  constructor <;> (field_simp; ring)

/-- [proved-derived; formal-checked] Rotations compose by multiplying their turns. -/
theorem rotBy_comp {w w' : ℚ × ℚ} (hw : w ≠ 0) (hw' : w' ≠ 0) (z : ℚ × ℚ) :
    rotBy w (rotBy w' z) = rotBy (cmul w w') z := by
  have hNw : cnormSq w ≠ 0 := cnormSq_ne_zero hw
  have hNw' : cnormSq w' ≠ 0 := cnormSq_ne_zero hw'
  have hrot : rotBy (cmul w w') z
      = cscale (1 / (cnormSq w * cnormSq w')) (cmul (cmul (cmul w w') (cmul w w')) z) := by
    unfold rotBy; rw [cnormSq_cmul]
  rw [hrot]
  simp only [rotBy, cscale, cmul, Prod.ext_iff]
  constructor <;> (field_simp; ring)

theorem rotBy_one (w : ℚ × ℚ) :
    rotBy w (1, 0) = ((w.1 ^ 2 - w.2 ^ 2) / cnormSq w, (2 * w.1 * w.2) / cnormSq w) := by
  simp only [rotBy, cscale, cmul, Prod.mk.injEq]
  constructor <;> (rw [div_eq_mul_inv, div_eq_mul_inv]; ring)

/-- [proved-derived; formal-checked] **A rotation is the identity exactly when its turn is real.**
One rational equation decides it: no angle, no transcendental comparison. -/
theorem rotBy_eq_id_iff {w : ℚ × ℚ} (hw : w ≠ 0) : (∀ z, rotBy w z = z) ↔ w.2 = 0 := by
  have hN : cnormSq w ≠ 0 := cnormSq_ne_zero hw
  constructor
  · intro h
    have h1 := h (1, 0)
    rw [rotBy_one, Prod.mk.injEq] at h1
    obtain ⟨hre, _⟩ := h1
    rw [div_eq_iff hN, one_mul, cnormSq] at hre
    have h2 : w.2 ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp h2
  · intro h z
    have hw1 : w.1 ≠ 0 := by
      intro hc
      exact hw (Prod.ext_iff.mpr ⟨by simpa using hc, by simpa using h⟩)
    simp only [rotBy, cscale, cmul, cnormSq, h, Prod.ext_iff]
    constructor <;> (field_simp; try ring)

/-! ### Kawasaki's law without angles -/

/-- [definition] **The accumulated turn of a crease pattern.** The creases of a degree-`2n` vertex
are listed in cyclic order as `n` consecutive pairs `(d_{2k−1}, d_{2k})`; the turn is the product
of the Gaussian-rational quotients `d_{2k} d̄_{2k−1}`. -/
def kawasakiTurn : List ((ℚ × ℚ) × (ℚ × ℚ)) → ℚ × ℚ
  | [] => (1, 0)
  | (u, v) :: rest => cmul (cmul v (cconj u)) (kawasakiTurn rest)

/-- [definition] The composite of the crease reflections, in the order the creases are listed. -/
def reflectPairs : List ((ℚ × ℚ) × (ℚ × ℚ)) → (ℚ × ℚ) → ℚ × ℚ
  | [], z => z
  | (u, v) :: rest, z => lineReflect v (lineReflect u (reflectPairs rest z))

/-- [definition] Every crease direction of a listed pattern is nonzero. -/
def CreasesNonzero (ps : List ((ℚ × ℚ) × (ℚ × ℚ))) : Prop :=
  ∀ p ∈ ps, p.1 ≠ 0 ∧ p.2 ≠ 0

theorem kawasakiTurn_ne_zero : ∀ (ps : List ((ℚ × ℚ) × (ℚ × ℚ))), CreasesNonzero ps →
    kawasakiTurn ps ≠ 0 := by
  intro ps
  induction ps with
  | nil =>
    intro _
    simp [kawasakiTurn, Prod.ext_iff]
  | cons p rest ih =>
    obtain ⟨u, v⟩ := p
    intro hp
    have hu : u ≠ 0 := (hp (u, v) (by simp)).1
    have hv : v ≠ 0 := (hp (u, v) (by simp)).2
    have hrest : CreasesNonzero rest := fun q hq => hp q (by simp [hq])
    rw [kawasakiTurn]
    exact cmul_ne_zero (cmul_ne_zero hv (cconj_ne_zero hu)) (ih hrest)

/-- [proved-derived; formal-checked] **The composite of the crease reflections is one rotation**,
whose turn is the accumulated Gaussian-rational product. -/
theorem reflectPairs_eq_rotBy : ∀ (ps : List ((ℚ × ℚ) × (ℚ × ℚ))), CreasesNonzero ps →
    ∀ z, reflectPairs ps z = rotBy (kawasakiTurn ps) z := by
  intro ps
  induction ps with
  | nil =>
    intro _ z
    simp only [reflectPairs, kawasakiTurn, rotBy, cscale, cmul, cnormSq, Prod.ext_iff]
    constructor <;> norm_num
  | cons p rest ih =>
    obtain ⟨u, v⟩ := p
    intro hp z
    have hu : u ≠ 0 := (hp (u, v) (by simp)).1
    have hv : v ≠ 0 := (hp (u, v) (by simp)).2
    have hrest : CreasesNonzero rest := fun q hq => hp q (by simp [hq])
    have hprev := kawasakiTurn_ne_zero rest hrest
    have hstep : cmul v (cconj u) ≠ 0 := cmul_ne_zero hv (cconj_ne_zero hu)
    rw [reflectPairs, ih hrest z, lineReflect_comp_eq_rotBy hu hv, rotBy_comp hstep hprev,
      kawasakiTurn]

/-- [proved-derived; formal-checked] **Kawasaki's condition, exactly over `ℚ` and with no angle.**
The ordered product of the `2n` crease reflections at a vertex is the identity exactly when the
accumulated turn has zero imaginary part.

[proved-standard; cited] The classical reading: the turn's imaginary part vanishes exactly when
twice the sum of the odd sectors is a multiple of `π`, which with the sectors summing to `2π` is
`α₁ − α₂ + ⋯ − α_{2n} = 0` — Kawasaki's theorem (T. Kawasaki, *On the relation between mountain
creases and valley creases of a flat origami*, 1989; Hull, *On the mathematics of flat origamis*,
1994). Only the algebraic form is proved here; the passage to sector angles is the cited classical
statement and leaves this chart. -/
theorem kawasaki_iff {ps : List ((ℚ × ℚ) × (ℚ × ℚ))} (hp : CreasesNonzero ps) :
    (∀ z, reflectPairs ps z = z) ↔ (kawasakiTurn ps).2 = 0 := by
  have hturn := kawasakiTurn_ne_zero ps hp
  constructor
  · intro h
    refine (rotBy_eq_id_iff hturn).mp fun z => ?_
    rw [← reflectPairs_eq_rotBy ps hp z]
    exact h z
  · intro h z
    rw [reflectPairs_eq_rotBy ps hp z]
    exact (rotBy_eq_id_iff hturn).mpr h z

/-- [definition] The degree-four vertex whose four creases are the coordinate rays. -/
def plusVertex : List ((ℚ × ℚ) × (ℚ × ℚ)) := [((1, 0), (0, 1)), ((-1, 0), (0, -1))]

/-- [definition] The same vertex with one ray moved to `(1, −1)`: the sectors become
`90, 90, 135, 45` and the alternating sum is `90`. -/
def skewVertex : List ((ℚ × ℚ) × (ℚ × ℚ)) := [((1, 0), (0, 1)), ((-1, 0), (1, -1))]

theorem plusVertex_nonzero : CreasesNonzero plusVertex := by
  intro p hp
  simp only [plusVertex, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    exact ⟨by simp [Prod.ext_iff], by simp [Prod.ext_iff]⟩

theorem skewVertex_nonzero : CreasesNonzero skewVertex := by
  intro p hp
  simp only [skewVertex, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    exact ⟨by simp [Prod.ext_iff], by simp [Prod.ext_iff]⟩

/-- [proved-derived; formal-checked] **An exact flat-foldable degree-four vertex.** -/
theorem plusVertexIsFlatFoldable : ∀ z, reflectPairs plusVertex z = z :=
  (kawasaki_iff plusVertex_nonzero).mpr (by norm_num [kawasakiTurn, plusVertex, cmul, cconj])

/-- [counterexample; formal-checked] **And one that is not.** -/
theorem skewVertexIsNotFlatFoldable : ¬ ∀ z, reflectPairs skewVertex z = z := by
  intro h
  have hz := (kawasaki_iff skewVertex_nonzero).mp h
  norm_num [kawasakiTurn, skewVertex, cmul, cconj] at hz

/-! ### Maekawa's law as an integer count -/

/-- [definition] The mountains of a mountain/valley assignment: `true` is a mountain. -/
def mountains {n : ℕ} (a : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => a i = true).card

/-- [definition] The valleys are the rest. -/
def valleys {n : ℕ} (a : Fin n → Bool) : ℕ := n - mountains a

theorem mountains_le {n : ℕ} (a : Fin n → Bool) : mountains a ≤ n := by
  simpa [mountains] using Finset.card_filter_le (Finset.univ : Finset (Fin n)) fun i => a i = true

/-- [definition] **Maekawa's balance**: `M − V = ±2`. -/
def MaekawaBalanced {n : ℕ} (a : Fin (2 * n) → Bool) : Prop :=
  (mountains a : ℤ) - valleys a = 2 ∨ (mountains a : ℤ) - valleys a = -2

/-- [proved-derived; formal-checked] **Maekawa's law is an integer count law.** At a degree-`2n`
vertex, `M − V = ±2` holds exactly when `M = n + 1` or `M = n − 1`, because `M + V = 2n`.

[proved-standard; cited] That a flat-foldable single vertex's assignment is balanced is Maekawa's
theorem (Hull, *On the mathematics of flat origamis*, 1994, Theorem 3.1); the folded-state model it
needs is outside this chart and is cited, not reproved. What is proved here is the count law
itself, which is what the Rust owner checks on an assignment. -/
theorem maekawa_iff_mountain_count {n : ℕ} (hn : 1 ≤ n) (a : Fin (2 * n) → Bool) :
    MaekawaBalanced a ↔ mountains a = n + 1 ∨ mountains a = n - 1 := by
  have hle : mountains a ≤ 2 * n := mountains_le a
  simp only [MaekawaBalanced, valleys]
  omega

/-- [proved-derived; formal-checked] The degree-four case, decided over all sixteen assignments:
exactly eight are balanced, and they are exactly the ones with three mountains or one. -/
theorem maekawa_degree_four :
    (Finset.univ.filter fun a : Fin 4 → Bool => mountains a = 3 ∨ mountains a = 1).card = 8 := by
  decide

/-! ## 5. A shear is not a fold, and inversion is the third of the triple -/

/-- [definition] The plane shear `(x, y) ↦ (x + k y, y)`. -/
def shear (k : ℚ) (z : ℚ × ℚ) : ℚ × ℚ := (z.1 + k * z.2, z.2)

/-- [definition] The plane's squared distance in the Gaussian chart. -/
def planeDistSq (z w : ℚ × ℚ) : ℚ := (z.1 - w.1) ^ 2 + (z.2 - w.2) ^ 2

/-- [proved-derived; formal-checked] **A shear changes a squared distance in every neighbourhood of
every point and at every scale.** A fold is an exact isometry on each side of its crease; a shear is
an isometry on no nonempty open set at all. That is the precise sense in which the shear deforms the
lattice rather than folding it. -/
theorem shear_changes_a_squared_distance_at_every_point_and_scale
    {k : ℚ} (hk : k ≠ 0) (p : ℚ × ℚ) {t : ℚ} (ht : t ≠ 0) :
    planeDistSq (shear k p) (shear k (p.1, p.2 + t)) ≠ planeDistSq p (p.1, p.2 + t) := by
  simp only [planeDistSq, shear]
  intro h
  have hk2 : k ^ 2 * t ^ 2 = 0 := by linear_combination h
  rcases mul_eq_zero.mp hk2 with h' | h'
  · exact hk (sq_eq_zero_iff.mp h')
  · exact ht (sq_eq_zero_iff.mp h')

/-- [proved-derived; formal-checked] **No map preserving every squared distance is a nonzero
shear.** Reflections preserve every squared distance and so does every composition of them, so a
shear is not a composition of reflections. -/
theorem no_isometry_is_a_shear {k : ℚ} (hk : k ≠ 0) (f : ℚ × ℚ → ℚ × ℚ)
    (hf : ∀ z w, planeDistSq (f z) (f w) = planeDistSq z w) : f ≠ shear k := by
  intro hc
  have h := hf (0, 0) (0, 1)
  rw [hc] at h
  simp only [planeDistSq, shear] at h
  have hk2 : k ^ 2 = 0 := by linear_combination h
  exact hk (sq_eq_zero_iff.mp hk2)

/-- [definition] **Inversion in the sphere of radius `r`**: `x ↦ r² x / ⟨x,x⟩`. -/
def inversion (r : ℚ) (x : Fin d → ℚ) : Fin d → ℚ := fun a => r ^ 2 * x a / dot x x

theorem distSq_expand (x y : Fin d → ℚ) : distSq x y = dot x x - 2 * dot x y + dot y y := by
  have hrw : (fun a => x a - y a) = (fun a => (1 : ℚ) * x a + (-1 : ℚ) * y a) := by
    funext a; ring
  simp only [distSq, hrw, dot_pair]
  ring

/-- [proved-derived; formal-checked] **The exact inversion distance formula.** Everything is
rational; no root is taken. -/
theorem inversion_distSq {r : ℚ} {x y : Fin d → ℚ} (hx : dot x x ≠ 0) (hy : dot y y ≠ 0) :
    distSq (inversion r x) (inversion r y)
      = r ^ 4 * distSq x y / (dot x x * dot y y) := by
  have hform : (fun a => inversion r x a - inversion r y a)
      = (fun a => (r ^ 2 / dot x x) * x a + (-(r ^ 2 / dot y y)) * y a) := by
    funext a
    simp only [inversion]
    field_simp
    ring
  have hleft : distSq (inversion r x) (inversion r y)
      = (r ^ 2 / dot x x) * (r ^ 2 / dot x x) * dot x x
        + 2 * ((r ^ 2 / dot x x) * (-(r ^ 2 / dot y y))) * dot x y
        + (-(r ^ 2 / dot y y)) * (-(r ^ 2 / dot y y)) * dot y y := by
    simp only [distSq]
    rw [hform, dot_pair]
  rw [hleft, distSq_expand]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Inversion preserves the cross ratio.** Every `r⁴` and every
`⟨x,x⟩` cancels, so the squared cross ratio of four points is exactly invariant — over `ℚ`, with no
root and no conformal machinery.

[proved-standard; cited] That inversion in a sphere *is* a reflection in a hyperplane of the
conformal (Lorentz) model, so that Brandon's "division, shear, inversion" triple is literally
reflection in three different ambient geometries, is the classical statement and is cited rather
than formalized here. -/
theorem inversion_preserves_cross_ratio {r : ℚ} {w x y z : Fin d → ℚ}
    (hw : dot w w ≠ 0) (hx : dot x x ≠ 0) (hy : dot y y ≠ 0) (hz : dot z z ≠ 0) (hr : r ≠ 0)
    (hwy : distSq w y ≠ 0) (hxz : distSq x z ≠ 0) :
    distSq (inversion r w) (inversion r x) * distSq (inversion r y) (inversion r z)
        * (distSq w y * distSq x z)
      = distSq w x * distSq y z
        * (distSq (inversion r w) (inversion r y) * distSq (inversion r x) (inversion r z)) := by
  rw [inversion_distSq hw hx, inversion_distSq hy hz, inversion_distSq hw hy,
    inversion_distSq hx hz]
  have hr4 : r ^ 4 ≠ 0 := pow_ne_zero 4 hr
  field_simp

/-! ## 6. A fold preserves homology; a cut does not -/

/-- [definition] A two-dimensional chain complex over `ℚ` with its two boundary matrices. -/
structure ChainTwo (v e f : ℕ) where
  /-- `∂₁`, from edges to vertices. -/
  d1 : Matrix (Fin v) (Fin e) ℚ
  /-- `∂₂`, from faces to edges. -/
  d2 : Matrix (Fin e) (Fin f) ℚ
  /-- `∂₁ ∂₂ = 0`. -/
  boundary_squared : d1 * d2 = 0

namespace ChainTwo

variable {v e f : ℕ}

/-- [definition] `b₀ = #cells₀ − rank ∂₁`. -/
def betti0 (K : ChainTwo v e f) : ℕ := v - K.d1.rank
/-- [definition] `b₁ = #cells₁ − rank ∂₁ − rank ∂₂`. -/
def betti1 (K : ChainTwo v e f) : ℕ := e - K.d1.rank - K.d2.rank
/-- [definition] `b₂ = #cells₂ − rank ∂₂`. -/
def betti2 (K : ChainTwo v e f) : ℕ := f - K.d2.rank

/-- [definition] A **relabelling of cells**: bijections of the vertex, edge and face addresses
carrying one complex to another. This is a fold whose crease lies along the skeleton, read on the
incidence: the fold is an isometry on each cell and a bijection on cells. -/
structure Relabelling (K L : ChainTwo v e f) where
  /-- The vertex relabelling. -/
  onVertices : Fin v ≃ Fin v
  /-- The edge relabelling. -/
  onEdges : Fin e ≃ Fin e
  /-- The face relabelling. -/
  onFaces : Fin f ≃ Fin f
  /-- It carries `∂₁`. -/
  carries_one : L.d1 = K.d1.submatrix onVertices onEdges
  /-- It carries `∂₂`. -/
  carries_two : L.d2 = K.d2.submatrix onEdges onFaces

/-- [proved-derived; formal-checked] **A fold does not move a Betti number.** A relabelling of
cells carrying both boundaries leaves every rank unchanged, through `Matrix.rank_submatrix`, so
every Betti number is unchanged.

[definition] This is the **automorphism** statement, and it is stated as such. The *quotient*
statement — the fold that carries one half of a sheet onto the other — is `Crease.fold_fibre`
above, whose fibre has two elements and whose residual is one bit. A **cut** is neither: it removes
or duplicates cells, so no such relabelling exists, and the Rust owner exhibits the exact instances
(an annulus cut to a disc, `b₁ : 1 ↦ 0`; a disc cut in two, `b₀ : 1 ↦ 2`) with the existing
Smith-normal-form owner. -/
theorem fold_preserves_betti {K L : ChainTwo v e f} (φ : Relabelling K L) :
    L.betti0 = K.betti0 ∧ L.betti1 = K.betti1 ∧ L.betti2 = K.betti2 := by
  have h1 : L.d1.rank = K.d1.rank := by
    rw [φ.carries_one]; exact Matrix.rank_submatrix _ _ _
  have h2 : L.d2.rank = K.d2.rank := by
    rw [φ.carries_two]; exact Matrix.rank_submatrix _ _ _
  exact ⟨by simp only [betti0, h1], by simp only [betti1, h1, h2], by simp only [betti2, h2]⟩

/-- [definition] The identity relabelling: a complex is a fold of itself. This is the constructed
instance, so that `Relabelling` is not a hypothesis bundle nothing inhabits. -/
def Relabelling.refl (K : ChainTwo v e f) : Relabelling K K where
  onVertices := Equiv.refl _
  onEdges := Equiv.refl _
  onFaces := Equiv.refl _
  carries_one := by simp
  carries_two := by simp

/-- [counterexample; formal-checked] **A cut is not a fold.** Two complexes whose boundary ranks
differ admit no relabelling at all, so nothing carrying the name "fold" can relate them. This is
the constructed *non*-instance, and it is exactly why the Rust owner's annulus-to-disc and
disc-in-two cuts are cuts rather than folds. -/
theorem no_relabelling_when_the_rank_moves {K L : ChainTwo v e f} (h : L.d1.rank ≠ K.d1.rank) :
    IsEmpty (Relabelling K L) := by
  constructor
  intro φ
  exact h (by rw [φ.carries_one]; exact Matrix.rank_submatrix _ _ _)

end ChainTwo

/-- [proved-derived; formal-checked] **A fold preserves the intrinsic metric.** An edge whose two
endpoints lie on one closed side of the crease keeps its exact squared length, so the edge-length
metric of the complex — what the paper measures along itself — is unchanged. -/
theorem fold_preserves_intrinsic_length (H : Crease d) {x y : Fin d → ℚ}
    (h : (0 ≤ H.side x ∧ 0 ≤ H.side y) ∨ (H.side x < 0 ∧ H.side y < 0)) :
    distSq (H.fold x) (H.fold y) = distSq x y :=
  H.fold_distSq_same_side h

/-! ## 7. Unfolding at a tolerance: the fold catastrophe -/

/-- [definition] The fold catastrophe's normal form, `V_a(x) = x³/3 − a x`. -/
def foldPotential (a x : ℝ) : ℝ := x ^ 3 / 3 - a * x

/-- [definition] Its derivative, `V'_a(x) = x² − a`. -/
def foldForce (a x : ℝ) : ℝ := x ^ 2 - a

/-- [definition] Its second derivative, `V''_a(x) = 2x`. -/
def foldStiffness (x : ℝ) : ℝ := 2 * x

/-- [proved-derived; formal-checked] **An equilibrium exists exactly when `a ≥ 0`.** -/
theorem foldEquilibria_iff (a : ℝ) : (∃ x : ℝ, foldForce a x = 0) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨x, hx⟩
    have hax : a = x ^ 2 := by simp only [foldForce] at hx; linarith
    rw [hax]; positivity
  · intro ha
    exact ⟨Real.sqrt a, by simp [foldForce, Real.sq_sqrt ha]⟩

/-- [counterexample; formal-checked] **Below the threshold there is none.** -/
theorem no_equilibrium_of_neg {a : ℝ} (ha : a < 0) : ¬ ∃ x : ℝ, foldForce a x = 0 := by
  rw [foldEquilibria_iff]; linarith

/-- [proved-derived; formal-checked] **Above it there are exactly two**, and they merge at `a = 0`
(`equilibrium_unique_at_zero`). -/
theorem foldEquilibria_two_of_pos {a : ℝ} (ha : 0 < a) :
    foldForce a (Real.sqrt a) = 0 ∧ foldForce a (-Real.sqrt a) = 0
      ∧ Real.sqrt a ≠ -Real.sqrt a
      ∧ ∀ z : ℝ, foldForce a z = 0 → z = Real.sqrt a ∨ z = -Real.sqrt a := by
  have hs : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hpos : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  refine ⟨by simp [foldForce, hs], by simp [foldForce, hs], by intro hc; linarith [hc ▸ hpos], ?_⟩
  intro z hz
  have hfac : (z - Real.sqrt a) * (z + Real.sqrt a) = 0 := by
    simp only [foldForce] at hz
    nlinarith [hz, hs]
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

theorem equilibrium_unique_at_zero : ∀ z : ℝ, foldForce 0 z = 0 → z = 0 := by
  intro z hz
  simp only [foldForce, sub_zero] at hz
  exact sq_eq_zero_iff.mp hz

/-- [proved-derived; formal-checked] **The upper root is the held state.** `V'' > 0` there. -/
theorem positiveRoot_is_stable {a : ℝ} (ha : 0 < a) : 0 < foldStiffness (Real.sqrt a) := by
  simp only [foldStiffness]
  linarith [Real.sqrt_pos.mpr ha]

/-- [proved-derived; formal-checked] **The lower root is the barrier.** -/
theorem negativeRoot_is_unstable {a : ℝ} (ha : 0 < a) : foldStiffness (-Real.sqrt a) < 0 := by
  simp only [foldStiffness]
  linarith [Real.sqrt_pos.mpr ha]

/-! ### The declared crease model -/

/-- [definition] **A declared constitutive model of one crease.** The hinge's restoring torque is
modelled by the polynomial `κ (u² − u₀²)` in the opening coordinate `u`, and gravity enters as a
constant load — a torque, in the same units — so the potential is
`V(u) = κ (u³/3 − u₀² u) + load · u`.

[definition] Its approximations, stated affirmatively: the hinge torque is a declared quadratic in
the opening coordinate — two terms of an expansion about the flat state, not a trigonometric law;
the panels are rigid and the crease's finite thickness and its parabolic curvature are not
modelled; gravity acts as one constant torque `m g ℓ` with `ℓ` a declared lever arm; the reading is
quasi-static, so no inertia and no rate dependence enter, and stability is read from the sign of
`V''` alone. The Rust owner carries the same model with typed units. -/
def creaseTorque (κ u₀ load u : ℝ) : ℝ := κ * (u ^ 2 - u₀ ^ 2) + load

/-- [proved-derived; formal-checked] **The held state disappears at an exact threshold.** With a
positive hinge stiffness, an equilibrium of the loaded crease exists exactly when the gravity load
is at most `κ u₀²`; above it the fold opens and there is no equilibrium at all. That threshold is
the fold catastrophe's `a = 0` in the model's own coordinates, and it is exact. -/
theorem held_equilibrium_iff_load_le_threshold {κ u₀ load : ℝ} (hκ : 0 < κ) :
    (∃ u : ℝ, creaseTorque κ u₀ load u = 0) ↔ load ≤ κ * u₀ ^ 2 := by
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hrel : ∀ u : ℝ, foldForce (u₀ ^ 2 - load / κ) u = creaseTorque κ u₀ load u / κ := by
    intro u
    simp only [foldForce, creaseTorque]
    field_simp
    ring
  have hreduce : ∀ u : ℝ, creaseTorque κ u₀ load u = 0 ↔ foldForce (u₀ ^ 2 - load / κ) u = 0 := by
    intro u
    rw [hrel u, div_eq_zero_iff]
    simp [hκ0]
  constructor
  · rintro ⟨u, hu⟩
    have h0 : 0 ≤ u₀ ^ 2 - load / κ := (foldEquilibria_iff _).mp ⟨u, (hreduce u).mp hu⟩
    have hdiv : load / κ ≤ u₀ ^ 2 := by linarith
    rw [div_le_iff₀ hκ] at hdiv
    linarith
  · intro h
    have h0 : 0 ≤ u₀ ^ 2 - load / κ := by
      rw [sub_nonneg, div_le_iff₀ hκ]; linarith
    obtain ⟨u, hu⟩ := (foldEquilibria_iff (u₀ ^ 2 - load / κ)).mpr h0
    exact ⟨u, (hreduce u).mpr hu⟩

/-! ### Brandon's lever arm: the offset grows with distance from the crease -/

/-- [definition] The rational parametrization of a plane rotation, `t = tan(θ/2)`: its cosine is
exactly rational. -/
def rotCos (t : ℚ) : ℚ := (1 - t ^ 2) / (1 + t ^ 2)

/-- [definition] The sine of the same rotation, also exactly rational. -/
def rotSin (t : ℚ) : ℚ := 2 * t / (1 + t ^ 2)

theorem one_add_sq_ne_zero (t : ℚ) : (1 : ℚ) + t ^ 2 ≠ 0 := by positivity

/-- [proved-derived; formal-checked] **The rational rotation really is a rotation**, exactly over
`ℚ`: no angle, no transcendental function, no square root. -/
theorem rationalRotation_orthogonal (t : ℚ) : rotCos t ^ 2 + rotSin t ^ 2 = 1 := by
  have h := one_add_sq_ne_zero t
  simp only [rotCos, rotSin]
  field_simp
  ring

/-- [definition] The squared displacement of a point at perpendicular distance `ℓ` from the crease
when the crease opens by the rotation parametrized by `t`. -/
def displacementSq (ℓ t : ℚ) : ℚ := (rotCos t * ℓ - ℓ) ^ 2 + (rotSin t * ℓ) ^ 2

/-- [proved-derived; formal-checked] The closed form: `4 ℓ² t² / (1 + t²)`. -/
theorem displacementSq_eq (ℓ t : ℚ) : displacementSq ℓ t = 4 * ℓ ^ 2 * t ^ 2 / (1 + t ^ 2) := by
  have h := one_add_sq_ne_zero t
  simp only [displacementSq, rotCos, rotSin]
  field_simp
  ring

/-- [proved-derived; formal-checked] **Brandon's lever arm, exactly.** The squared offset scales as
the square of the distance from the crease, so the offset itself grows *linearly* with that
distance: a point twice as far from the crease moves twice as far for the same opening. Nothing
here is approximate and nothing is a small-angle expansion. -/
theorem displacementSq_scales_with_lever (c ℓ t : ℚ) :
    displacementSq (c * ℓ) t = c ^ 2 * displacementSq ℓ t := by
  have h := one_add_sq_ne_zero t
  simp only [displacementSq_eq]
  field_simp

/-- [proved-derived; formal-checked] The offset is zero exactly when the crease has not opened. -/
theorem displacementSq_eq_zero_iff {ℓ t : ℚ} (hℓ : ℓ ≠ 0) : displacementSq ℓ t = 0 ↔ t = 0 := by
  have h := one_add_sq_ne_zero t
  rw [displacementSq_eq, div_eq_zero_iff]
  constructor
  · rintro (hc | hc)
    · rcases mul_eq_zero.mp hc with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · norm_num at h''
        · exact absurd (sq_eq_zero_iff.mp h'') hℓ
      · exact sq_eq_zero_iff.mp h'
    · exact absurd hc h
  · rintro rfl; left; ring

/-! ## 8. The protein backbone as rigid origami of a one-dimensional linkage -/

/-- [definition] **The bars a backbone window of `r` residues carries** in the bar-joint model with
fixed bond lengths, fixed bond angles and a planar `ω`:

* `2r + (r − 1)` bonds — `N–CA` and `CA–C` inside each residue, and `C–N` between them;
* `r + 2(r − 1)` angle bars — `N–C` at each `CA`, `CA–N` at each `C`, `C–CA` at each `N`;
* `r − 1` planarity bars — `CA–CA` across each peptide unit, which is exactly the declaration
  that `ω` is planar.

The free dihedrals left over are `φ` and `ψ`. -/
def backboneBarCount (r : ℕ) : ℤ := 7 * r - 4

/-- [definition] Three atoms per residue, three coordinates each. -/
def backboneCoordinateCount (r : ℕ) : ℤ := 9 * r

/-- [proved-derived; formal-checked] **The exact prediction the Rust owner measures against the
deposited structures**: a free backbone window of `r` residues has `2(r − 1)` internal degrees of
freedom — the `φ`/`ψ` dihedrals, with the two terminal flaps absorbed because a rotation of a
terminal atom about the axis of its two bars differs from the corresponding dihedral by a rigid
motion of the whole window. This holds when the bar system has full rank at the presented
configuration, which the Rust owner measures rather than assumes. -/
theorem backbone_internal_dof (r : ℕ) :
    backboneCoordinateCount r - backboneBarCount r - 6 = 2 * (r : ℤ) - 2 := by
  simp only [backboneCoordinateCount, backboneBarCount]
  ring

/-! ### The dihedral without an angle -/

/-- [definition] The cross product on `ℚ³`. -/
def cross (u v : Fin 3 → ℚ) : Fin 3 → ℚ := fun i =>
  if i = 0 then u 1 * v 2 - u 2 * v 1
  else if i = 1 then u 2 * v 0 - u 0 * v 2
  else u 0 * v 1 - u 1 * v 0

@[simp] theorem cross_apply_zero (u v : Fin 3 → ℚ) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 := by
  simp [cross]

@[simp] theorem cross_apply_one (u v : Fin 3 → ℚ) :
    cross u v 1 = u 2 * v 0 - u 0 * v 2 := by
  norm_num [cross]

@[simp] theorem cross_apply_two (u v : Fin 3 → ℚ) :
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by
  have h0 : (2 : Fin 3) ≠ 0 := by decide
  have h1 : (2 : Fin 3) ≠ 1 := by decide
  simp [cross, h0, h1]

theorem cross_dot_left (u v : Fin 3 → ℚ) : dot u (cross u v) = 0 := by
  simp only [dot, Fin.sum_univ_three, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

theorem cross_dot_right (u v : Fin 3 → ℚ) : dot v (cross u v) = 0 := by
  simp only [dot, Fin.sum_univ_three, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- [proved-derived; formal-checked] **Lagrange's identity on `ℚ³`**, exact. -/
theorem lagrange_identity (u v : Fin 3 → ℚ) :
    dot u u * dot v v - dot u v ^ 2 = dot (cross u v) (cross u v) := by
  simp only [dot, Fin.sum_univ_three, cross_apply_zero, cross_apply_one, cross_apply_two]
  ring

/-- [definition] **The exact squared cosine of a dihedral.** A dihedral angle is not rational and
is never taken: what is reported is `cos²θ = ⟨n₁,n₂⟩² / (⟨n₁,n₁⟩⟨n₂,n₂⟩)`, an exact rational, with
the signs of `cos θ` and `sin θ` carried beside it. -/
def dihedralCosSq (n₁ n₂ : Fin 3 → ℚ) : ℚ := dot n₁ n₂ ^ 2 / (dot n₁ n₁ * dot n₂ n₂)

theorem dihedralCosSq_nonneg (n₁ n₂ : Fin 3 → ℚ) : 0 ≤ dihedralCosSq n₁ n₂ :=
  div_nonneg (sq_nonneg _) (mul_nonneg (dot_self_nonneg _) (dot_self_nonneg _))

/-- [proved-derived; formal-checked] It is a squared cosine: at most one, exactly, by Lagrange. -/
theorem dihedralCosSq_le_one {n₁ n₂ : Fin 3 → ℚ} (h₁ : dot n₁ n₁ ≠ 0) (h₂ : dot n₂ n₂ ≠ 0) :
    dihedralCosSq n₁ n₂ ≤ 1 := by
  have hp₁ : 0 < dot n₁ n₁ := lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm h₁)
  have hp₂ : 0 < dot n₂ n₂ := lt_of_le_of_ne (dot_self_nonneg _) (Ne.symm h₂)
  rw [dihedralCosSq, div_le_one (by positivity)]
  have hlag := lagrange_identity n₁ n₂
  have hcross : 0 ≤ dot (cross n₁ n₂) (cross n₁ n₂) := dot_self_nonneg _
  linarith

/-- [proved-derived; formal-checked] **A pivot move is a rotation about a chain axis**, which is
two reflections in hyperplanes containing that axis. The composite preserves every squared distance,
so every bond length in the moved part is preserved exactly. -/
theorem pivot_preserves_squared_lengths (H₁ H₂ : Crease d) (x y : Fin d → ℚ) :
    distSq (H₂.reflect (H₁.reflect x)) (H₂.reflect (H₁.reflect y)) = distSq x y := by
  rw [H₂.reflect_distSq, H₁.reflect_distSq]

/-- [proved-derived; formal-checked] An atom on both creases is fixed by the pivot, which is why a
bond from the moved tail to the fixed head keeps its length too. -/
theorem pivot_fixes_the_axis {H₁ H₂ : Crease d} {x : Fin d → ℚ}
    (h₁ : H₁.side x = 0) (h₂ : H₂.side x = 0) : H₂.reflect (H₁.reflect x) = x := by
  rw [H₁.reflect_eq_self_of_side_zero h₁, H₂.reflect_eq_self_of_side_zero h₂]

section Audit

#print axioms dot_self_eq_zero_iff
#print axioms dot_pair
#print axioms dot_shift
#print axioms Crease.side_reflect
#print axioms Crease.reflect_involutive
#print axioms Crease.reflect_eq_self_of_side_zero
#print axioms Crease.linReflect_dot
#print axioms Crease.linReflect_fixes_tangential
#print axioms Crease.linReflect_normal
#print axioms Crease.reflect_distSq
#print axioms Crease.fold_distSq_same_side
#print axioms Crease.fold_distSq_opposite_side
#print axioms Crease.fold_brings_the_two_sides_together
#print axioms Crease.fold_mem_positive_side
#print axioms Crease.fold_eq_self_iff
#print axioms Crease.fold_fibre
#print axioms Crease.reopen_apply_fold
#print axioms Crease.foldTransition
#print axioms Crease.side_segment
#print axioms Crease.crossing_side_eq_zero
#print axioms Crease.fold_segment_before
#print axioms Crease.fold_segment_after
#print axioms Crease.bounce_direction
#print axioms sideWord_card
#print axioms k_folds_branch_dyadically
#print axioms residual_injective_on_fibre
#print axioms cnormSq_cmul
#print axioms cnormSq_eq_zero_iff
#print axioms lineReflect_involutive
#print axioms lineReflect_cscale
#print axioms lineReflect_fixes_direction
#print axioms lineReflect_cnormSq
#print axioms lineReflect_comp_eq_rotBy
#print axioms rotBy_comp
#print axioms rotBy_eq_id_iff
#print axioms kawasakiTurn_ne_zero
#print axioms reflectPairs_eq_rotBy
#print axioms kawasaki_iff
#print axioms plusVertexIsFlatFoldable
#print axioms skewVertexIsNotFlatFoldable
#print axioms maekawa_iff_mountain_count
#print axioms maekawa_degree_four
#print axioms shear_changes_a_squared_distance_at_every_point_and_scale
#print axioms no_isometry_is_a_shear
#print axioms inversion_distSq
#print axioms inversion_preserves_cross_ratio
#print axioms ChainTwo.fold_preserves_betti
#print axioms ChainTwo.Relabelling.refl
#print axioms ChainTwo.no_relabelling_when_the_rank_moves
#print axioms fold_preserves_intrinsic_length
#print axioms foldEquilibria_iff
#print axioms no_equilibrium_of_neg
#print axioms foldEquilibria_two_of_pos
#print axioms equilibrium_unique_at_zero
#print axioms positiveRoot_is_stable
#print axioms negativeRoot_is_unstable
#print axioms held_equilibrium_iff_load_le_threshold
#print axioms rationalRotation_orthogonal
#print axioms displacementSq_eq
#print axioms displacementSq_scales_with_lever
#print axioms displacementSq_eq_zero_iff
#print axioms backbone_internal_dof
#print axioms cross_dot_left
#print axioms cross_dot_right
#print axioms lagrange_identity
#print axioms dihedralCosSq_nonneg
#print axioms dihedralCosSq_le_one
#print axioms pivot_preserves_squared_lengths
#print axioms pivot_fixes_the_axis

end Audit

end Holonics.Transport.Fold

import Holonics.Geometry.Motion
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Order is torsion: the carry a loop of moves leaves

[proved-derived; formal-checked] October 22
([record](../../../research/records/2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md)).
The motion owner (`Geometry/Motion`) states the move `x ↦ M x + b`, its pivot `(1 − M) O = b` and
the composition law. This module reads the failure of two moves to commute as the **carry** they
leave around their loop. That is the teleparallel reading of torsion: a loop of moves fails to
close by a turn (curvature) or by a carry (torsion), and the carry of a pair of turns is the
separation of their pivots.

```text
(k_u, b_u) ∘ (k_v, b_v) − (k_v, b_v) ∘ (k_u, b_u) = b_u (1 − k_v) − b_v (1 − k_u)   (complex_moves_commutator)
                                                  = (1 − k_u)(1 − k_v)(O_u − O_v)     (complex_commutator_pivots)
k_u, k_v ≠ 1:   the two moves commute  ⇔  O_u = O_v               (complex_moves_commute_iff_shared_pivot)
(M, b₁) ∘ (M, b₂) − (M, b₂) ∘ (M, b₁) = (1 − M)(b₁ − b₂)          (move_same_linear_commutator)
```

What is proved.

1. **Order is torsion** (`complex_moves_commutator`, `complex_commutator_pivots`,
   `complex_moves_commute_iff_shared_pivot`): two turns commute exactly when they share a pivot,
   and the carry of their loop is the product of their two departures from free fall times the
   separation of their pivots.
2. **One linear part** (`move_same_linear_commutator`): moves that share their linear part `M` and
   differ only in what they add leave the carry `(1 − M)(b₁ − b₂)`. A stream of such moves is a sum
   of `M`-transported additions, so its state is a function of how often each addition occurred at
   each lag.
3. **The Burgers vector** (`flat_loop_carry`): a loop of pure translations closes by the sum of
   its carries.
4. **The carry needs its base point** (`move_basepoint`, `translation_basepoint`): read from a base
   point shifted by `t`, a move keeps its turn and its carry gains `(M − 1) t`; the carry is
   independent of the base point only when the turn is trivial.
5. **The fifth torsion is the field** (`fifth_torsion_is_field`): for a frame `e⁵ = dy + A`, an
   exact part never reaches the coboundary, so `d e⁵ = d A`; this is `T⁵ = F` of teleparallel
   Kaluza–Klein, with charge the carry around the fifth circle.
6. **The redshift loop** (`redshift_loop`): on a grid of cells, the coboundary of the time coframe
   `e⁰ = N dt` summed over the cells is the product of the lapse and clock differences across the
   whole grid (Stokes on a grid), so a static lapse difference leaves a carry around every loop
   that spans it.
7. **The squeeze is the ratio's dilation** (`squeeze_dilates_ratio`): `diag(λ, λ⁻¹)` acting on the
   undivided pair `(a, b)` multiplies its ratio by `λ²`. The det-1 squeeze of the turn·boost·shear
   factorization and the ratio dilation `MoveKind::Boost` are one boost read in two charts.

No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace Holonics.Geometry.Motion

/-! ## 1. Order is torsion -/

section ComplexTorsion

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] **The carry of a loop of two moves.** -/
theorem complex_moves_commutator (ku bu kv bv z : K) :
    (ku * (kv * z + bv) + bu) - (kv * (ku * z + bu) + bv) = bu * (1 - kv) - bv * (1 - ku) := by
  ring

/-- [proved-derived; formal-checked] **The carry is the separation of the pivots.** -/
theorem complex_commutator_pivots {ku kv bu bv Ou Ov : K}
    (hOu : (1 - ku) * Ou = bu) (hOv : (1 - kv) * Ov = bv) :
    bu * (1 - kv) - bv * (1 - ku) = (1 - ku) * (1 - kv) * (Ou - Ov) := by
  linear_combination (-(1 - kv)) * hOu + (1 - ku) * hOv

/-- [proved-derived; formal-checked] **Two turns commute exactly when they share a pivot.** -/
theorem complex_moves_commute_iff_shared_pivot {ku kv bu bv Ou Ov : K} (hu : ku ≠ 1)
    (hv : kv ≠ 1) (hOu : (1 - ku) * Ou = bu) (hOv : (1 - kv) * Ov = bv) (z : K) :
    ku * (kv * z + bv) + bu = kv * (ku * z + bu) + bv ↔ Ou = Ov := by
  constructor
  · intro h
    have h0 : (1 - ku) * (1 - kv) * (Ou - Ov) = 0 := by
      linear_combination h + (1 - kv) * hOu - (1 - ku) * hOv
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (sub_eq_zero.mp h2).symm hu
      · exact absurd (sub_eq_zero.mp h2).symm hv
    · exact sub_eq_zero.mp h1
  · intro h
    linear_combination (-(1 - kv)) * hOu + (1 - ku) * hOv + (1 - ku) * (1 - kv) * h

end ComplexTorsion

/-! ## 2. One linear part, the Burgers vector and the base point -/

section AffineTorsion

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- [proved-derived; formal-checked] **Moves with one linear part** leave the carry `(1 − M)(b₁ − b₂)`. -/
theorem move_same_linear_commutator (M : Module.End R V) (b₁ b₂ x : V) :
    move M b₁ (move M b₂ x) - move M b₂ (move M b₁ x) = (1 - M) (b₁ - b₂) := by
  simp only [move, map_add, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  abel

/-- [proved-derived; formal-checked] **The Burgers vector:** a loop of pure translations closes by the sum of
its carries. -/
theorem flat_loop_carry (bs : List V) (x : V) :
    bs.foldr (move (1 : Module.End R V)) x = x + bs.sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldr_cons, ih, move, Module.End.one_apply, List.sum_cons]
    abel

/-- [proved-derived; formal-checked] **The carry needs its base point:** read from a base point shifted by `t`,
a move keeps its turn and its carry gains `M t − t`. -/
theorem move_basepoint (M : Module.End R V) (b t x : V) :
    move M b (x + t) - t = move M (b + (M t - t)) x := by
  rw [move, move, map_add]
  abel

/-- [proved-derived; formal-checked] A pure translation reads the same carry from every base point. -/
theorem translation_basepoint (b t x : V) :
    move (1 : Module.End R V) b (x + t) - t = move (1 : Module.End R V) b x := by
  rw [move_basepoint, Module.End.one_apply, sub_self, add_zero]

end AffineTorsion

/-! ## 3. The fifth torsion, the redshift loop and the squeeze -/

/-- [proved-derived; formal-checked] **The fifth torsion is the field:** with `d₁ ∘ d₀ = 0`, the coboundary of the
frame `e⁵ = d₀ y + A` is the coboundary of `A`. -/
theorem fifth_torsion_is_field {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (d₀ : U →+ V) (d₁ : V →+ W) (hdd : ∀ u, d₁ (d₀ u) = 0) (y : U) (A : V) :
    d₁ (d₀ y + A) = d₁ A := by
  rw [map_add, hdd, zero_add]

/-- [proved-derived; formal-checked] **The redshift loop:** summed over a grid of cells, the coboundary of the
time coframe is the product of the lapse difference and the clock difference across the grid. -/
theorem redshift_loop {A : Type*} [CommRing A] (N T : ℕ → A) (n m : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, (N (i + 1) - N i) * (T (j + 1) - T j) =
      (N n - N 0) * (T m - T 0) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_range_sub]

/-- [proved-derived; formal-checked] **The squeeze is the ratio's dilation:** `diag(λ, λ⁻¹)` on the undivided pair
`(a, b)` multiplies its ratio by `λ²`. -/
theorem squeeze_dilates_ratio {K : Type*} [Field K] (l a b : K) :
    (l * a) / (l⁻¹ * b) = l ^ 2 * (a / b) := by
  rw [div_eq_mul_inv, mul_inv, inv_inv]
  ring

end Holonics.Geometry.Motion

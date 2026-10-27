import HolonicsResearch.Geometry.TorusIndex
import Holonics.Compression.Landmark.SiteKind

/-!
# A boost's periodic points on the clock torus are its Lefschetz count

`Compression/Landmark/SiteKind` reads a determinant-one site `M` on the two-clock torus through
`det(Mⁿ − 1) = 2 − t_n` with `t_n = tr(Mⁿ)` (`det_pow_sub_one`), calls its absolute value "the
classical count of period-`n` points (the Lefschetz reading, not formalized here)", and proves the
rate `(1/n) log |t_n − 2| → log k` (`torus_count_rate`). #410 owes the Lefschetz count of periodic
points of boosts on the clock torus. `Geometry/TorusIndex` proves the count for one map
(`card_fixed`); this file joins the two.

[proved-standard; formal-checked] What is proved.

1. **The Lefschetz number on the torus's cohomology** (`lefschetz`, `lefschetz_eq_det`,
   `lefschetz_eq_det_sub_one`): with ranks 1, 2, 1 and the move acting by `1`, `N` and `det N`,
   `L(N) = 1 − tr N + det N`, which is `det(1 − N)` and `det(N − 1)` on the two-torus.
2. **The count is the Lefschetz number** (`card_fixed_lefschetz`): a move with `L(N) ≠ 0` fixes
   exactly `|L(N)|` points. For a hyperbolic move every fixed point has index `sign det(1 − N)`, so
   the signed count is `L(N)` itself; the theorem states the unsigned count.
3. **A boost's period-`n` points** (`boost_periodic_points`, `boost_iterate_points`): for
   `det M = 1` and `tr² M > 4`, `#{x : Mⁿ x = x} = |t_n − 2|` for every `n ≥ 1`, through
   `det_pow_sub_one` and the growth `n + 2 ≤ |t_n|` (`SiteKind.boost_counts_grow`), which keeps
   `t_n` off `2`. The count is the same read on the `n`-fold step `(act M)^[n]`
   (`TorusIndex.act_pow`).
4. **Their growth is the rapidity** (`boost_periodic_rate`): with `k > 1` and `k + k⁻¹ = tr M`,
   `(1/n) log #{x : Mⁿ x = x} → log k`, the topological entropy of the boost on the torus
   (`SiteKind.torus_count_rate` read as a count).

The computational object is the helical pair interaction on the clock torus: a period-`n` point is a
place the boost's `n`-fold carry returns to, and the count is the cell holonomy's index. Of the
winding guide's six general objects this touches the cell holonomy and the tube (the `n`-fold
clocked span); the helix, the pair, faces and placement and the tower thread stay attached.

Consumers: the atlas rows `landmark.boost-entropy-rapidity` and `motion.torus-twists-every-kind`,
and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.TorusPeriodic

open Holonics.Geometry.TorusIndex
open Holonics.Compression.Landmark

/-! ## 1. The Lefschetz number -/

/-- [definition] The Lefschetz number of a two-torus move on the torus's cohomology (ranks 1, 2, 1,
acted on by `1`, `N` and `det N`): `L(N) = 1 − tr N + det N`. -/
def lefschetz (N : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := 1 - N.trace + N.det

/-- [proved-standard; formal-checked] `L(N) = det(N − 1)` on the two-torus. -/
theorem lefschetz_eq_det_sub_one (N : Matrix (Fin 2) (Fin 2) ℤ) : lefschetz N = (N - 1).det := by
  rw [TorusBraid.det_sub_one_fin_two, lefschetz]
  ring

/-- [proved-standard; formal-checked] `L(N) = det(1 − N)` on the two-torus. -/
theorem lefschetz_eq_det (N : Matrix (Fin 2) (Fin 2) ℤ) : lefschetz N = (1 - N).det := by
  rw [lefschetz_eq_det_sub_one, ← neg_sub, Matrix.det_neg]
  simp only [Fintype.card_fin]
  ring

/-! ## 2. The count is the Lefschetz number -/

/-- [proved-standard; formal-checked] **The count is the Lefschetz number**: a two-torus move with
`L(N) ≠ 0` fixes exactly `|L(N)|` points. -/
theorem card_fixed_lefschetz (N : Matrix (Fin 2) (Fin 2) ℤ) (hL : lefschetz N ≠ 0) :
    Nat.card {x : UnitAddTorus (Fin 2) // act N x = x} = (lefschetz N).natAbs := by
  rw [lefschetz_eq_det_sub_one] at hL ⊢
  exact card_fixed N hL

/-! ## 3. A boost's periodic points -/

/-- [proved-standard; formal-checked] **A boost's period-`n` points**: for `det M = 1` and
`tr² M > 4`, `#{x : Mⁿ x = x} = |t_n − 2|` with `t_n = tr(Mⁿ)` the trace recurrence, for every
`n ≥ 1`. -/
theorem boost_periodic_points (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hboost : 4 < M.trace ^ 2) {n : ℕ} (hn : 0 < n) :
    Nat.card {x : UnitAddTorus (Fin 2) // act (M ^ n) x = x} =
      (TraceSequence.trace M.trace 1 n - 2).natAbs := by
  have hd := SiteKind.det_pow_sub_one M hdet n
  have hgrow := SiteKind.boost_counts_grow M.trace hboost n
  have hne : (M ^ n - 1).det ≠ 0 := by
    rw [hd]
    intro h0
    have h2 : TraceSequence.trace M.trace 1 n = 2 := by linarith
    rw [h2, abs_of_pos (by norm_num : (0 : ℤ) < 2)] at hgrow
    omega
  rw [card_fixed _ hne, hd, ← Int.natAbs_neg, neg_sub]

/-- [proved-standard; formal-checked] The same count read on the boost's `n`-fold step: the points
with `(act M)^[n] x = x` (`TorusIndex.act_pow`). -/
theorem boost_iterate_points (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1)
    (hboost : 4 < M.trace ^ 2) {n : ℕ} (hn : 0 < n) :
    Nat.card {x : UnitAddTorus (Fin 2) // (act M)^[n] x = x} =
      (TraceSequence.trace M.trace 1 n - 2).natAbs := by
  rw [← boost_periodic_points M hdet hboost hn]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by rw [act_pow])

/-- [proved-standard; formal-checked] **The periodic points grow at the rapidity**: with `k > 1`
and `k + k⁻¹ = tr M`, `(1/n) log #{x : Mⁿ x = x} → log k`. -/
theorem boost_periodic_rate (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (k : ℝ)
    (hk1 : 1 < k) (hk : k + k⁻¹ = M.trace) :
    Filter.Tendsto
      (fun n : ℕ => Real.log (Nat.card {x : UnitAddTorus (Fin 2) // act (M ^ n) x = x}) / n)
      Filter.atTop (nhds (Real.log k)) := by
  have hkpos : 0 < k := by linarith
  have hk0 : k ≠ 0 := hkpos.ne'
  have hx1 : k⁻¹ < 1 := inv_lt_one_of_one_lt₀ hk1
  have h2 : (2 : ℝ) < k + k⁻¹ := by
    nlinarith [mul_pos (sub_pos.mpr hk1) (sub_pos.mpr hx1), mul_inv_cancel₀ hk0]
  have hboost : 4 < M.trace ^ 2 := by
    have h3 : (2 : ℤ) < M.trace := by
      have : (2 : ℝ) < M.trace := by
        rw [← hk]
        exact h2
      exact_mod_cast this
    nlinarith
  refine (SiteKind.torus_count_rate M.trace k hk1 hk).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [boost_periodic_points M hdet hboost (by omega)]
  simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_ofNat]

end Holonics.Geometry.TorusPeriodic

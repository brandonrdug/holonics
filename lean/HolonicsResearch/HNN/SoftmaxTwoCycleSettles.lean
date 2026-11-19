import HolonicsResearch.HNN.SoftmaxTwoCycle

/-!
# The softmax orbit settles on two-cycles: states two passes apart draw together in norm

`HNN/SoftmaxTwoCycle` proves that a place hearing its own softmax release in step lowers the pair energy by the
relative entropy between states two passes apart, and that those relative entropies are summable along the orbit of a
law (`kl_two_apart_summable`). Its limits left the step from a summable relative entropy to the states themselves:
that `x_(k+2) − x_k → 0` in norm. #410's box on the synchronous two-cycle (the ring record of November 13, §2 and §5;
atlas `tower.field-echo`, `motion.relaxed-step-three-kinds`) owes it. This file proves it.

[proved-standard; formal-checked] What is proved, for a law `s` and a positive law `u` on places `P` and classes `C`.

1. **The relative entropy bounds the squared Hellinger distance** (`log_gap_ge`, `kl_ge_hellinger`): with
   `H²(s, u) = Σ_a (√s_a − √u_a)²` (`hellinger`), `D(s ‖ u) ≥ H²(s, u)`. Each term obeys
   `s (log s − log u) ≥ 2 (s − √(s u))`, which is `log y ≤ y − 1` at `y = √(u/s)`, and the two laws have equal mass
   at each place, so the terms `s + u − 2√(su)` sum to the same total.
2. **On laws the squared difference is at most four times the Hellinger term** (`sq_sub_le_hellinger`,
   `sumSq_le_hellinger`): `(s_a − u_a)² ≤ 4 (√s_a − √u_a)²`, since each entry is at most one.
3. **Along the orbit** of a law at a temperature `T > 0` under a symmetric coupling:
   - the squared Euclidean departure from a two-cycle is summable, `Σ_k Σ_a (x_k(a) − x_(k+2)(a))² < ∞`
     (`departure_summable`);
   - every entry draws together, `x_(k+2)(a) − x_k(a) → 0` (`tendsto_entry_two_apart`);
   - and in norm, `‖x_(k+2) − x_k‖ → 0` (`tendsto_norm_two_apart`).

What is not claimed. The orbit itself need not converge: two passes apart the states draw together, but a slow drift
along a set of two-cycles is not excluded here, and convergence of the orbit needs Łojasiewicz's inequality or isolated
critical points. No rate is given; the summable departure is the whole statement. The sign chart is the limit `T → 0`
and is proved apart (`HNN/SynchronousTwoCycle.eventually_period_two`), where the period two is reached in finitely many
steps.

The computational object is the helical pair interaction: the coupling is the pair contacts' symmetric exchange, the
release a place's face at the field's own temperature, and the two-cycle the sheet that flips each pass. Of the winding
guide's six general objects this touches the pair, faces and placement and the tube (the passes as a clocked span); the
helix, the cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SoftmaxTwoCycle

open Filter Topology

variable {P C : Type*} [Fintype P] [Fintype C]

/-! ## 1. The relative entropy and the Hellinger distance -/

/-- [definition] The squared Hellinger distance summed over the places' faces. -/
noncomputable def hellinger (s u : P × C → ℝ) : ℝ := ∑ a, (Real.sqrt (s a) - Real.sqrt (u a)) ^ 2

/-- One term: `s (log s − log u) ≥ 2 (s − √s √u)` for `s ≥ 0`, `u > 0`. -/
theorem log_gap_ge {s u : ℝ} (hs : 0 ≤ s) (hu : 0 < u) :
    2 * (s - Real.sqrt s * Real.sqrt u) ≤ s * (Real.log s - Real.log u) := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0; simp
  · have hy : 0 < Real.sqrt u / Real.sqrt s := div_pos (Real.sqrt_pos.2 hu) (Real.sqrt_pos.2 hpos)
    have hlog := Real.log_le_sub_one_of_pos hy
    have hss : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs
    have huu : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu.le
    have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hpos
    have hlogy : Real.log (Real.sqrt u / Real.sqrt s) = (Real.log u - Real.log s) / 2 := by
      rw [Real.log_div (Real.sqrt_pos.2 hu).ne' hsq.ne', Real.log_sqrt hu.le, Real.log_sqrt hs]
      ring
    rw [hlogy] at hlog
    have key : 2 * (1 - Real.sqrt u / Real.sqrt s) ≤ Real.log s - Real.log u := by linarith
    have hmul := mul_le_mul_of_nonneg_left key hs
    have hdiv : s * (Real.sqrt u / Real.sqrt s) = Real.sqrt s * Real.sqrt u := by
      have hne : Real.sqrt s ≠ 0 := hsq.ne'
      calc s * (Real.sqrt u / Real.sqrt s) = (Real.sqrt s * Real.sqrt s) * (Real.sqrt u / Real.sqrt s) := by
            rw [hss]
        _ = Real.sqrt s * Real.sqrt u := by field_simp
    have e : s * (2 * (1 - Real.sqrt u / Real.sqrt s)) = 2 * s - 2 * (s * (Real.sqrt u / Real.sqrt s)) := by ring
    rw [hdiv] at e
    linarith

/-- Statement 1: `D(s ‖ u) ≥ H²(s, u)` for a law `s` and a positive law `u`. -/
theorem kl_ge_hellinger {s u : P × C → ℝ} (hs : IsLaw s) (hu0 : ∀ a, 0 < u a) (hu : ∀ i, ∑ c, u (i, c) = 1) :
    hellinger s u ≤ kl s u := by
  have hmass : ∑ a, s a = ∑ a, u a := by
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => by rw [hs.2 i, hu i]
  have hterm : ∀ a, (Real.sqrt (s a) - Real.sqrt (u a)) ^ 2
      = s a + u a - 2 * (Real.sqrt (s a) * Real.sqrt (u a)) := by
    intro a
    rw [sub_sq, Real.sq_sqrt (hs.1 a), Real.sq_sqrt (hu0 a).le]
    ring
  calc hellinger s u = ∑ a, 2 * (s a - Real.sqrt (s a) * Real.sqrt (u a)) := by
        unfold hellinger
        rw [Finset.sum_congr rfl fun a _ => hterm a]
        simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub, ← Finset.mul_sum]
        linarith [hmass]
    _ ≤ ∑ a, s a * (Real.log (s a) - Real.log (u a)) :=
        Finset.sum_le_sum fun a _ => log_gap_ge (hs.1 a) (hu0 a)
    _ = kl s u := rfl

/-! ## 2. Entries of laws -/

/-- On entries in `[0, 1]`, `(s − u)² ≤ 4 (√s − √u)²`. -/
theorem sq_sub_le_hellinger {s u : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hs1 : s ≤ 1) (hu1 : u ≤ 1) :
    (s - u) ^ 2 ≤ 4 * (Real.sqrt s - Real.sqrt u) ^ 2 := by
  have h1 := Real.sq_sqrt hs
  have h2 := Real.sq_sqrt hu
  have hs' : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1
  have hu' : Real.sqrt u ≤ 1 := Real.sqrt_le_one.mpr hu1
  have hs0 := Real.sqrt_nonneg s
  have hu0 := Real.sqrt_nonneg u
  have hfac : s - u = (Real.sqrt s - Real.sqrt u) * (Real.sqrt s + Real.sqrt u) := by
    linear_combination h2 - h1
  rw [hfac, mul_pow]
  have hsum : (Real.sqrt s + Real.sqrt u) ^ 2 ≤ 4 := by nlinarith
  nlinarith [sq_nonneg (Real.sqrt s - Real.sqrt u)]

/-- Statement 2: on two laws, `Σ_a (s_a − u_a)² ≤ 4 H²(s, u)`. -/
theorem sumSq_le_hellinger {s u : P × C → ℝ} (hs : IsLaw s) (hu : IsLaw u) :
    ∑ a, (s a - u a) ^ 2 ≤ 4 * hellinger s u := by
  rw [hellinger, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ =>
    sq_sub_le_hellinger (hs.1 a) (hu.1 a) (law_le_one hs a) (law_le_one hu a)

/-! ## 3. Along the orbit -/

variable [Nonempty C] {W : P × C → P × C → ℝ} (b : P × C → ℝ) {T : ℝ} {x : P × C → ℝ}

private theorem departure_le (hx : IsLaw x) (k : ℕ) :
    ∑ a, (orbit W b T x k a - orbit W b T x (k + 2) a) ^ 2
      ≤ 4 * kl (orbit W b T x k) (orbit W b T x (k + 2)) := by
  have h2 : orbit W b T x (k + 2) = release T (field W b (orbit W b T x (k + 1))) := by
    rw [show k + 2 = k + 1 + 1 from rfl, orbit_succ]; rfl
  calc _ ≤ 4 * hellinger (orbit W b T x k) (orbit W b T x (k + 2)) :=
        sumSq_le_hellinger (orbit_isLaw W b T hx k) (orbit_isLaw W b T hx (k + 2))
    _ ≤ 4 * kl (orbit W b T x k) (orbit W b T x (k + 2)) := by
        gcongr
        rw [h2]
        exact kl_ge_hellinger (orbit_isLaw W b T hx k) (release_pos T _) (release_isLaw T _).2

/-- Statement 3, first part: the squared Euclidean departure from a two-cycle is summable along the orbit. -/
theorem departure_summable (hW : ∀ a a', W a a' = W a' a) (hT : 0 < T) (hx : IsLaw x) :
    Summable (fun k => ∑ a, (orbit W b T x k a - orbit W b T x (k + 2) a) ^ 2) := by
  refine Summable.of_nonneg_of_le (fun k => Finset.sum_nonneg fun a _ => sq_nonneg _)
    (fun k => departure_le b hx k) ?_
  exact (kl_two_apart_summable hW b hT hx).mul_left 4

/-- Statement 3, second part: every entry draws together two passes apart. -/
theorem tendsto_entry_two_apart (hW : ∀ a a', W a a' = W a' a) (hT : 0 < T) (hx : IsLaw x) (a : P × C) :
    Tendsto (fun k => orbit W b T x (k + 2) a - orbit W b T x k a) atTop (𝓝 0) := by
  have hsum := (departure_summable b hW hT hx).tendsto_atTop_zero
  have hsq : Tendsto (fun k => (orbit W b T x (k + 2) a - orbit W b T x k a) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun k => sq_nonneg _) (fun k => ?_) hsum
    rw [show (orbit W b T x (k + 2) a - orbit W b T x k a) ^ 2
      = (orbit W b T x k a - orbit W b T x (k + 2) a) ^ 2 by ring]
    exact Finset.single_le_sum (f := fun a' => (orbit W b T x k a' - orbit W b T x (k + 2) a') ^ 2)
      (fun a' _ => sq_nonneg _) (Finset.mem_univ a)
  have habs : Tendsto (fun k => |orbit W b T x (k + 2) a - orbit W b T x k a|) atTop (𝓝 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 habs

/-- Statement 3, third part: `‖x_(k+2) − x_k‖ → 0`. -/
theorem tendsto_norm_two_apart (hW : ∀ a a', W a a' = W a' a) (hT : 0 < T) (hx : IsLaw x) :
    Tendsto (fun k => ‖orbit W b T x (k + 2) - orbit W b T x k‖) atTop (𝓝 0) := by
  rw [← tendsto_zero_iff_norm_tendsto_zero]
  exact tendsto_pi_nhds.2 fun a => tendsto_entry_two_apart b hW hT hx a

end Holonics.HNN.SoftmaxTwoCycle

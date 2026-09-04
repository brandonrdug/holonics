import Mathlib

/-!
# The heat deformation binds the integer events: the flow weight on a composite is not
multiplicative

Under the de Bruijn--Newman deformation the Fourier profile of the completed zeta,
`Φ(u) = Σ_n n^{−1/2} φ(u + log n)`, one Gamma-type profile `φ` translated to the integer event
`log n` and weighted by the half-density `n^{−1/2}`, is multiplied by `e^{t u²}`.  In the `n`-th
event's own coordinate `v = u + log n`,

```text
e^{t (v − log n)²} = e^{t v²} · n^{−2 t v} · e^{t (log n)²}.
```

The middle factor is a running power of `n` and stays completely multiplicative; the last factor,
the flow weight `e^{t (log n)²}`, is not.  On a composite `m · k` it factors as the constituents'
weights times a binding defect `e^{2 t log m log k}`, and that defect is one exactly when `t = 0`
or a constituent is the unit.  So the integer events compose freely, with unique factorization
intact, at time zero and at no other time; and away from time zero every event is entangled with
the archimedean profile through `n^{−2tv}`.  This is the exact reason the flow side of the phase
ledger cannot decide the time-zero face on its own: the Euler product exists only there.

Every theorem below is elementary real arithmetic and is discharged with no `sorryAx`.  The
reading is in the dated record of 2026-09-03.
-/

namespace Soma.Holonics.RH.HeatFlowBinding

open Real

/-- The flow weight carried by the integer event `n` at deformation time `t`. -/
noncomputable def flowWeight (t : ℝ) (n : ℝ) : ℝ := exp (t * (log n) ^ 2)

/-- The binding defect between two constituents at deformation time `t`. -/
noncomputable def bindingDefect (t : ℝ) (m k : ℝ) : ℝ := exp (2 * t * log m * log k)

/-- **The flow weight of a composite is the product of its constituents' weights times the
binding defect.** -/
theorem flowWeight_mul (t : ℝ) {m k : ℝ} (hm : 0 < m) (hk : 0 < k) :
    flowWeight t (m * k) = flowWeight t m * flowWeight t k * bindingDefect t m k := by
  unfold flowWeight bindingDefect
  rw [log_mul hm.ne' hk.ne', ← exp_add, ← exp_add]
  congr 1
  ring

/-- **At time zero the binding defect is one: composition is free.** -/
theorem bindingDefect_zero (m k : ℝ) : bindingDefect 0 m k = 1 := by
  simp [bindingDefect]

/-- **Away from time zero, two constituents above the unit bind.** -/
theorem bindingDefect_ne_one {t m k : ℝ} (ht : t ≠ 0) (hm : 1 < m) (hk : 1 < k) :
    bindingDefect t m k ≠ 1 := by
  unfold bindingDefect
  intro h
  rw [exp_eq_one_iff] at h
  have hlm : log m ≠ 0 := (log_pos hm).ne'
  have hlk : log k ≠ 0 := (log_pos hk).ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ht) hlm) hlk h

/-- **The binding defect is one exactly when the time is zero or a constituent is the unit**, for
constituents at or above the unit. -/
theorem bindingDefect_eq_one_iff {t m k : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    bindingDefect t m k = 1 ↔ t = 0 ∨ m = 1 ∨ k = 1 := by
  unfold bindingDefect
  rw [exp_eq_one_iff]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · norm_num at h3
        · exact Or.inl h3
      · right
        left
        rcases log_eq_zero.mp h2 with h3 | h3 | h3
        · linarith
        · exact h3
        · linarith
    · right
      right
      rcases log_eq_zero.mp h1 with h3 | h3 | h3
      · linarith
      · exact h3
      · linarith
  · rintro (h | h | h)
    · simp [h]
    · simp [h]
    · simp [h]

/-- **The running-abscissa identity.**  The flow factor at the `n`-th integer event, in the event's
own coordinate `v = u + log n`, is the archimedean factor `e^{t v²}`, the running power `n^{−2tv}`,
and the flow weight `e^{t (log n)²}`. -/
theorem flow_factor_split (t v : ℝ) {n : ℝ} (hn : 0 < n) :
    exp (t * (v - log n) ^ 2) = exp (t * v ^ 2) * n ^ (-(2 * t * v)) * flowWeight t n := by
  unfold flowWeight
  rw [rpow_def_of_pos hn, ← exp_add, ← exp_add]
  congr 1
  ring

end Soma.Holonics.RH.HeatFlowBinding

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite divisor-source transport

This file formalizes the finite algebraic core of the divisor-source
continuation.  It deliberately does not formalize the analytic construction
of Suzuki's kernel, its sign seam, or its asymptotics.

The theorem proved here is conditional and exact:

* a negative source cell has a demand;
* a positive receiver cell has a capacity;
* an incidence relation says which source may use which receiver;
* each source distributes its demand proportionally across all of its
  incident receiver capacity;
* the resulting receiver load is its capacity multiplied by one explicit
  congestion value.

Consequently, congestion at most one gives a feasible finite transport, and
the total demand is no greater than the total capacity.  `ℝ` below is Lean's
exact real-number object; no floating-point arithmetic is used.
-/

open scoped BigOperators

namespace Soma.RHSourceTransport

section Finite

variable {Old New : Type*}
variable [Fintype Old] [Fintype New]
variable (demand : Old → ℝ) (capacity : New → ℝ)
variable (incident : Old → New → Prop) [DecidableRel incident]

/-- Total capacity visible to one old/source cell. -/
def descendantCapacity (n : Old) : ℝ :=
  ∑ m : New, if incident n m then capacity m else 0

/--
The canonical diffuse candidate: distribute one source demand in proportion
to the capacities of all incident receivers.
-/
noncomputable def proportionalFlow (n : Old) (m : New) : ℝ :=
  if incident n m then
    demand n * capacity m / descendantCapacity capacity incident n
  else
    0

/--
The receiver-relative sum of all normalized demands which can arrive at one
new cell.
-/
noncomputable def congestion (m : New) : ℝ :=
  ∑ n : Old, if incident n m then
    demand n / descendantCapacity capacity incident n
  else
    0

omit [Fintype Old] in
theorem proportionalFlow_nonnegative
    (hd : ∀ n, 0 ≤ demand n)
    (hc : ∀ m, 0 ≤ capacity m)
    (hz : ∀ n, descendantCapacity capacity incident n ≠ 0)
    (n : Old) (m : New) :
    0 ≤ proportionalFlow demand capacity incident n m := by
  classical
  have hcap : 0 ≤ descendantCapacity capacity incident n := by
    apply Finset.sum_nonneg
    intro m hm
    by_cases hnm : incident n m
    · simp [hnm, hc m]
    · simp [hnm]
  have hcap_pos : 0 < descendantCapacity capacity incident n :=
    lt_of_le_of_ne hcap (Ne.symm (hz n))
  by_cases hnm : incident n m
  · rw [proportionalFlow, if_pos hnm]
    exact div_nonneg (mul_nonneg (hd n) (hc m)) hcap_pos.le
  · simp [proportionalFlow, hnm]

omit [Fintype Old] in
/-- Every proportional row carries exactly its source demand. -/
theorem proportionalFlow_row_sum
    (n : Old)
    (hz : descendantCapacity capacity incident n ≠ 0) :
    (∑ m : New, proportionalFlow demand capacity incident n m) = demand n := by
  classical
  calc
    (∑ m : New, proportionalFlow demand capacity incident n m)
        = ∑ m : New,
            (demand n / descendantCapacity capacity incident n) *
              (if incident n m then capacity m else 0) := by
                apply Finset.sum_congr rfl
                intro m hm
                by_cases hnm : incident n m
                · simp [proportionalFlow, hnm]
                  ring
                · simp [proportionalFlow, hnm]
    _ = (demand n / descendantCapacity capacity incident n) *
          descendantCapacity capacity incident n := by
            unfold descendantCapacity
            rw [Finset.mul_sum]
    _ = demand n := by
          field_simp

/--
The complete incoming load at a receiver is exactly its capacity multiplied
by its congestion.
-/
theorem proportionalFlow_column_sum (m : New) :
    (∑ n : Old, proportionalFlow demand capacity incident n m) =
      capacity m * congestion demand capacity incident m := by
  classical
  rw [congestion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnm : incident n m
  · simp only [proportionalFlow, hnm, if_true]
    ring
  · simp [proportionalFlow, hnm]

/--
If every receiver's congestion is at most one, the proportional flow respects
every receiver capacity.
-/
theorem proportionalFlow_respects_capacity
    (hc : ∀ m, 0 ≤ capacity m)
    (hcong : ∀ m, congestion demand capacity incident m ≤ 1)
    (m : New) :
    (∑ n : Old, proportionalFlow demand capacity incident n m) ≤ capacity m := by
  rw [proportionalFlow_column_sum]
  nlinarith [hc m, hcong m]

/--
Every declared finite family of sources incident to one receiver contributes
its complete normalized demand to that receiver's congestion.

This is the finite combinatorial carrier of the primorial obstruction: once a
family of quotient axes has normalized demands summing to more than one, the
proportional transport necessarily overloads that receiver.
-/
theorem subset_normalized_load_le_congestion
    (hd : ∀ n, 0 ≤ demand n)
    (hc : ∀ m, 0 ≤ capacity m)
    (hz : ∀ n, descendantCapacity capacity incident n ≠ 0)
    (S : Finset Old)
    (m : New)
    (hinc : ∀ n ∈ S, incident n m) :
    (∑ n ∈ S, demand n / descendantCapacity capacity incident n) ≤
      congestion demand capacity incident m := by
  classical
  rw [congestion]
  calc
    (∑ n ∈ S, demand n / descendantCapacity capacity incident n)
        = ∑ n ∈ S,
            if incident n m then
              demand n / descendantCapacity capacity incident n
            else
              0 := by
                apply Finset.sum_congr rfl
                intro n hn
                simp [hinc n hn]
    _ ≤ ∑ n ∈ Finset.univ,
          if incident n m then
            demand n / descendantCapacity capacity incident n
          else
            0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · simp
              · intro n hn_univ hn_not_mem
                by_cases hnm : incident n m
                · simp only [hnm, if_true]
                  have hcap : 0 ≤ descendantCapacity capacity incident n := by
                    apply Finset.sum_nonneg
                    intro receiver hreceiver
                    by_cases hin : incident n receiver
                    · simp [hin, hc receiver]
                    · simp [hin]
                  have hcap_pos : 0 < descendantCapacity capacity incident n :=
                    lt_of_le_of_ne hcap (Ne.symm (hz n))
                  exact div_nonneg (hd n) hcap_pos.le
                · simp [hnm]

theorem congestion_exceeds_one_of_subset_load
    (hd : ∀ n, 0 ≤ demand n)
    (hc : ∀ m, 0 ≤ capacity m)
    (hz : ∀ n, descendantCapacity capacity incident n ≠ 0)
    (S : Finset Old)
    (m : New)
    (hinc : ∀ n ∈ S, incident n m)
    (hover :
      1 < ∑ n ∈ S, demand n / descendantCapacity capacity incident n) :
    1 < congestion demand capacity incident m :=
  hover.trans_le
    (subset_normalized_load_le_congestion
      demand capacity incident hd hc hz S m hinc)

/--
The finite source sign follows from a congestion certificate: exact row
transport plus bounded column load forces total demand not to exceed total
positive capacity.
-/
theorem total_demand_le_total_capacity
    (hc : ∀ m, 0 ≤ capacity m)
    (hz : ∀ n, descendantCapacity capacity incident n ≠ 0)
    (hcong : ∀ m, congestion demand capacity incident m ≤ 1) :
    (∑ n : Old, demand n) ≤ ∑ m : New, capacity m := by
  calc
    (∑ n : Old, demand n)
        = ∑ n : Old, ∑ m : New,
            proportionalFlow demand capacity incident n m := by
              apply Finset.sum_congr rfl
              intro n hn
              symm
              exact proportionalFlow_row_sum demand capacity incident n (hz n)
    _ = ∑ m : New, ∑ n : Old,
          proportionalFlow demand capacity incident n m := by
            rw [Finset.sum_comm]
    _ ≤ ∑ m : New, capacity m := by
          exact Finset.sum_le_sum fun m hm =>
            proportionalFlow_respects_capacity demand capacity incident hc hcong m

end Finite

end Soma.RHSourceTransport

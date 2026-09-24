import Mathlib

/-!
# A deterministic address through an exact winding census

An oriented region with nonnegative zero count may be split in two when the
shared boundary cut is certified zero-free. The argument principle and
shared-edge cancellation supply the additive count law. This file extracts
the purely exact navigation consequence: a positive parent has a positive
child, and a canonical ordered address continues through every finite
depth. It does not assert that an arbitrary count function came from an
analytic source or that nested regions have a unique limit point.
-/

namespace Soma.Holonics.Computation.CertifiedWindingRoute

open Filter

/-- The two addressed children of one region. -/
def left (address : List Bool) : List Bool := address ++ [false]
def right (address : List Bool) : List Bool := address ++ [true]

/-- Additivity of a nonnegative divisor count under one certified split. -/
def AdditiveCount (count : List Bool → ℕ) : Prop :=
  ∀ address, count address = count (left address) + count (right address)

/-- A positive parent has a positive child, and conversely, under the
exact additivity of its two oriented children. -/
theorem positive_iff_positive_child {count : List Bool → ℕ}
    (hadd : AdditiveCount count) (address : List Bool) :
    0 < count address ↔
      0 < count (left address) ∨ 0 < count (right address) := by
  rw [hadd address]
  omega

/-- A zero-count parent has two zero-count children, and conversely. -/
theorem empty_iff_both_empty {count : List Bool → ℕ}
    (hadd : AdditiveCount count) (address : List Bool) :
    count address = 0 ↔
      count (left address) = 0 ∧ count (right address) = 0 := by
  rw [hadd address]
  omega

/-- All regions at one exact subdivision depth, retaining both oriented
children and their complete addresses. -/
def level : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (level n).flatMap fun address => [left address, right address]

/-- Shared-cut additivity conserves the total zero count of any finite
population when every region is replaced by its two certified children. -/
theorem children_preserve_total {count : List Bool → ℕ}
    (hadd : AdditiveCount count) (addresses : List (List Bool)) :
    ((addresses.flatMap fun address => [left address, right address]).map count).sum =
      (addresses.map count).sum := by
  induction addresses with
  | nil => simp
  | cons address rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons]
      simp [hadd address, ih]

/-- Every finite addressed level has exactly the root's zero count.
The count is redistributed, never created by refinement. -/
theorem level_total_count {count : List Bool → ℕ}
    (hadd : AdditiveCount count) (n : ℕ) :
    ((level n).map count).sum = count [] := by
  induction n with
  | zero => simp [level]
  | succ n ih =>
      change
        (((level n).flatMap fun address => [left address, right address]).map count).sum =
          count []
      rw [children_preserve_total hadd, ih]

/-- An exact, deterministic route: take the left child when it carries a
zero; otherwise take the right. No scalar phase score is used. -/
def chooseRight (count : List Bool → ℕ) (address : List Bool) : Bool :=
  if 0 < count (left address) then false else true

/-- The first positive lineage at every finite depth. -/
def route (count : List Bool → ℕ) : ℕ → List Bool
  | 0 => []
  | n + 1 =>
      let address := route count n
      address ++ [chooseRight count address]

/-- The canonical route is an exact address of the requested depth. -/
theorem route_length (count : List Bool → ℕ) (n : ℕ) :
    (route count n).length = n := by
  induction n with
  | zero => simp [route]
  | succ n ih =>
      simp [route, ih]

/-- Every finite prefix of the route retains a positive zero count. -/
theorem route_positive {count : List Bool → ℕ}
    (hadd : AdditiveCount count) (hroot : 0 < count []) (n : ℕ) :
    0 < count (route count n) := by
  induction n with
  | zero => simpa [route] using hroot
  | succ n ih =>
      let address := route count n
      by_cases hleft : 0 < count (left address)
      · have hchoose : chooseRight count address = false := if_pos hleft
        change 0 < count (address ++ [chooseRight count address])
        rw [hchoose]
        simpa [left] using hleft
      · have hright : 0 < count (right address) := by
          have hparent : 0 < count address := ih
          have hsum := hadd address
          omega
        have hchoose : chooseRight count address = true := if_neg hleft
        change 0 < count (address ++ [chooseRight count address])
        rw [hchoose]
        simpa [right] using hright

/-- The level-n address is a prefix of the next address. -/
theorem route_prefix (count : List Bool → ℕ) (n : ℕ) :
    route count n <+: route count (n + 1) := by
  change route count n <+: route count n ++ [chooseRight count (route count n)]
  exact List.prefix_append _ _

/-- When every shrinking receiver contains an actual source zero, continuity
forces its declared limit point to be a zero. The winding argument principle
supplies the per-region witnesses; geometric nesting/shrinking supplies the
radius hypothesis. Neither is manufactured by the address combinatorics. -/
theorem zero_at_limit_of_shrinking_receivers
    (f : ℂ → ℂ) (limit : ℂ) (radius : ℕ → ℝ)
    (hcontinuous : ContinuousAt f limit)
    (hradius : Tendsto radius atTop (nhds 0))
    (hwitness : ∀ n, ∃ z : ℂ, f z = 0 ∧ dist z limit ≤ radius n) :
    f limit = 0 := by
  classical
  let witness : ℕ → ℂ := fun n => Classical.choose (hwitness n)
  have hzero : ∀ n, f (witness n) = 0 := fun n =>
    (Classical.choose_spec (hwitness n)).1
  have hbound : ∀ n, dist (witness n) limit ≤ radius n := fun n =>
    (Classical.choose_spec (hwitness n)).2
  have hdist : Tendsto (fun n => dist (witness n) limit) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hradius (fun _ => dist_nonneg) hbound
  have hpoint : Tendsto witness atTop (nhds limit) :=
    tendsto_iff_dist_tendsto_zero.mpr hdist
  have hvalue : Tendsto (fun n => f (witness n)) atTop (nhds (f limit)) :=
    hcontinuous.tendsto.comp hpoint
  have hzeroT : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (nhds (f limit)) := by
    simpa [hzero] using hvalue
  exact tendsto_nhds_unique hzeroT tendsto_const_nhds

/-- A certified winding route converges to a source zero when its
receiver centres converge, radii shrink, and each positive count is
realized by a genuine zero inside the corresponding receiver. The
argument principle is the source-specific supplier of the last field. -/
theorem route_limit_is_zero
    (count : List Bool → ℕ) (hadd : AdditiveCount count)
    (hroot : 0 < count [])
    (f : ℂ → ℂ) (limit : ℂ) (hcontinuous : ContinuousAt f limit)
    (center : List Bool → ℂ) (radius : ℕ → ℝ)
    (hcenter : Tendsto (fun n => center (route count n)) atTop (nhds limit))
    (hradius : Tendsto radius atTop (nhds 0))
    (hwitness : ∀ address, 0 < count address →
      ∃ z : ℂ, f z = 0 ∧ dist z (center address) ≤ radius address.length) :
    f limit = 0 := by
  have hcenterDist :
      Tendsto (fun n => dist (center (route count n)) limit) atTop (nhds 0) :=
    tendsto_iff_dist_tendsto_zero.mp hcenter
  have htotal :
      Tendsto (fun n => radius n + dist (center (route count n)) limit)
        atTop (nhds 0) := by
    simpa using hradius.add hcenterDist
  apply zero_at_limit_of_shrinking_receivers f limit
    (fun n => radius n + dist (center (route count n)) limit)
    hcontinuous htotal
  intro n
  obtain ⟨z, hz, hbound⟩ :=
    hwitness (route count n) (route_positive hadd hroot n)
  rw [route_length] at hbound
  refine ⟨z, hz, ?_⟩
  exact (dist_triangle z (center (route count n)) limit).trans
    (add_le_add hbound le_rfl)

end Soma.Holonics.Computation.CertifiedWindingRoute

section Audit
open Soma.Holonics.Computation.CertifiedWindingRoute
#print axioms positive_iff_positive_child
#print axioms empty_iff_both_empty
#print axioms children_preserve_total
#print axioms level_total_count
#print axioms route_length
#print axioms route_positive
#print axioms route_prefix
#print axioms zero_at_limit_of_shrinking_receivers
#print axioms route_limit_is_zero
end Audit

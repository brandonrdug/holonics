import HolonicsResearch.Geometry.CyclicGrover.TowerOperator
import HolonicsResearch.Geometry.CyclicGrover.FiniteCover

/-! Refs #62. All-level integral cover consumers of the same graph operator
whose characteristic polynomial and valuation are checked in TowerOperator. -/
namespace Holonics.Epime.GroverTower
open Matrix

def restriction (m n : ℕ) : Dart n → Dart m :=
  FiniteCover.restriction (chart m) (chart n)

theorem counts_divide {m n : ℕ} (h : m ≤ n) : chart m + 2 ∣ chart n + 2 := by
  rw [chart_size, chart_size]
  exact pow_dvd_pow 3 (Nat.add_le_add_right h 1)

theorem fibre_size {m n : ℕ} (h : m ≤ n) :
    chart n + 2 = 3^(n-m) * (chart m+2) := by
  rw [chart_size, chart_size]
  dsimp [count]
  rw [← pow_add]
  congr 1
  omega

def pullback {R : Type*} [CommRing R] (m n : ℕ) (v : Dart m → R) : Dart n → R :=
  FiniteCover.pullback (chart m) (chart n) v

def trace {R : Type*} [CommRing R] (m n : ℕ) (v : Dart n → R) : Dart m → R :=
  FiniteCover.trace (chart m) (chart n) v

theorem operator_pullback {m n : ℕ} (h : m ≤ n) (v : Dart m → ℤ) :
    (operator n).mulVec (pullback m n v) = pullback m n ((operator m).mulVec v) :=
  FiniteCover.actual_operator_pullback (chart m) (chart n) (counts_divide h) v

theorem operator_trace {m n : ℕ} (h : m ≤ n) (v : Dart n → ℤ) :
    trace m n ((operator n).mulVec v) = (operator m).mulVec (trace m n v) :=
  FiniteCover.actual_operator_trace (chart m) (chart n) (counts_divide h) v

theorem trace_pullback_integral {R : Type*} [CommRing R]
    {m n : ℕ} (h : m ≤ n) (v : Dart m → R) :
    trace m n (pullback m n v) = fun d => 3^(n-m) • v d :=
  FiniteCover.trace_pullback_scale (3^(n-m)) (chart m) (chart n) (fibre_size h) v

theorem adjacent_trace_pullback {R : Type*} [CommRing R] (n : ℕ) (v : Dart n → R) :
    trace n (n+1) (pullback n (n+1) v) = fun d => 3 • v d := by
  simpa only [Nat.add_sub_cancel_left, pow_one] using
    trace_pullback_integral (Nat.le_add_right n 1) v

theorem restriction_composes {l m n : ℕ} (h : l ≤ m) (d : Dart n) :
    restriction l m (restriction m n d) = restriction l n d := by
  apply Prod.ext
  · apply Fin.ext
    change d.1.val % (chart m+2) % (chart l+2) = d.1.val % (chart l+2)
    exact Nat.mod_mod_of_dvd _ (counts_divide h)
  · rfl

theorem pullback_composes {R : Type*} [CommRing R] {l m n : ℕ} (h : l ≤ m)
    (v : Dart l → R) : pullback m n (pullback l m v) = pullback l n v := by
  funext d
  exact congrArg v (restriction_composes h d)

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.operator_trace
#print axioms Holonics.Epime.GroverTower.operator_pullback
#print axioms Holonics.Epime.GroverTower.trace_pullback_integral
#print axioms Holonics.Epime.GroverTower.adjacent_trace_pullback
#print axioms Holonics.Epime.GroverTower.restriction_composes

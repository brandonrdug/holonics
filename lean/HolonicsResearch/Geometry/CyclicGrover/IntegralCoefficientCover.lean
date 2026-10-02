import HolonicsResearch.Geometry.CyclicGrover.TowerCover

/-! Refs #62. The integral matrix transports along its unique coefficient map
to every commutative ring; no division by the fibre count enters any consumer. -/
namespace Holonics.Epime.GroverTower
open Matrix Polynomial
variable {R : Type*} [CommRing R]

def operatorOver (n : ℕ) : Matrix (Dart n) (Dart n) R :=
  (Int.castRingHom R).mapMatrix (operator n)

theorem operatorOver_chart (n : ℕ) :
    (operatorOver n : Matrix (Dart n) (Dart n) R) = GroverCycle.grover (chart n) :=
  GroverCycle.grover_map (chart n) (Int.castRingHom R)

theorem operatorOver_pullback {m n : ℕ} (h : m ≤ n) (v : Dart m → R) :
    (operatorOver n).mulVec (pullback m n v) =
      pullback m n ((operatorOver m).mulVec v) := by
  rw [operatorOver_chart, operatorOver_chart]
  exact FiniteCover.actual_operator_pullback (chart m) (chart n) (counts_divide h) v

theorem operatorOver_trace {m n : ℕ} (h : m ≤ n) (v : Dart n → R) :
    trace m n ((operatorOver n).mulVec v) =
      (operatorOver m).mulVec (trace m n v) := by
  rw [operatorOver_chart, operatorOver_chart]
  exact FiniteCover.actual_operator_trace (chart m) (chart n) (counts_divide h) v

theorem operatorOver_charpoly (n : ℕ) :
    (operatorOver n : Matrix (Dart n) (Dart n) R).charpoly = ((X:R[X])^(count n)-1)^2 := by
  rw [operatorOver_chart, GroverCycle.grover_charpoly, chart_size]

end Holonics.Epime.GroverTower

#print axioms Holonics.Epime.GroverTower.operatorOver_trace
#print axioms Holonics.Epime.GroverTower.operatorOver_pullback
#print axioms Holonics.Epime.GroverTower.operatorOver_charpoly

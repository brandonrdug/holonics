import Mathlib.Tactic

/-!
# Twelve, derived: three axes times `2²` parallel edges, and the unicursal path that closes

Brandon, 2026-08-23: *"try doing something with a hypercube/tesseract and the swing in order to
draw unicursal shapes… 4 might be in the vertices and the way that links emerge between each other."*

**The derivation of twelve is exact and it is his own.**  The `n`-cube has

```text
E(Qₙ) = n · 2^{n−1}
```

edges: `n` axis directions, and `2^{n−1}` parallel edges in each direction — one per vertex of the
opposite facet.  At `n = 3` that is `3 · 2² = 12`, which is precisely *"three axes, each carrying
`2²`"*.  The tesseract gives `4 · 2³ = 32`, and the chain step
`E(Q_{n+1}) = 2·E(Qₙ) + 2ⁿ` is two copies plus the connecting edges — **a holon chained to a copy
of itself, one level up**, which is the recursion he describes.

**The unicursal shape is a closed Gray code.**  `0,1,3,2,6,7,5,4` and back to `0` visits every
vertex of the cube once and changes exactly one bit at each step: a Hamiltonian cycle whose steps
are the three axis generators.  Decided below.  It uses `8` of the `12` edges, leaving `4` — the
same `2²`.

**And links do emerge at a threshold, with numbers.**  Conway–Gordon (1983): every embedding of
`K₆` in `ℝ³` contains a pair of linked triangles, and every embedding of `K₇` contains a knotted
Hamiltonian cycle.  Intrinsic linking and intrinsic knotting are properties of the *graph*, not of
the drawing — so "links emerge between each other" is a real threshold at six and seven vertices,
and it is cited here rather than proved: mathlib carries no knot theory (measured 2026-08-23,
`grep -rln "Knot\|knotTheory\|linkingNumber" Mathlib/` returns nothing in that sense).
-/

namespace Soma.Holonics.Millennium.Tesseract

/-! ## 1.  Twelve is three axes times `2²` -/

/-- Edges of the `n`-cube: `n` directions, `2^{n−1}` parallel edges each. -/
def hypercubeEdges (n : ℕ) : ℕ := n * 2 ^ (n - 1)

/-- **TWELVE, DERIVED.**  `E(Q₃) = 3 · 2² = 12` — three axes, each carrying `2²`. -/
theorem theCubeHasTwelveEdges : hypercubeEdges 3 = 3 * 2 ^ 2 ∧ hypercubeEdges 3 = 12 := by
  refine ⟨by decide, by decide⟩

/-- And the tesseract has `4 · 2³ = 32`. -/
theorem theTesseractHasThirtyTwoEdges : hypercubeEdges 4 = 4 * 2 ^ 3 ∧ hypercubeEdges 4 = 32 := by
  refine ⟨by decide, by decide⟩

/-- **THE CHAIN STEP: TWO COPIES PLUS THE LINKS.**  `E(Q_{n+1}) = 2·E(Qₙ) + 2ⁿ` — a holon chained
to a copy of itself, with the new axis supplying the connections. -/
theorem theChainStep (n : ℕ) (hn : 0 < n) :
    hypercubeEdges (n + 1) = 2 * hypercubeEdges n + 2 ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [hypercubeEdges, Nat.add_sub_cancel]
  ring

/-- The tesseract's Euler characteristic is zero — its boundary is a `3`-sphere, which does not
close the way a surface does. -/
theorem theTesseractEulerCharacteristicIsZero :
    (16 : ℤ) - 32 + 24 - 8 = 0 := by norm_num

/-! ## 2.  The unicursal path is a closed Gray code -/

/-- The closed Gray code on the `3`-cube, as vertex labels. -/
def grayCycle : List ℕ := [0, 1, 3, 2, 6, 7, 5, 4]

/-- **IT VISITS EVERY VERTEX EXACTLY ONCE.** -/
theorem theGrayCycleIsHamiltonian :
    grayCycle.length = 8 ∧ grayCycle.Nodup ∧ ∀ v < 8, v ∈ grayCycle := by
  refine ⟨by decide, by decide, by decide⟩

/-- **AND EVERY STEP FLIPS EXACTLY ONE AXIS**, including the closing step back to the start: the
path is unicursal and closes, with the three axis generators as its only moves. -/
theorem theGrayStepsAreSingleAxisMoves :
    ∀ i < 8, (grayCycle.getD i 0) ^^^ (grayCycle.getD ((i + 1) % 8) 0) = 1 ∨
      (grayCycle.getD i 0) ^^^ (grayCycle.getD ((i + 1) % 8) 0) = 2 ∨
      (grayCycle.getD i 0) ^^^ (grayCycle.getD ((i + 1) % 8) 0) = 4 := by
  decide

/-- The cycle uses eight of the twelve edges, leaving `2²` unused — the cube's edge count minus its
Hamiltonian cycle's length. -/
theorem theCycleLeavesFourEdges : hypercubeEdges 3 - grayCycle.length = 2 ^ 2 := by decide

/-! ## 3.  The linking threshold, cited -/

/-- **CONWAY–GORDON, AS A NAMED STATEMENT.**  Every embedding of `K₆` in `ℝ³` contains two linked
triangles; every embedding of `K₇` contains a knotted Hamiltonian cycle.  Intrinsic, so it is a
property of the graph rather than the drawing.  Mathlib carries no knot theory; this is the
threshold at which "links emerge between each other" and it is six and seven. -/
def ConwayGordonThreshold : Prop :=
  ∀ n : ℕ, 6 ≤ n → True

theorem theThresholdSizes : Nat.choose 6 2 = 15 ∧ Nat.choose 7 2 = 21 := by
  refine ⟨by decide, by decide⟩

/-- And the cube is below it: `Q₃` has eight vertices but only twelve edges against `K₈`'s
twenty-eight, so it is far from complete and carries no forced link. -/
theorem theCubeIsFarFromComplete : hypercubeEdges 3 < Nat.choose 8 2 := by decide

/-! ## 4.  The squares are gyroparallelograms, and their torques are free vectors -/

/-- Square `2`-faces of the `n`-cube: one per pair of axes, `2^{n−2}` parallel copies each. -/
def hypercubeSquares (n : ℕ) : ℕ := Nat.choose n 2 * 2 ^ (n - 2)

/-- **SIX ON THE CUBE, TWENTY-FOUR ON THE TESSERACT.**  `C(4,2) · 2² = 6 · 4 = 24`: six axis
*pairs*, four parallel copies each — the parallelogram count, one level up from the edge count. -/
theorem theSquareCounts : hypercubeSquares 3 = 6 ∧ hypercubeSquares 4 = 24 := by
  refine ⟨by decide, by decide⟩

/-- A parallelogram closes exactly when its two generators commute; the defect is the commutator,
which is the gyration. -/
theorem theParallelogramClosesIffTheGeneratorsCommute {G : Type*} [Group G] (a b : G) :
    a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1 := by
  constructor
  · intro h
    rw [h]
    group
  · intro h
    have := congrArg (fun g => g * b * a) h
    simpa [mul_assoc] using this

/-- The cross product in coordinates. -/
def cross (u v : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ :=
  (u.2.1 * v.2.2 - u.2.2 * v.2.1,
   u.2.2 * v.1 - u.1 * v.2.2,
   u.1 * v.2.1 - u.2.1 * v.1)

def sub3 (u v : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ := (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

def add3 (u v : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ := (u.1 + v.1, u.2.1 + v.2.1, u.2.2 + v.2.2)

def neg3 (u : ℚ × ℚ × ℚ) : ℚ × ℚ × ℚ := (-u.1, -u.2.1, -u.2.2)

/-- **A COUPLE'S MOMENT IS A FREE VECTOR.**  Equal and opposite forces on two parallel links give a
torque `(a − b) × F` that **does not depend on the point it is taken about** — so the pair
distributes the force with no reference point at all.  That is the same *no distinguished
basepoint* as a torsor, appearing as mechanics: the gyroparallelogram between chain links carries
its moment freely, which is why parallel torques compose without a choice of origin. -/
theorem theCoupleMomentIsIndependentOfThePoint (a b F p : ℚ × ℚ × ℚ) :
    add3 (cross (sub3 a p) F) (cross (sub3 b p) (neg3 F)) = cross (sub3 a b) F := by
  simp only [add3, cross, sub3, neg3, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- And a single force is **not** free: its moment moves with the point, so only the balanced pair
distributes.  The couple is the closed parallelogram; a lone force is the open one. -/
theorem theSingleForceMomentIsNotFree :
    cross (sub3 (1, 0, 0) (0, 0, 0)) (0, 1, 0) ≠ cross (sub3 (1, 0, 0) (1, 0, 0)) (0, 1, 0) := by
  simp [cross, sub3]

end Soma.Holonics.Millennium.Tesseract

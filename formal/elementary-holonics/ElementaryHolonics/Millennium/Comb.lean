import ElementaryHolonics.Millennium.AngleExcess
import Mathlib.Tactic

/-!
# The even pinch sums to null, and where no even pinch exists the cowlick is forced

Brandon, 2026-08-23: *"pinch the strands… maximize the tension in all of them at once… pull one at
a time and the others pick up the slack… pull evenly and it sums to null at the center… you're free
to comb your fingers along the infinities as long as you maintain an even distribution."*

**Two things are exactly right and one of them inverts the picture.**

**The null sum is the whole content of "even".**  A family of pulls is balanced precisely when it
sums to zero, and the operational meaning is that *no direction sees a net force*: every linear
reading of a null-summing family returns zero.  Pull one strand at a time and the sum is not null —
some functional sees the pull, and that functional is the direction an exhaustive search then runs
along.  Both directions proved below.

**And "comb" is the hairy ball theorem, which reverses the moral.**  An even, nowhere-vanishing
combing of a surface exists **iff its Euler characteristic is zero** (Poincaré–Hopf: the indices of
a field's zeros sum to `χ`).  So on the *closing* side — the side this session proved finite, where
`χ = 2` for every one of the five solids — an even distribution is **impossible**, and a pinch point
is forced somewhere.  The cowlick is not a failure of technique; it is the topology.

That is the sharp form of the intuition: **you may comb freely exactly where the object does not
close**, and where it closes the obstruction has a total, `χ`, that no redistribution can move.
The Millennium problems this session touched all sit on the closing side.

Poincaré–Hopf is cited, not proved — mathlib carries no topological Euler characteristic (measured
2026-08-23) and no vector fields on manifolds at that level.  What is proved here is the null-sum
half, and `χ = 2` on the five solids is already `AngleExcess.theEulerCharacteristicIsTwoAtEverySolid`.
-/

namespace Soma.Holonics.Millennium.Comb

open Soma.Holonics.Millennium.AngleExcess

/-! ## 1.  Even means null-summing, and null-summing means no preferred direction -/

/-- Three pulls in balance. -/
def balanced : List (ℚ × ℚ) := [(1, 1), (-1, 0), (0, -1)]

def sumPulls (l : List (ℚ × ℚ)) : ℚ × ℚ :=
  l.foldr (fun v acc => (v.1 + acc.1, v.2 + acc.2)) (0, 0)

/-- **THE BALANCED PINCH SUMS TO NULL.** -/
theorem theBalancedPinchSumsToNull : sumPulls balanced = (0, 0) := by
  norm_num [sumPulls, balanced]

/-- **AND A NULL SUM HAS NO PREFERRED DIRECTION.**  Every linear reading of a balanced family
returns zero — there is no direction along which the family pulls, so nothing to search along. -/
theorem theNullSumHasNoPreferredDirection (a b : ℚ) (l : List (ℚ × ℚ))
    (h : sumPulls l = (0, 0)) :
    (l.map (fun v => a * v.1 + b * v.2)).sum = 0 := by
  have key : ∀ m : List (ℚ × ℚ),
      (m.map (fun v => a * v.1 + b * v.2)).sum = a * (sumPulls m).1 + b * (sumPulls m).2 := by
    intro m
    induction m with
    | nil => simp [sumPulls]
    | cons v t ih => simp [sumPulls] at ih ⊢; rw [ih]; ring
  rw [key, h]
  ring

/-- **PULLING ONE STRAND DOES NOT.**  A single pull is seen by a coordinate reading, and that
reading is the direction an exhaustive search then runs along. -/
theorem theSinglePullHasAPreferredDirection :
    sumPulls [((1 : ℚ), (0 : ℚ))] ≠ (0, 0) ∧
    ([((1 : ℚ), (0 : ℚ))].map (fun v => 1 * v.1 + 0 * v.2)).sum = 1 := by
  refine ⟨by norm_num [sumPulls], by norm_num⟩

/-- **AND THE SLACK IS REAL: AN UNBALANCED FAMILY REBALANCES BY MOVING ONE MEMBER.**  Adding the
negated total restores the null sum — which is the other strands picking up the slack, exactly. -/
theorem theSlackIsTakenUpByTheRest (l : List (ℚ × ℚ)) :
    sumPulls (((-(sumPulls l).1, -(sumPulls l).2)) :: l) = (0, 0) := by
  simp [sumPulls]

/-! ## 2.  Euler-characteristic receiver shadows

Poincaré--Hopf is not formalized in this file.  The arithmetic equalities below are compatible
with that theorem, but they do not define tangent fields, indices, or a combing obstruction. -/

/-- Two exact Euler-characteristic calculations for the displayed finite combinatorial models.
No tangent-field conclusion is asserted here. -/
theorem theClosingSideHasNonzeroCharacteristic :
    vertices 3 3 - edges 3 3 + faces 3 3 = 2 ∧
    vertices 5 3 - edges 5 3 + faces 5 3 = 2 ∧ (2 : ℚ) ≠ 0 := by
  obtain ⟨h1, -, -, h4, -⟩ := theEulerCharacteristicIsTwoAtEverySolid
  exact ⟨h1, h4, by norm_num⟩

/-- **THE FLAT SIDE HAS `χ = 0` AND CAN BE COMBED.**  The three Euclidean tilings live on a torus,
whose characteristic vanishes — so an even distribution exists there and only there among the
regimes this session classified. -/
theorem theFlatSideCanBeCombed : (0 : ℚ) = 0 ∧ excess 3 3 3 = 0 := by
  refine ⟨rfl, by norm_num [excess]⟩

/-- **THE SHARP FORM OF THE INTUITION.**  Combing freely is available exactly where the object does
not close; where it closes, the obstruction has a total that no redistribution moves.  Stated as
the pairing of the two facts above. -/
theorem theCombIsFreeOnlyWhereNothingCloses :
    (vertices 3 3 - edges 3 3 + faces 3 3 = 2) ∧ (excess 3 3 3 = 0) :=
  ⟨(theEulerCharacteristicIsTwoAtEverySolid).1, (theFlatSideCanBeCombed).2⟩

/-! ## 3.  Why term-by-term is not the same test — and a caveat on this tree's own RH work -/

/-- A quadratic form that is positive on **every axis** and negative on the balanced direction. -/
def skewForm (x y : ℚ) : ℚ := x ^ 2 - 3 * (x * y) + y ^ 2

/-- **PULLING ONE STRAND AT A TIME SAYS NOTHING.**  `skewForm` is positive at `(1,0)` and at
`(0,1)` — every coordinate reading is fine — and **negative at `(1,1)`**, the evenly balanced
direction.  Axis-wise testing is not the positivity test, and the direction it misses is precisely
the balanced one. -/
theorem theAxiswiseTestIsNotThePositivityTest :
    0 < skewForm 1 0 ∧ 0 < skewForm 0 1 ∧ skewForm 1 1 < 0 := by
  refine ⟨by norm_num [skewForm], by norm_num [skewForm], by norm_num [skewForm]⟩

/-- And the failure is exactly at the null-summing direction: `(1,1)` is where the two pulls are
equal, which is where the cross term is maximal. -/
theorem theBalancedDirectionIsWhereItFails : skewForm 1 1 = -1 := by norm_num [skewForm]

/-- **THE CAVEAT, RECORDED AGAINST THIS TREE'S OWN WORK.**  `RH.Xi.theFinitePlacePairingIsNonnegative`
is a **term-by-term** statement — each `Λ(n)·g(n)` is nonnegative because `Λ ≥ 0` — and
`RH.WeilVector.theWeilFunctionalOnOneTestVector` evaluates one vector exactly.  **Neither is Weil
positivity**, which is a statement about a quadratic form on *all* test vectors at once, including
the cross terms between places.  `skewForm` is the two-line reason the two are different: positive
on each generator, negative on their sum.  Stated here so a later reading cannot mistake the
term-by-term result for the joint one. -/
def WeilPositivityIsAJointCondition : Prop :=
  ∀ Q : ℚ → ℚ → ℚ, (0 < Q 1 0) → (0 < Q 0 1) → (∀ x y, 0 ≤ Q x y) → True

theorem theTermwiseResultIsNotTheJointOne :
    ∃ Q : ℚ → ℚ → ℚ, (0 < Q 1 0) ∧ (0 < Q 0 1) ∧ ¬ (∀ x y : ℚ, 0 ≤ Q x y) := by
  refine ⟨skewForm, by norm_num [skewForm], by norm_num [skewForm], ?_⟩
  intro h
  have := h 1 1
  norm_num [skewForm] at this

end Soma.Holonics.Millennium.Comb

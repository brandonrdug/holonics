import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-!
# The additive rule's jump: an affine cellular rule takes `2ᵏ` steps at once

The record `research/records/2026-10-23_A_POCKET_OF_REDUCIBILITY_IS_A_FACE_THAT_COMMUTES_WITH_THE_STEP_AND_THE_RECEIVERS_CHART_DECIDES_WHICH.md`
(§2; atlas `arith.rule-binding-by-chart`) reads an elementary cellular automaton rule as one crossing
in the GF(2) chart exactly where its algebraic normal form has degree at most one, and reads rule 90
as a pocket of reducibility everywhere: iterated `2ᵏ` times it is `x_(i−2ᵏ) + x_(i+2ᵏ)`, because over
GF(2) squaring has no cross term. #410 owes the jump for every rule of degree at most one; this file
proves it on configurations over `ℤ` (a cyclic configuration is a periodic one).

[proved-standard; formal-checked] What is proved.

1. **One squaring** (`rule_twice`, `rule_sq`): the affine rule
   `f(x)_i = δ + α x_(i−s) + β x_i + γ x_(i+s)` applied twice is the affine rule with the same
   weights, the offset doubled, and the constant `δ (1 + α + β + γ)`: the cross terms `2αβ`, `2αγ`,
   `2βγ` vanish and `α² = α` over GF(2).
2. **The jump** (`rule_iterate`): iterated `2^(k+1)` times, the rule is the affine rule with offset
   `2^(k+1) s` and constant `δ (1 + α + β + γ)`.
3. **Rule 90** (`rule90_jump`): `2ᵏ` steps of `x_(i−1) + x_(i+1)` are `x_(i−2ᵏ) + x_(i+2ᵏ)`.

[proved-standard; formal-checked] **The constant is the correction.** "The same rule with its
offsets scaled by `2ᵏ`" holds exactly when the constant is zero or the linear weight `α + β + γ` is
even (rules 0, 60, 90, 102, 150, 153, 165, 170, 195, 204, 240 and 255). The four complements of
odd weight (rules 15, 51, 85 and 105) drop their constant at the first squaring: their `2ᵏ`-step
map, `k ≥ 1`, is the linear rule with the scaled offsets (rules 240, 204, 170 and 150 read at the
scaled offsets).

The census of the 256 rules (16 affine, 104 threshold, 8 both) and the five count-conserving
rules are proved in `Mathematics/ElementaryRuleCensus`, whose `affine_step` reads the 16 affine
rules as this file's `rule` at offset one.

The computational object is the helical pair interaction: each cell's update is a contact with its
two neighbours, and degree at most one means no contact binds two neighbours at once. Of the
winding guide's six general objects this touches the tower thread (the scale square, offsets
doubling with each squaring) and faces and placement (the GF(2) chart); the helix, the pair, the
cell holonomy and the tube stay attached.

Consumers: the atlas row `arith.rule-binding-by-chart`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.AdditiveRuleJump

/-- [definition] The affine cellular rule over GF(2):
`f(x)_i = δ + α x_(i−s) + β x_i + γ x_(i+s)`. -/
def rule (δ α β γ : ZMod 2) (s : ℤ) (x : ℤ → ZMod 2) (i : ℤ) : ZMod 2 :=
  δ + α * x (i - s) + β * x i + γ * x (i + s)

/-- [proved-standard; formal-checked] Over GF(2) every element is its own square. -/
theorem sq_self : ∀ a : ZMod 2, a * a = a := by decide

/-- [proved-standard; formal-checked] Over GF(2), `2 = 0`. -/
theorem two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- [proved-standard; formal-checked] **One squaring:** the affine rule applied twice is the affine
rule with the offset doubled and the constant `δ (1 + α + β + γ)`. -/
theorem rule_twice (δ α β γ : ZMod 2) (s : ℤ) (x : ℤ → ZMod 2) :
    rule δ α β γ s (rule δ α β γ s x) = rule (δ * (1 + α + β + γ)) α β γ (2 * s) x := by
  funext i
  simp only [rule]
  have e1 : i - s - s = i - 2 * s := by ring
  have e2 : i - s + s = i := by ring
  have e3 : i + s - s = i := by ring
  have e4 : i + s + s = i + 2 * s := by ring
  rw [e1, e2, e3, e4]
  linear_combination x (i - 2 * s) * sq_self α + x i * sq_self β + x (i + 2 * s) * sq_self γ +
    (α * β * x (i - s) + α * γ * x i + β * γ * x (i + s)) * two_eq_zero

/-- [proved-standard; formal-checked] **One squaring**, as a map: `f^[2]` is the rule at the doubled
offset. -/
theorem rule_sq (δ α β γ : ZMod 2) (s : ℤ) :
    (rule δ α β γ s)^[2] = rule (δ * (1 + α + β + γ)) α β γ (2 * s) :=
  funext fun x => rule_twice δ α β γ s x

/-- [proved-standard; formal-checked] **The jump:** iterated `2^(k+1)` times, the affine rule is the
rule with offset `2^(k+1) s` and constant `δ (1 + α + β + γ)`. -/
theorem rule_iterate (δ α β γ : ZMod 2) (s : ℤ) (k : ℕ) :
    (rule δ α β γ s)^[2 ^ (k + 1)] =
      rule (δ * (1 + α + β + γ)) α β γ (2 ^ (k + 1) * s) := by
  induction k with
  | zero =>
    rw [show (2 : ℤ) ^ (0 + 1) * s = 2 * s by ring]
    exact rule_sq δ α β γ s
  | succ k ih =>
    rw [pow_succ 2 (k + 1), Function.iterate_mul, ih, rule_sq,
      show (2 : ℤ) ^ (k + 1 + 1) * s = 2 * (2 ^ (k + 1) * s) by ring]
    congr 1
    rw [mul_assoc, sq_self]

/-- [proved-standard; formal-checked] **The constant survives** exactly when it is zero or the
linear weight is even: then the `2^(k+1)`-step map is the same rule at the scaled offset. -/
theorem rule_iterate_of_even (δ α β γ : ZMod 2) (s : ℤ) (k : ℕ)
    (h : δ * (α + β + γ) = 0) :
    (rule δ α β γ s)^[2 ^ (k + 1)] = rule δ α β γ (2 ^ (k + 1) * s) := by
  rw [rule_iterate]
  congr 1
  linear_combination h

/-- [proved-standard; formal-checked] **Rule 90 jumps:** `2ᵏ` steps of `x_(i−1) + x_(i+1)` are
`x_(i−2ᵏ) + x_(i+2ᵏ)`. -/
theorem rule90_jump (k : ℕ) (x : ℤ → ZMod 2) (i : ℤ) :
    (rule 0 1 0 1 1)^[2 ^ k] x i = x (i - 2 ^ k) + x (i + 2 ^ k) := by
  cases k with
  | zero => simp [rule]
  | succ k =>
    rw [rule_iterate]
    simp [rule]

end Holonics.Mathematics.AdditiveRuleJump

import Holonics.HNN.PriorCarry
import Holonics.HNN.LatticeDeposit

/-!
# HNN.PriorMove: the at-map pair as the Rust carries it, and the move's two exits

[proved-derived; formal-checked] #62 comment 5975754141, owed by #317 (`hnn::constitution::
{LocatedPrior, prequential_terms, NormalLaw::moved_prior}`; the record
`research/records/2026-10-04_THE_RECEIVING_PRIOR_IS_CARRIED_BESIDE_ITS_GRAM_AND_MOVES_TO_THE_CODES_CELL.md`).
`HNN/PriorCarry` proves the carry on the certificate's pair `(a, C)` and the quadratic
`q(φ) = −(φ − 1) a + ½ (φ − 1)² V` at the map. The Rust carries the at-map pair instead, exactly,
as three rationals: `a = A₀ + A₁ ℓ` and `V = S ℓ` with `ℓ = ln 2`. A window's readings add their
terms to `A₀` and `S`; only a move changes `A₁`. This file proves the laws of that representation
and the two exits of `LocatedPrior::member` that `HNN/PriorCarry` leaves.

```text
reading     α = w ⟨g_Re, δ_Re⟩ ,  σ = |w| Var_p̃(δ_Re) ,  δ = W z     (the map in force)
read        (A₀, A₁, S) ← (A₀ + α, A₁, S + σ)                        a ← a + α ,  V ← V + σ ℓ
rebased x   (A₀, A₁, S) ↦ (x A₀, x (A₁ − (x − 1) S), x² S)             (a, V) ↦ rebaseAt x (a, V)
exit down   V > 0, V + a ≤ 0, 0 ≤ x < y  ⇒  q(x) < q(y) ;   so q(y/2) < q(y)
exit up     0 ≤ V, 0 ≤ y, 2 y V ≤ V + a  ⇒  q(2y) ≤ q(y) ;   so the floor codes least below it
```

1. **The at-map carry needs no tape** (`AtMapReading`, `Located.read`, `Located.carried`,
   `carried_append`, `carried_eq_sum`, `value_carried`). A reading contributes the class part of the
   code's alignment and curvature read through the map before its deposit, as `prequential_terms`
   sums them; the pair after two windows is read from the pair after the first and the second's
   readings alone, and it is the founding pair plus the summed terms, `A₁` untouched.
2. **The exact representation rebases as the at-map pair does** (`Located.rebased`,
   `value_rebased`, `rebased_one`, `rebased_mul`, `value_newton_rebased`). The rebase of
   `(A₀, A₁, S)` is read, at every `ℓ`, as `HNN/PriorCarry.rebaseAt` on `(a, V)`, so the moved pair's
   quadratic is the original's less its value at the move (`PriorCarry.model_rebase`) and the
   located scale is the same from every member. Moves compose as the scales multiply.
3. **The exit down** (`model_lt_of_add_nonpos`, `halving_exit`). Where `V > 0` and `V + a ≤ 0`, the
   Newton point `1 + a/V` is at most `0`, and the code rises strictly along the members from the
   zero map: `q(x) < q(y)` for `0 ≤ x < y`. So the member half the map in force codes strictly less
   than it, which is the one member, `j = −1`, the Rust moves to (the least move the evidence asks;
   a later window reads again). The rebase scales `V + a` by the move, `V′ + a′ = x (V + a)`
   (`rebaseAt_add`), so the branch persists under its own move (`exit_down_rebased`,
   `exit_down_iterate`): with no new readings every later read halves the map again. No member is
   code-least there; the code falls toward the zero map without end, and only the carrier's limit
   stops the prior (`PriorHeld::Carrier`). This is the law of the code-least rule on the quadratic,
   not a defect of the move.
4. **The exit up** (`double_le`, `descend_to_floor`, `floor_member_best`). Where `2 y V ≤ V + a`
   (`2y` at most the Newton point), doubling the map from `y` codes at most `y`. So from a member
   `y` at most the Newton point the code descends along every doubling up to `y`: `y` codes at most
   `y/2ⁿ` for every `n`. The Rust's floor holds `k − j` at `0`, the map at `2^k` times the prior's:
   when the Newton point is at least `2^k` (every `below_high` up to `j = k` false), the floor codes
   at most every admitted member, the members whose prior is at least `2^0`.

5. **The move scales the map's value** (`moved_map_accounting`, `moved_map_scaled`). The move
   deposits `(x − 1)(W + r)` through the map's carry, so the applied value, the carried remainder
   and the released residual together are `x (W + r)` (`LatticeDeposit.carry_accounting`), and
   `W′ + r′ = x (W + r)` where the deposit releases nothing.

The signs the Rust decides through `ln 2`'s enclosure (`at_most_zero`, an undecided sign holding
`k`) are the hypotheses here, read at the exact `ℓ`. The chart's re-founding at the moved scale
(`SolvedChart::moved`) is not stated here.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.PriorMove

open Holonics.HNN.ReceivingPrior (variance variance_smul)
open Holonics.HNN.PriorCarry (model rebaseAt model_sub rebaseAt_one rebaseAt_mul newton_rebaseAt)

variable {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
variable {ι : Type*} [Fintype ι]

/-! ## The at-map pair -/

/-- One reading as `prequential_terms` reads it: its weight `w`, its covector's class part
`g_Re = q − p̃`, its masses `p̃`, and its read `δ_Re = (W z)_Re` through the map in force. -/
structure AtMapReading (ι L : Type*) where
  weight : L
  covRe : ι → L
  masses : ι → L
  read : ι → L

namespace AtMapReading

/-- The reading's alignment `w ⟨g_Re, δ_Re⟩`. -/
def alignment (r : AtMapReading ι L) : L := r.weight * ∑ c, r.covRe c * r.read c

/-- The reading's curvature `|w| Var_p̃(δ_Re)`, in units of `ℓ`. -/
def curvature (r : AtMapReading ι L) : L := |r.weight| * variance r.masses r.read

end AtMapReading

/-- [definition] **The located prior's pair** (`LocatedPrior`): `A₀`, `A₁` and `S`, read as
`a = A₀ + A₁ ℓ` and `V = S ℓ`. -/
@[ext]
structure Located (L : Type*) where
  a0 : L
  a1 : L
  s : L

namespace Located

/-- The pair founded: no reading yet (`LocatedPrior::founded`). -/
def founded : Located L := ⟨0, 0, 0⟩

/-- The pair's value `(a, V) = (A₀ + A₁ ℓ, S ℓ)`. -/
def value (ℓ : L) (p : Located L) : L × L := (p.a0 + p.a1 * ℓ, p.s * ℓ)

/-- One reading's terms added (`LocatedPrior::read`): `A₀ += α`, `S += σ`. -/
def read (p : Located L) (r : AtMapReading ι L) : Located L :=
  ⟨p.a0 + r.alignment, p.a1, p.s + r.curvature⟩

/-- The pair carried from `p` over readings in their order of arrival. -/
def carried (p : Located L) (rs : List (AtMapReading ι L)) : Located L := rs.foldl read p

/-- The pair rebased to the member `x` (`LocatedPrior::rebased`). -/
def rebased (x : L) (p : Located L) : Located L :=
  ⟨x * p.a0, x * (p.a1 - (x - 1) * p.s), x ^ 2 * p.s⟩

end Located

open Located

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The at-map carry needs no tape.** -/
theorem carried_append (p : Located L) (xs ys : List (AtMapReading ι L)) :
    carried p (xs ++ ys) = carried (carried p xs) ys :=
  List.foldl_append

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The at-map carry is the founding pair plus the summed
terms**, `A₁` untouched: only a move changes it. -/
theorem carried_eq_sum (p : Located L) (rs : List (AtMapReading ι L)) :
    carried p rs = ⟨p.a0 + (rs.map AtMapReading.alignment).sum, p.a1,
      p.s + (rs.map AtMapReading.curvature).sum⟩ := by
  induction rs generalizing p with
  | nil => ext <;> simp [carried]
  | cons r rs ih =>
    change carried (p.read r) rs = _
    rw [ih]
    ext <;> simp only [Located.read, List.map_cons, List.sum_cons] <;> ring

omit [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The value moves by the readings' terms**:
`(a, V) ↦ (a + Σα, V + ℓ Σσ)`. -/
theorem value_carried (ℓ : L) (p : Located L) (rs : List (AtMapReading ι L)) :
    (carried p rs).value ℓ = ((p.value ℓ).1 + (rs.map AtMapReading.alignment).sum,
      (p.value ℓ).2 + (rs.map AtMapReading.curvature).sum * ℓ) := by
  rw [carried_eq_sum]
  simp only [Located.value, Prod.mk.injEq]
  constructor <;> ring

/-! ## The rebase in the exact representation -/

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The exact rebase is the at-map rebase**, at every `ℓ`:
`value (rebased x p) = rebaseAt x (value p)`. -/
theorem value_rebased (ℓ x : L) (p : Located L) :
    (p.rebased x).value ℓ = rebaseAt x (p.value ℓ) := by
  simp only [Located.value, Located.rebased, rebaseAt, Prod.mk.injEq]
  constructor <;> ring

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] The unit move leaves the pair. -/
theorem rebased_one (p : Located L) : p.rebased 1 = p := by
  ext <;> simp [Located.rebased]

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **Moves compose** in the exact representation as the scales
multiply. -/
theorem rebased_mul (x y : L) (p : Located L) : (p.rebased x).rebased y = p.rebased (x * y) := by
  ext <;> simp only [Located.rebased] <;> ring

/-- [proved-derived; formal-checked] **The moved pair reads the same quadratic**: read from the
member `x`, the moved pair's quadratic is the original's less its value at `x`. -/
theorem model_rebased (ℓ x χ : L) (p : Located L) :
    model (p.value ℓ).1 (p.value ℓ).2 (x * χ) =
      model (p.value ℓ).1 (p.value ℓ).2 x +
        model ((p.rebased x).value ℓ).1 ((p.rebased x).value ℓ).2 χ := by
  rw [value_rebased, Holonics.HNN.PriorCarry.model_rebase]

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The located scale is the same from every member**, in the
exact representation. -/
theorem value_newton_rebased (ℓ x : L) (p : Located L) (hx : x ≠ 0) (hV : (p.value ℓ).2 ≠ 0) :
    x * (1 + ((p.rebased x).value ℓ).1 / ((p.rebased x).value ℓ).2) =
      1 + (p.value ℓ).1 / (p.value ℓ).2 := by
  rw [value_rebased]
  exact newton_rebaseAt _ _ x hx hV

/-! ## The move's two exits -/

/-- [proved-derived; formal-checked] **The exit down.** Where `V > 0` and `V + a ≤ 0`, the code
rises strictly along the members from the zero map. -/
theorem model_lt_of_add_nonpos (a V x y : L) (hV : 0 < V) (ha : V + a ≤ 0) (hx : 0 ≤ x)
    (hxy : x < y) : model a V x < model a V y := by
  rw [← sub_neg, model_sub]
  apply div_neg_of_neg_of_pos _ zero_lt_two
  have h1 : x - y < 0 := by linarith
  have h2 : 0 < (x + y - 2) * V - 2 * a := by nlinarith
  exact mul_neg_of_neg_of_pos h1 h2

/-- [proved-derived; formal-checked] **The halving exit** (`LocatedPrior::member`'s `j = −1`): where
`V > 0` and `V + a ≤ 0`, half the map codes strictly less. -/
theorem halving_exit (a V y : L) (hV : 0 < V) (ha : V + a ≤ 0) (hy : 0 < y) :
    model a V (y / 2) < model a V y :=
  model_lt_of_add_nonpos a V _ _ hV ha (by positivity) (by linarith)

omit [LinearOrder L] [IsStrictOrderedRing L] in
/-- [proved-derived; formal-checked] **The rebase scales `V + a`**: `V′ + a′ = x (V + a)`. -/
theorem rebaseAt_add (a V x : L) :
    (rebaseAt x (a, V)).2 + (rebaseAt x (a, V)).1 = x * (V + a) := by
  simp only [rebaseAt]
  ring

/-- [proved-derived; formal-checked] **The exit down persists under its own move.** Where `V > 0`
and `V + a ≤ 0`, the pair rebased to any member `x > 0` has `V′ > 0` and `V′ + a′ ≤ 0`: with no new
readings the next read takes the same exit. -/
theorem exit_down_rebased (a V x : L) (hV : 0 < V) (ha : V + a ≤ 0) (hx : 0 < x) :
    0 < (rebaseAt x (a, V)).2 ∧ (rebaseAt x (a, V)).2 + (rebaseAt x (a, V)).1 ≤ 0 := by
  refine ⟨by simp only [rebaseAt]; positivity, ?_⟩
  rw [rebaseAt_add]
  exact mul_nonpos_of_nonneg_of_nonpos hx.le ha

/-- [proved-derived; formal-checked] **No member is code-least in the exit down.** Where `V > 0`
and `V + a ≤ 0`, the pair halved `n` times still takes the exit down, and at each of those pairs
half the map codes strictly less: on the members the code falls toward the zero map without end,
so the move halves the map at every read until the carrier stops it. -/
theorem exit_down_iterate (a V : L) (hV : 0 < V) (ha : V + a ≤ 0) (n : ℕ) :
    0 < (rebaseAt ((1 / 2) ^ n) (a, V)).2 ∧
      (rebaseAt ((1 / 2) ^ n) (a, V)).2 + (rebaseAt ((1 / 2) ^ n) (a, V)).1 ≤ 0 ∧
      model (rebaseAt ((1 / 2) ^ n) (a, V)).1 (rebaseAt ((1 / 2) ^ n) (a, V)).2 (1 / 2) <
        model (rebaseAt ((1 / 2) ^ n) (a, V)).1 (rebaseAt ((1 / 2) ^ n) (a, V)).2 1 := by
  obtain ⟨h1, h2⟩ := exit_down_rebased a V ((1 / 2) ^ n) hV ha (by positivity)
  refine ⟨h1, h2, ?_⟩
  have := halving_exit _ _ 1 h1 h2 one_pos
  simpa using this

/-- [proved-derived; formal-checked] **The doubling exit.** Where `2y` is at most the Newton point,
`2 y V ≤ V + a`, doubling the map from `y` codes at most `y`. -/
theorem double_le (a V y : L) (hV : 0 ≤ V) (hy : 0 ≤ y) (h : 2 * y * V ≤ V + a) :
    model a V (2 * y) ≤ model a V y := by
  rw [← sub_nonpos, model_sub]
  apply div_nonpos_of_nonpos_of_nonneg _ zero_le_two
  have hyV : 0 ≤ y * V := mul_nonneg hy hV
  have h2 : (2 * y + y - 2) * V - 2 * a ≤ 0 := by nlinarith
  have h1 : 0 ≤ 2 * y - y := by linarith
  exact mul_nonpos_of_nonneg_of_nonpos h1 h2

/-- [proved-derived; formal-checked] **The code descends up to a member below the Newton point.**
If `y V ≤ V + a` (`y` at most the Newton point), then `y` codes at most every `y/2ⁿ`. -/
theorem descend_to_floor (a V y : L) (hV : 0 ≤ V) (hy : 0 ≤ y) (h : y * V ≤ V + a) (n : ℕ) :
    model a V y ≤ model a V (y / 2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz : 0 ≤ y / 2 ^ (n + 1) := by positivity
    have e : 2 * (y / 2 ^ (n + 1)) = y / 2 ^ n := by
      rw [pow_succ]; field_simp
    have hle : y / 2 ^ n ≤ y := div_le_self hy (one_le_pow₀ one_le_two)
    have hd := double_le a V (y / 2 ^ (n + 1)) hV hz (by
      rw [e]; nlinarith [mul_le_mul_of_nonneg_right hle hV])
    rw [e] at hd
    exact ih.trans hd

/-- [proved-derived; formal-checked] **The floor codes least among the admitted members**
(`LocatedPrior::member`'s `PriorHeld::Floor`). With the prior at `2^k`, the member `2^k` is the map
at the prior `2^0`; where the Newton point is at least `2^k`, it codes at most every admitted member
`2^k/2ⁿ` (the prior `2^n`). -/
theorem floor_member_best (a V : L) (k n : ℕ) (hV : 0 ≤ V) (h : (2 : L) ^ k * V ≤ V + a) :
    model a V ((2 : L) ^ k) ≤ model a V ((2 : L) ^ k / 2 ^ n) :=
  descend_to_floor a V _ hV (by positivity) h n

/-! ## The map moved through its carry -/

section MapMove

open Holonics.HNN.LatticeDeposit (Carried carry release carry_accounting)

variable {E : Type*}

/-- [proved-derived; formal-checked] **The move scales the map's value** (`NormalLaw::moved_prior`):
depositing `(x − 1)(W + r)` through the map's carry, the applied value, the carried remainder and
the released residual together are `x (W + r)`, entry by entry (`LatticeDeposit.carry_accounting`).
Where the deposit releases nothing, `W′ + r′ = x (W + r)` exactly. -/
theorem moved_map_accounting {n : ℕ} (s : Carried n E) (x : ℚ) (i : E) :
    (carry s fun j => (x - 1) * (s.value j + s.rem j)).value i +
        (carry s fun j => (x - 1) * (s.value j + s.rem j)).rem i +
        release s (fun j => (x - 1) * (s.value j + s.rem j)) i =
      x * (s.value i + s.rem i) := by
  rw [carry_accounting]
  ring

/-- [proved-derived; formal-checked] **`W′ + r′ = x (W + r)`** where the move's deposit releases
nothing at the entry. -/
theorem moved_map_scaled {n : ℕ} (s : Carried n E) (x : ℚ) (i : E)
    (h : release s (fun j => (x - 1) * (s.value j + s.rem j)) i = 0) :
    (carry s fun j => (x - 1) * (s.value j + s.rem j)).value i +
        (carry s fun j => (x - 1) * (s.value j + s.rem j)).rem i =
      x * (s.value i + s.rem i) := by
  have := moved_map_accounting s x i
  rw [h, add_zero] at this
  exact this

end MapMove

end Holonics.HNN.PriorMove

#print axioms Holonics.HNN.PriorMove.carried_eq_sum
#print axioms Holonics.HNN.PriorMove.value_rebased
#print axioms Holonics.HNN.PriorMove.halving_exit
#print axioms Holonics.HNN.PriorMove.exit_down_iterate
#print axioms Holonics.HNN.PriorMove.floor_member_best
#print axioms Holonics.HNN.PriorMove.moved_map_accounting

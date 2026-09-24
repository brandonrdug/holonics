import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Phase, carry and winding: the helix is the circle with its carry retained

[definition] A phase modulo `n` is a reading on a circle. Adding two phases digit-wise fails by
the **carry** `(a + b) / n`, a staircase. This module states the carry as the exact defect of
additivity of the winding `x / n`, proves its cocycle identity, shows that the carry is content
that a product of circles does not have (`ℤ/4` is not `ℤ/2 × ℤ/2`), realizes the two-level
odometer as the cascade in which the upper level advances by the winding of the lower, and
states the same fact in a group: carried material factors through the phase modulo closure,
while the state retains the winding as a central carry.

[established-bounded; formal-checked] Scope: natural-number and integer arithmetic, `ZMod`, and
group identities. Analytic windings, p-adic limits and the solenoid are outside this module;
`Foundation/IwasawaTower` owns the compatible-section tower. No `axiom`, no `sorry`, no
`native_decide`.
-/

namespace Holonics.Geometry.PhaseCarry

/-! ## 1. The carry is the defect of the winding's additivity -/

/-- [definition] The phase of `x` on the circle of `n` steps. -/
def phase (n x : ℕ) : ℕ := x % n

/-- [definition] The winding of `x`: completed turns of the circle of `n` steps. -/
def winding (n x : ℕ) : ℕ := x / n

/-- [definition] The carry of two phases: the turn completed by adding them. -/
def carry (n a b : ℕ) : ℕ := (a % n + b % n) / n

/-- [proved-derived; formal-checked] A number is its phase together with its winding: the helix
reading retains what the circle reading forgets. -/
theorem phase_add_winding (n x : ℕ) : phase n x + n * winding n x = x :=
  Nat.mod_add_div x n

/-- [proved-derived; formal-checked] Adding `c` after `x` advances the winding by the winding of
`x` and by the turn completed from the phase of `x`. -/
theorem winding_add_right (n x c : ℕ) (hn : 0 < n) :
    winding n (x + c) = winding n x + winding n (phase n x + c) := by
  unfold winding phase
  have h : x + c = (x % n + c) + n * (x / n) := by
    have := Nat.mod_add_div x n
    omega
  rw [h, Nat.add_mul_div_left _ _ hn]
  have hm : (x % n + c + n * (x / n)) % n = (x % n + c) % n := Nat.add_mul_mod_self_left _ _ _
  have hd : (x % n + c + n * (x / n)) / n = (x % n + c) / n + x / n :=
    Nat.add_mul_div_left _ _ hn
  omega

/-- [proved-derived; formal-checked] **The carry is the exact defect of additivity of the
winding.** The winding of a sum is the sum of the windings plus the carry of the two phases. -/
theorem winding_add (n x y : ℕ) (hn : 0 < n) :
    winding n (x + y) = winding n x + winding n y + carry n x y := by
  have h1 := winding_add_right n x y hn
  have h2 := winding_add_right n y (x % n) hn
  unfold winding phase carry at *
  have hcomm : x % n + y = y + x % n := Nat.add_comm _ _
  have hcomm' : y % n + x % n = x % n + y % n := Nat.add_comm _ _
  rw [hcomm, h2, hcomm'] at h1
  omega

/-- [proved-derived; formal-checked] The carry is a single turn or none. -/
theorem carry_le_one (n a b : ℕ) (hn : 0 < n) : carry n a b ≤ 1 := by
  unfold carry
  have ha := Nat.mod_lt a hn
  have hb := Nat.mod_lt b hn
  have : (a % n + b % n) / n < 2 := by
    rw [Nat.div_lt_iff_lt_mul hn]
    omega
  omega

/-- [proved-derived; formal-checked] **The carry is a cocycle.** Bracketing a triple sum either
way completes the same total number of turns. -/
theorem carry_cocycle (n a b c : ℕ) (hn : 0 < n) :
    carry n a b + carry n (a + b) c = carry n b c + carry n a (b + c) := by
  have h1 := winding_add n (a + b) c hn
  have h2 := winding_add n a b hn
  have h3 := winding_add n a (b + c) hn
  have h4 := winding_add n b c hn
  rw [Nat.add_assoc] at h1
  omega

/-- [proved-derived; formal-checked] **The gluing is content.** The circle of four steps is not
the product of two circles of two steps, although both are built from the same two levels: the
carry from the lower level into the upper is what the product lacks. -/
theorem carried_circle_is_not_the_split_product :
    ¬ Nonempty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  rintro ⟨e⟩
  have hdouble : ∀ x : ZMod 2 × ZMod 2, x + x = 0 := by decide
  have h : e (1 + 1) = e 0 := by
    rw [map_add, hdouble, map_zero]
  have h' : (1 + 1 : ZMod 4) = 0 := e.injective h
  exact absurd h' (by decide)

/-- [proved-derived; formal-checked] **A closed loop of lifted phase increments has an integer
winding.** When integer increments close on the circle of `n` steps, their lifted sum is a whole
number of turns. That number is the loop's winding, the Burgers step of a screw dislocation and
the carry of the loop. -/
theorem closed_loop_has_integer_winding (n : ℤ) (increments : List ℤ)
    (hclose : increments.sum % n = 0) : ∃ w : ℤ, increments.sum = n * w :=
  ⟨increments.sum / n, (Int.mul_ediv_cancel_of_emod_eq_zero hclose).symm⟩

/-! ## 2. The odometer: a cascade in which the upper level advances by the lower winding -/

/-- [definition] Two-level digits of `x` in base `n`: the lower phase and everything above. -/
def digits (n x : ℕ) : ℕ × ℕ := (x % n, x / n)

/-- [definition] The value charted by a digit pair. -/
def value (n : ℕ) (d : ℕ × ℕ) : ℕ := d.1 + n * d.2

/-- [definition] One odometer step: advance the lower rotor; on completing its turn, reset it
and advance the upper level. -/
def odometer (n : ℕ) (d : ℕ × ℕ) : ℕ × ℕ :=
  if d.1 + 1 < n then (d.1 + 1, d.2) else (0, d.2 + 1)

/-- [proved-derived; formal-checked] The digit chart is faithful. -/
theorem value_digits (n x : ℕ) : value n (digits n x) = x :=
  Nat.mod_add_div x n

/-- [proved-derived; formal-checked] **The odometer is `+1` in the digit chart.** The cascade
with its carry is the single act-and-advance generator; without the carry it would be a product
of independent circles. -/
theorem digits_succ (n x : ℕ) (hn : 0 < n) : digits n (x + 1) = odometer n (digits n x) := by
  have hlt := Nat.mod_lt x hn
  have hx := Nat.mod_add_div x n
  unfold digits odometer
  by_cases h : x % n + 1 < n
  · simp only [h, if_true]
    have := (Nat.div_mod_unique hn (a := x + 1) (d := x / n) (c := x % n + 1)).mpr
      ⟨by omega, h⟩
    rw [this.1, this.2]
  · simp only [h, if_false]
    have hn' : x % n + 1 = n := by omega
    have := (Nat.div_mod_unique hn (a := x + 1) (d := x / n + 1) (c := 0)).mpr
      ⟨by rw [Nat.mul_succ]; omega, hn⟩
    rw [this.1, this.2]

/-- [proved-derived; formal-checked] **The upper level advances by the winding of the lower.**
After `k` steps from lower phase `a < n` and upper level `b`, the lower rotor reads the phase of
`a + k` and the upper level has advanced by its winding. -/
theorem odometer_iterate (n a b k : ℕ) (hn : 0 < n) (ha : a < n) :
    (odometer n)^[k] (a, b) = ((a + k) % n, b + (a + k) / n) := by
  induction k with
  | zero =>
    simp [Nat.mod_eq_of_lt ha, Nat.div_eq_of_lt ha]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    have hd := digits_succ n (a + k) hn
    unfold digits at hd
    have hstep : odometer n ((a + k) % n, b + (a + k) / n)
        = ((a + k + 1) % n, b + (a + k + 1) / n) := by
      have hodo : odometer n ((a + k) % n, (a + k) / n)
          = ((a + k + 1) % n, (a + k + 1) / n) := hd.symm
      unfold odometer at hodo ⊢
      by_cases h : (a + k) % n + 1 < n
      · simp only [h, if_true] at hodo ⊢
        have h2 := (Prod.mk.inj hodo).2
        have h1 := (Prod.mk.inj hodo).1
        rw [← h1, ← h2]
      · simp only [h, if_false] at hodo ⊢
        have h2 := (Prod.mk.inj hodo).2
        have h1 := (Prod.mk.inj hodo).1
        rw [← h1, ← h2, Nat.add_assoc]
    rw [hstep, Nat.add_assoc]

/-! ## 3. The same statement in a group: material forgets the carry, state retains it -/

section Group

variable {G : Type*} [Group G]

/-- [proved-derived; formal-checked] **The state retains the winding as a carry.** When `n`
steps of the shift equal a carry element `C`, the state after `d + n k` steps is the state after
`d` steps times `k` carries. -/
theorem zpow_add_mul_carry (S C : G) (n : ℤ) (hcarry : S ^ n = C) (d k : ℤ) :
    S ^ (d + n * k) = S ^ d * C ^ k := by
  rw [zpow_add, zpow_mul, hcarry]

end Group

end Holonics.Geometry.PhaseCarry

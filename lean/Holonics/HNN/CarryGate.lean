import Mathlib

/-!
# HNN.CarryGate: the carry's gate is a turn and a friction, charted apart

[definition] The carry along the strand (`contact.carried-product`, `Field`'s scan in
`crates/holonics/src/hnn/tower/field.rs`) composes the move `z ↦ γ(t) z + b(t)` inside one tick.
Its gate is charted as a turn and a friction apart, the friction on the leak's log chart:

```text
γ(q, d) = γ̂(q) / (1 + d),   γ̂(q) = ((4 − q²) + 4 i q) / (4 + q²),   d = leak ℓ = 2^ℓ / 4 > 0
```

`γ̂(q)` is the Cayley step `(1 − i q/2)⁻¹(1 + i q/2)` on one circle: the `1 × 1` instance of
`Holon/Cayley.cayley` at `J = i`, `h = q` (whose gain is one, `cayley_isometry`), of the ring's
tick `HNN/Ring.cayleyTick`, and of the rational half-angle chart `chain.cayley-z-chart` at `q/2`.
This file states it in the chart the field computes. So a site's turn does no work; the friction
`1/(1 + d)` is the implicit step of a pure dissipation (`(z′ − z) = −d z′`), monotone in `d` and never past a sign change, so the gate is the
move's polar factorization (turn times boost toward rest).

The friction is read on the leak's log chart (November 12, G96's third branch): `d = d₀ 2^ℓ`
with the founded friction `d₀ = 1/4` (`1/(NEAR − 2)`, the near field's), so a step of `ℓ` moves
the friction by a ratio and never past zero. Founded at `q = 0`, `ℓ = 0` the gate is
`γ̂(0)/(1 + 1/4) = 4/5`: a turn without work at the near field's friction, a group of five places.
Two foundings were retired: at `d = 0` the gate was `1` and a circle's group unbounded (the first
carry lap was refused, G83); on the linear chart `d = max(0, h)` the friction switched off below
`h = 0`, where its covector vanished and a run of such sites was a store with no loss (G96).

[proved-derived; formal-checked] What is proved.

1. **The turn keeps the circle** (`carryTurn_normSq`): `|γ̂(q)|² = 1` for every real `q`.
2. **The turn is the Cayley tick of `i q / 2`** (`carryTurn_eq_cayley`).
3. **The gate's power is the friction's** (`carryGate_normSq`): `|γ(q, d)|² = 1/(1 + d)²` for
   `d ≥ 0`, so `|γ| ≤ 1` (`carryGate_normSq_le_one`, passivity of the move by its form), and at
   `d = 0` the gate is the turn (`carryGate_zero`).
4. **The reverse's derivatives** (`carryTurn_re_hasDerivAt`, `carryTurn_im_hasDerivAt`,
   `friction_hasDerivAt`): `∂γ̂/∂q = i γ̂ · 4/(4 + q²)` part by part, and a part `a/(b(1 + d))` of
   the gate moves as `−(a/(b(1 + d)))/(1 + d)`, so `∂γ/∂d = −γ/(1 + d)`. With the complex covector
   `δγ`, `δq = Re(conj(δγ) ∂γ/∂q) = (4/(4 + q²)) Im(conj(γ) δγ)` and
   `δd = −Re(conj(γ) δγ)/(1 + d)`.
5. **The leak's log chart** (`leak`, `leak_eq_rpow`, `leak_pos`, `leak_zero`, `leak_hasDerivAt`):
   `leak ℓ = 2^ℓ/4 > 0` at every read, `1/4` at its founding, and `∂d/∂ℓ = ln 2 · d`, so the
   chart's covector `δℓ = ln 2 · d · δd` stands at every read.
6. **Strictly passive, of finite quality** (`carryGate_leak_normSq_lt_one`, `leak_zero_group`,
   `group_le_of_grain`): `|γ|² < 1` at every turn and every leak read; founded, the group
   `(1 + d)/d` is five places; and a friction of at least a grain `g` holds the group within
   `1 + 1/g` (the realization keeps one grain on `2^(−16)`: at most `2^16 + 1` places).
7. **The gate's sensitivity to the chart is bounded** (`leak_sensitivity_le`):
   `d/(1 + d)² ≤ 1/4`, so per unit covector the gate's modulus `1/(1 + d)` moves with `ℓ` by at
   most `ln 2/4`.

The host's adjoint probes check the realization's integers.
-/

namespace Holonics.HNN.CarryGate

open Complex

/-- [definition] **The carry's turn** `γ̂(q) = ((4 − q²) + 4 i q) / (4 + q²)`. -/
noncomputable def carryTurn (q : ℝ) : ℂ :=
  ⟨(4 - q ^ 2) / (4 + q ^ 2), 4 * q / (4 + q ^ 2)⟩

/-- [definition] **The carry's gate** `γ(q, d) = γ̂(q) / (1 + d)`, the friction `d ≥ 0` charted
apart from the turn. -/
noncomputable def carryGate (q d : ℝ) : ℂ :=
  ⟨(4 - q ^ 2) / ((4 + q ^ 2) * (1 + d)), 4 * q / ((4 + q ^ 2) * (1 + d))⟩

theorem four_add_sq_ne_zero (q : ℝ) : (4 + q ^ 2 : ℝ) ≠ 0 := by positivity

/-- [proved-derived; formal-checked] **The turn keeps the circle**: `|γ̂(q)|² = 1`. -/
theorem carryTurn_normSq (q : ℝ) : Complex.normSq (carryTurn q) = 1 := by
  have h := four_add_sq_ne_zero q
  simp only [carryTurn, Complex.normSq_mk]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The turn is the Cayley tick of `i q / 2`**:
`γ̂(q) = (1 + i q/2) / (1 − i q/2)`. -/
theorem carryTurn_eq_cayley (q : ℝ) :
    carryTurn q = (1 + (q : ℂ) / 2 * I) / (1 - (q : ℂ) / 2 * I) := by
  have hden : (1 - (q : ℂ) / 2 * I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  rw [eq_div_iff hden]
  have h := four_add_sq_ne_zero q
  apply Complex.ext
  · simp [carryTurn]
    field_simp
    ring
  · simp [carryTurn]
    field_simp
    ring

/-- [proved-derived; formal-checked] **Founded without friction the gate is the turn**. -/
theorem carryGate_zero (q : ℝ) : carryGate q 0 = carryTurn q := by
  apply Complex.ext <;> simp [carryGate, carryTurn]

/-- [proved-derived; formal-checked] **The gate's power is the friction's**:
`|γ(q, d)|² = 1/(1 + d)²` for `d ≥ 0`. -/
theorem carryGate_normSq (q d : ℝ) (hd : 0 ≤ d) :
    Complex.normSq (carryGate q d) = 1 / (1 + d) ^ 2 := by
  have h1 := four_add_sq_ne_zero q
  have h2 : (1 + d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  simp only [carryGate, Complex.normSq_mk]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The move is passive by its form**: `|γ(q, d)|² ≤ 1` for
every turn `q` and every friction `d ≥ 0`. -/
theorem carryGate_normSq_le_one (q d : ℝ) (hd : 0 ≤ d) :
    Complex.normSq (carryGate q d) ≤ 1 := by
  rw [carryGate_normSq q d hd, div_le_one (pow_pos (by linarith) 2)]
  nlinarith

/-- [proved-derived; formal-checked] **The turn's real part moves as `−Im γ̂ · 4/(4 + q²)`**. -/
theorem carryTurn_re_hasDerivAt (q : ℝ) :
    HasDerivAt (fun x : ℝ => (4 - x ^ 2) / (4 + x ^ 2))
      (-(4 * q / (4 + q ^ 2)) * (4 / (4 + q ^ 2))) q := by
  have hn : HasDerivAt (fun x : ℝ => 4 - x ^ 2) (-(2 * q)) q := by
    simpa using (hasDerivAt_pow 2 q).const_sub (4 : ℝ)
  have hd : HasDerivAt (fun x : ℝ => 4 + x ^ 2) (2 * q) q := by
    simpa using (hasDerivAt_pow 2 q).const_add (4 : ℝ)
  have h0 := four_add_sq_ne_zero q
  have h : HasDerivAt (fun x : ℝ => (4 - x ^ 2) / (4 + x ^ 2))
      ((-(2 * q) * (4 + q ^ 2) - (4 - q ^ 2) * (2 * q)) / (4 + q ^ 2) ^ 2) q := hn.div hd h0
  refine h.congr_deriv ?_
  field_simp
  ring

/-- [proved-derived; formal-checked] **The turn's imaginary part moves as `Re γ̂ · 4/(4 + q²)`**. -/
theorem carryTurn_im_hasDerivAt (q : ℝ) :
    HasDerivAt (fun x : ℝ => 4 * x / (4 + x ^ 2))
      ((4 - q ^ 2) / (4 + q ^ 2) * (4 / (4 + q ^ 2))) q := by
  have hn : HasDerivAt (fun x : ℝ => 4 * x) 4 q := by
    simpa using (hasDerivAt_id q).const_mul (4 : ℝ)
  have hd : HasDerivAt (fun x : ℝ => 4 + x ^ 2) (2 * q) q := by
    simpa using (hasDerivAt_pow 2 q).const_add (4 : ℝ)
  have h0 := four_add_sq_ne_zero q
  have h : HasDerivAt (fun x : ℝ => 4 * x / (4 + x ^ 2))
      ((4 * (4 + q ^ 2) - 4 * q * (2 * q)) / (4 + q ^ 2) ^ 2) q := hn.div hd h0
  refine h.congr_deriv ?_
  field_simp
  ring

/-- [proved-derived; formal-checked] **A part of the gate moves with the friction as
`−(its value)/(1 + d)`**: `∂/∂d (a/(b(1 + d))) = −(a/(b(1 + d)))/(1 + d)`. -/
theorem friction_hasDerivAt (a b d : ℝ) (hb : b ≠ 0) (hd : 1 + d ≠ 0) :
    HasDerivAt (fun x : ℝ => a / (b * (1 + x))) (-(a / (b * (1 + d))) / (1 + d)) d := by
  have hden : HasDerivAt (fun x : ℝ => b * (1 + x)) b d := by
    simpa using ((hasDerivAt_id d).const_add (1 : ℝ)).const_mul b
  have h : HasDerivAt (fun x : ℝ => a / (b * (1 + x)))
      ((0 * (b * (1 + d)) - a * b) / (b * (1 + d)) ^ 2) d := (hasDerivAt_const d a).div hden (mul_ne_zero hb hd)
  refine h.congr_deriv ?_
  field_simp
  ring

/-- [definition] **The leak's log chart** `d = d₀ 2^ℓ`, the founded friction `d₀ = 1/4`
(`1/(NEAR − 2)`, the near field's), written through the exponential: `2^ℓ = e^(ℓ ln 2)`. -/
noncomputable def leak (l : ℝ) : ℝ := Real.exp (l * Real.log 2) / 4

/-- [proved-derived; formal-checked] **The chart is `2^ℓ/4`**. -/
theorem leak_eq_rpow (l : ℝ) : leak l = (2 : ℝ) ^ l / 4 := by
  rw [leak, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2) l]

/-- [proved-derived; formal-checked] **The chart's friction is positive at every read**. -/
theorem leak_pos (l : ℝ) : 0 < leak l := by
  unfold leak
  positivity

/-- [proved-derived; formal-checked] **Founded at `ℓ = 0` the friction is the near field's**,
`1/4`. -/
theorem leak_zero : leak 0 = 1 / 4 := by
  simp [leak]

/-- [proved-derived; formal-checked] **The chart moves the friction by a ratio**:
`∂d/∂ℓ = ln 2 · d`. -/
theorem leak_hasDerivAt (l : ℝ) : HasDerivAt leak (Real.log 2 * leak l) l := by
  have h : HasDerivAt leak (Real.exp (l * Real.log 2) * (1 * Real.log 2) / 4) l :=
    (((hasDerivAt_id l).mul_const (Real.log 2)).exp).div_const 4
  refine h.congr_deriv ?_
  simp only [leak]
  ring

/-- [proved-derived; formal-checked] **On the log chart the move is strictly passive**:
`|γ(q, d₀ 2^ℓ)|² < 1` at every turn and every leak read. -/
theorem carryGate_leak_normSq_lt_one (q l : ℝ) : Complex.normSq (carryGate q (leak l)) < 1 := by
  have hd := leak_pos l
  rw [carryGate_normSq q (leak l) hd.le, div_lt_one (pow_pos (by linarith) 2)]
  nlinarith [sq_nonneg (leak l)]

/-- [proved-derived; formal-checked] **Founded, a circle's group is the near field's five
places**: `(1 + d)/d = 5` at `ℓ = 0`. -/
theorem leak_zero_group : (1 + leak 0) / leak 0 = 5 := by
  rw [leak_zero]
  norm_num

/-- [proved-derived; formal-checked] **A friction of at least a grain bounds the group**:
`(1 + d)/d ≤ 1 + 1/g` for `0 < g ≤ d`. -/
theorem group_le_of_grain (g d : ℝ) (hg : 0 < g) (hd : g ≤ d) : (1 + d) / d ≤ 1 + 1 / g := by
  rw [add_div, div_self (lt_of_lt_of_le hg hd).ne']
  linarith [one_div_le_one_div_of_le hg hd]

/-- [proved-derived; formal-checked] **The gate's sensitivity to the chart is bounded**:
`d/(1 + d)² ≤ 1/4` for `d ≥ 0`, so `|∂(1/(1 + d))/∂ℓ| = ln 2 · d/(1 + d)² ≤ ln 2/4`. -/
theorem leak_sensitivity_le (d : ℝ) (hd : 0 ≤ d) : d / (1 + d) ^ 2 ≤ 1 / 4 := by
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (1 - d)]

end Holonics.HNN.CarryGate

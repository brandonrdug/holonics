import Mathlib

/-!
# HNN.CarryGate: the carry's gate is a turn and a friction, charted apart

[definition] The carry along the strand (`contact.carried-product`, `Field`'s scan in
`crates/holonics/src/hnn/tower/field.rs`) composes the move `z ↦ γ(t) z + κ(t) b(t)` inside one
tick. Its gate is charted as a turn and a friction apart, the friction on the leak's log chart, and
the drive is admitted through the same friction (`κ`, below):

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
8. **The drive is charged through the leak** (`coupling`, `coupling_leak_zero`, `coupling_eq`,
   `gate_and_coupling`, `coupling_nonneg`, `coupling_steady`; November 12, G98): the coupling
   `κ(d) = 5 d/(1 + d)` is one at the founding, `1/(1 + d) + κ/5 = 1`, and a constant drive's
   level is `5 b` at every friction: the friction moves how far back the charge reaches, never its
   level.
9. **The charge stays within five places' drive** (`charge_step_le`, `charge`, `charge_le`):
   `‖Q n‖ ≤ 5 max ‖b‖` at every site, whatever the turns and however long a run of low friction,
   where the sum form's charge grew with its group.
10. **The coupling's derivatives** (`coupling_hasDerivAt`, `coupling_leak_hasDerivAt`):
   `∂κ/∂d = 5/(1 + d)²`, and on the leak's chart `∂κ/∂ℓ = ln 2 · κ/(1 + d)`, the second part of
   the leak's covector beside the gate's.

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

/-! ## The drive charged through the leak (G98)

[definition] The scan's move is `z ↦ γ(q, d) z + κ(d) b`, the drive `b` admitted through the
friction it leaks by: `κ(d) = 5 d/(1 + d)`, `5 = (1 + d₀)/d₀` the founded group. So the move keeps
`1/(1 + d)` of the turned charge and admits `d/(1 + d)` of the level `5 b`: it is the implicit
step of a dissipation relaxing toward `5 b` (a capacitor charged through its resistor), and the
charge is a turned mean of `5 b`, within `5 max |b|` at every friction. The sum form `z ↦ γ z + b`
held `(1 + d)/d` places' drive instead (G97 scored: at the six bursts a circle's largest charge
stood at 2.6 to 20 times the median section's, at the refused section 54 times). -/

/-- [definition] **The drive's coupling through the leak** `κ(d) = 5 d/(1 + d)`. -/
noncomputable def coupling (d : ℝ) : ℝ := 5 * d / (1 + d)

/-- [proved-derived; formal-checked] **Founded, the coupling is one** (`κ(1/4) = 1`), so a founded
circle's move is the sum form's. -/
theorem coupling_leak_zero : coupling (leak 0) = 1 := by
  rw [coupling, leak_zero]
  norm_num

/-- [proved-derived; formal-checked] **The coupling is what the move does not keep, five times**:
`κ(d) = 5 (1 − 1/(1 + d))` for `d ≥ 0`. -/
theorem coupling_eq (d : ℝ) (hd : 0 ≤ d) : coupling d = (1 - 1 / (1 + d)) * 5 := by
  have h1 : (1 + d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have e1 : 5 * d / (1 + d) * (1 + d) = 5 * d := div_mul_cancel₀ _ h1
  have e2 : 1 / (1 + d) * (1 + d) = 1 := one_div_mul_cancel h1
  apply mul_right_cancel₀ h1
  unfold coupling
  linear_combination e1 + 5 * e2

/-- [proved-derived; formal-checked] **What the move keeps and what it admits sum to one**:
`1/(1 + d) + κ(d)/5 = 1`. -/
theorem gate_and_coupling (d : ℝ) (hd : 0 ≤ d) : 1 / (1 + d) + coupling d / 5 = 1 := by
  rw [coupling_eq d hd]
  ring

/-- [proved-derived; formal-checked] **The coupling is never negative**. -/
theorem coupling_nonneg (d : ℝ) (hd : 0 ≤ d) : 0 ≤ coupling d := by
  unfold coupling
  positivity

/-- [proved-derived; formal-checked] **The driven level is the founded group's at every
friction**: a constant drive's fixed point `κ b/(1 − 1/(1 + d))` is `5 b`, since
`κ(d) (1 + d)/d = 5` for `d > 0`. -/
theorem coupling_steady (d : ℝ) (hd : 0 < d) : coupling d * ((1 + d) / d) = 5 := by
  have h0 : d ≠ 0 := hd.ne'
  have h1 : (1 + d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have e1 : d * d⁻¹ = 1 := mul_inv_cancel₀ h0
  have e2 : (1 + d) * (1 + d)⁻¹ = 1 := mul_inv_cancel₀ h1
  unfold coupling
  linear_combination (5 * (d * d⁻¹)) * e2 + 5 * e1

/-- [proved-derived; formal-checked] **One step keeps the charge within the level**: if
`‖z‖ ≤ M` and `5 ‖b‖ ≤ M`, then `‖γ(q, d) z + κ(d) b‖ ≤ M` for every turn `q` and friction
`d ≥ 0`. -/
theorem charge_step_le (q d M : ℝ) (z b : ℂ) (hd : 0 ≤ d) (hz : ‖z‖ ≤ M) (hb : 5 * ‖b‖ ≤ M) :
    ‖carryGate q d * z + (coupling d : ℂ) * b‖ ≤ M := by
  have h1 : (0 : ℝ) < 1 + d := by linarith
  have hg0 : (0 : ℝ) < 1 / (1 + d) := by positivity
  have hg1 : 1 / (1 + d) ≤ 1 := by
    rw [div_le_one h1]
    linarith
  have hg : ‖carryGate q d‖ ≤ 1 / (1 + d) := by
    have hsq := carryGate_normSq q d hd
    rw [Complex.normSq_eq_norm_sq] at hsq
    have hn := norm_nonneg (carryGate q d)
    have h2 : ‖carryGate q d‖ ^ 2 = (1 / (1 + d)) ^ 2 := by
      rw [hsq, div_pow, one_pow]
    nlinarith
  have hk : ‖(coupling d : ℂ)‖ = coupling d := by
    rw [Complex.norm_real, Real.norm_of_nonneg (coupling_nonneg d hd)]
  have hstep : ‖carryGate q d * z + (coupling d : ℂ) * b‖ ≤
      ‖carryGate q d‖ * ‖z‖ + coupling d * ‖b‖ := by
    calc ‖carryGate q d * z + (coupling d : ℂ) * b‖
        ≤ ‖carryGate q d * z‖ + ‖(coupling d : ℂ) * b‖ := norm_add_le _ _
      _ = ‖carryGate q d‖ * ‖z‖ + coupling d * ‖b‖ := by rw [norm_mul, norm_mul, hk]
  have ha : ‖carryGate q d‖ * ‖z‖ ≤ 1 / (1 + d) * M :=
    (mul_le_mul_of_nonneg_right hg (norm_nonneg z)).trans
      (mul_le_mul_of_nonneg_left hz hg0.le)
  have hc : coupling d * ‖b‖ ≤ (1 - 1 / (1 + d)) * M := by
    rw [coupling_eq d hd, mul_assoc]
    exact mul_le_mul_of_nonneg_left hb (by linarith)
  linarith

/-- [definition] **A circle's charge along its strand**: `Q 0 = 0` and
`Q (n + 1) = γ(q n, d n) Q n + κ(d n) b n`. -/
noncomputable def charge (q d : ℕ → ℝ) (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => carryGate (q n) (d n) * charge q d b n + (coupling (d n) : ℂ) * b n

/-- [proved-derived; formal-checked] **The charge stays within five places' drive**: with every
friction `d n ≥ 0` and every drive `‖b n‖ ≤ B`, `‖Q n‖ ≤ 5 B` at every site, whatever the turns
and however long a run of low friction. -/
theorem charge_le (q d : ℕ → ℝ) (b : ℕ → ℂ) (B : ℝ) (hd : ∀ n, 0 ≤ d n) (hb : ∀ n, ‖b n‖ ≤ B)
    (hB : 0 ≤ B) : ∀ n, ‖charge q d b n‖ ≤ 5 * B := by
  intro n
  induction n with
  | zero =>
    simp only [charge, norm_zero]
    linarith
  | succ n ih =>
    simp only [charge]
    exact charge_step_le (q n) (d n) (5 * B) (charge q d b n) (b n) (hd n) ih
      (by linarith [hb n])

/-- [proved-derived; formal-checked] **The coupling moves with the friction as `5/(1 + d)²`**. -/
theorem coupling_hasDerivAt (d : ℝ) (hd : 1 + d ≠ 0) :
    HasDerivAt coupling (5 / (1 + d) ^ 2) d := by
  have hn : HasDerivAt (fun x : ℝ => 5 * x) 5 d := by
    simpa using (hasDerivAt_id d).const_mul (5 : ℝ)
  have hden : HasDerivAt (fun x : ℝ => 1 + x) 1 d := by
    simpa using (hasDerivAt_id d).const_add (1 : ℝ)
  have h : HasDerivAt (fun x : ℝ => 5 * x / (1 + x)) ((5 * (1 + d) - 5 * d * 1) / (1 + d) ^ 2) d :=
    hn.div hden hd
  refine h.congr_deriv ?_
  ring

/-- [proved-derived; formal-checked] **On the leak's chart the coupling moves as
`ln 2 · κ/(1 + d)`**: `∂κ(d₀ 2^ℓ)/∂ℓ = ln 2 · κ/(1 + d)`, the covector the return adds to `δℓ`
beside the gate's. -/
theorem coupling_leak_hasDerivAt (l : ℝ) :
    HasDerivAt (fun x => coupling (leak x)) (Real.log 2 * coupling (leak l) / (1 + leak l)) l := by
  have h1 := leak_hasDerivAt l
  have hne : (1 + leak l : ℝ) ≠ 0 := ne_of_gt (by linarith [leak_pos l])
  have h := (h1.const_mul (5 : ℝ)).div (h1.const_add (1 : ℝ)) hne
  refine h.congr_deriv ?_
  unfold coupling
  field_simp
  ring

end Holonics.HNN.CarryGate

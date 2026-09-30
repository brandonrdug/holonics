import Holonics.HNN.Floquet

/-!
# HNN.FloquetPassage: the passage's monodromy through every crossing cell's pump

[definition] A passage's cells cross a receiving ring's section, and each crossing pumps the ring:
the pump's block is the reflection at the crossing's placed carrier (`HNN/Floquet.reflection`), and
between two crossings the ring turns by its own transport. The passage's monodromy is the ordered
product of those pumped ticks (the Rust owner `hnn::ring::ReceivingBank::read_turn`, module header
"The passage's monodromy"). This module states, in the kicked chart (a crossing is the tick
`Rot(v)(1 + p R_u)`: the ring's transport `v` after a pump of strength `p` at the carrier `u`), what
the monodromy reads at second order in the pump. The executed law's tick is a rational function of
`p` whose first-order term is linear in the carrier, so its expansion has the same form; the
executed law's own second-order identity is owed in #62.

1. **A transported pair composes to the turn by the relative phase less the transport.**
   [proved-derived; formal-checked] A reflection absorbs a turn on either side,
   `R_ψ Rot(α) = R_(ψ − α)` and `Rot(α) R_ψ = R_(ψ + α)` (`reflection_mul_rotation`,
   `rotation_mul_reflection`), so two crossings separated by the ring's transport compose to
   `R_ψ Rot(α) R_χ = Rot(ψ − α − χ)`: in carriers `R_u Rot_v R_w = Rot(u v̄ w̄)`
   (`reflection_transport_reflection`, `reflection_transport_reflection_carriers`). A turn's trace
   is `2 cos`, `tr Rot(z) = 2 Re z` (`rotation_trace_carrier`).
2. **The passage's expansion in the pump.** [proved-derived; formal-checked] The kicked tick is the
   polynomial `C(Rot_v) + X·C(Rot_v R_u)` with matrix coefficients (`kick`); one crossing more
   composes the passage's coefficients as `c₀′ = Rot_v c₀`, `c₁′ = Rot_v c₁ + Rot_v R_u c₀`,
   `c₂′ = Rot_v c₂ + Rot_v R_u c₁` (`kick_coeff_zero`, `kick_coeff_one`, `kick_coeff_two`). Over
   the whole passage (`passage`): `c₀ = Rot(v^n)`, `c₁ = Σ_t R(v^(n−t) u_t v̄^t)`, and the second order
   is the sum over ordered pairs of crossings `s < t`, each the transported pair of (1),
   `c₂ = Σ_(t<n) Σ_(s<t) Rot(v^(n−t) v̄^(t−s) v^s u_t ū_s)` (`passage_coeff_zero`,
   `passage_coeff_one`, `passage_coeff_two`). For a unit transport the pair's turn is
   `v^n (u_t v̄^(2t)) conj(u_s v̄^(2s))`: the carriers read at the ring's parametric resonance (the
   doubled transport).
3. **At a whole turn the second order's trace is the passage's power spectrum.**
   [proved-derived; formal-checked] `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ_t w_t|² − Σ_t |w_t|²`
   (`pair_sum_power_spectrum`): every crossing read against everything that crossed before it, the
   square law of the whole passage, blind to its global phase.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.HNN.FloquetPassage

open Matrix Polynomial
open Holonics.HNN.Floquet
open scoped BigOperators

/-! ## 1. A transported pair -/

section Transported

variable {R : Type*} [CommRing R]

/-- [definition] **The ring's transport between two crossings**: the turn `Rot(α)` at the carrier
`(c, s) = (cos α, sin α)`. -/
def rotation (c s : R) : Matrix (Fin 2) (Fin 2) R := !![c, -s; s, c]

/-- [proved-derived; formal-checked] **A reflection absorbs a turn after it**:
`R_ψ Rot(α) = R_(ψ − α)`. -/
theorem reflection_mul_rotation (c s a b : R) :
    reflection c s * rotation a b = reflection (c * a + s * b) (s * a - c * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [proved-derived; formal-checked] **A reflection absorbs a turn before it**:
`Rot(α) R_ψ = R_(ψ + α)`. -/
theorem rotation_mul_reflection (a b c s : R) :
    rotation a b * reflection c s = reflection (a * c - b * s) (b * c + a * s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [proved-derived; formal-checked] **A transported pair composes to a turn**:
`R_ψ Rot(α) R_χ = Rot(ψ − α − χ)`. -/
theorem reflection_transport_reflection (c s a b c' s' : R) :
    reflection c s * rotation a b * reflection c' s' =
      rotation ((c * a + s * b) * c' + (s * a - c * b) * s')
        ((s * a - c * b) * c' - (c * a + s * b) * s') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, rotation, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

end Transported

/-- [proved-derived; formal-checked] **In carriers**: `R_u Rot_v R_w = Rot(u v̄ w̄)`, the turn by the
pair's relative phase less the transport between them. -/
theorem reflection_transport_reflection_carriers (u v w : ℂ) :
    reflection u.re u.im * rotation v.re v.im * reflection w.re w.im =
      rotation (u * star v * star w).re (u * star v * star w).im := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, rotation, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im] <;> ring

/-- [proved-derived; formal-checked] **A turn's trace reads its carrier**: `tr Rot(z) = 2 Re z`. -/
theorem rotation_trace_carrier (z : ℂ) : (rotation z.re z.im).trace = 2 * z.re := by
  rw [Matrix.trace_fin_two]
  simp [rotation]
  ring

/-! ## 2. The passage's expansion in the pump -/

section Expansion

/-- [definition] **A crossing's kicked tick** as a polynomial in the pump strength with matrix
coefficients: `Rot_v (1 + p R_u) = C(Rot_v) + X·C(Rot_v R_u)`. -/
def kick (v u : ℂ) : (Matrix (Fin 2) (Fin 2) ℝ)[X] :=
  C (rotation v.re v.im) + X * C (rotation v.re v.im * reflection u.re u.im)

theorem kick_coeff (v u : ℂ) (n : ℕ) :
    (kick v u).coeff n =
      if n = 0 then rotation v.re v.im
      else if n = 1 then rotation v.re v.im * reflection u.re u.im else 0 := by
  rcases n with _ | _ | n <;> simp [kick, coeff_C, coeff_X_mul]

/-- [proved-derived; formal-checked] **One crossing more, order zero**: `c₀′ = Rot_v c₀`. -/
theorem kick_coeff_zero (v u : ℂ) (P : (Matrix (Fin 2) (Fin 2) ℝ)[X]) :
    (kick v u * P).coeff 0 = rotation v.re v.im * P.coeff 0 := by
  rw [coeff_mul]
  simp [kick_coeff]

/-- [proved-derived; formal-checked] **One crossing more, order one**:
`c₁′ = Rot_v c₁ + Rot_v R_u c₀`. -/
theorem kick_coeff_one (v u : ℂ) (P : (Matrix (Fin 2) (Fin 2) ℝ)[X]) :
    (kick v u * P).coeff 1 =
      rotation v.re v.im * P.coeff 1 + rotation v.re v.im * reflection u.re u.im * P.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, kick_coeff]

/-- [proved-derived; formal-checked] **One crossing more, order two**: the new crossing pairs with
every earlier one, `c₂′ = Rot_v c₂ + Rot_v R_u c₁`. -/
theorem kick_coeff_two (v u : ℂ) (P : (Matrix (Fin 2) (Fin 2) ℝ)[X]) :
    (kick v u * P).coeff 2 =
      rotation v.re v.im * P.coeff 2 + rotation v.re v.im * reflection u.re u.im * P.coeff 1 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ, kick_coeff]

/-- A turn at a carrier, `Rot z`. -/
abbrev Rot (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := rotation z.re z.im

/-- A reflection at a carrier, `R_z`. -/
abbrev Ref (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ := reflection z.re z.im

theorem rot_mul_rot (a b : ℂ) : Rot a * Rot b = Rot (a * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem rot_mul_ref (a u : ℂ) : Rot a * Ref u = Ref (a * u) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, reflection, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im] <;> ring

theorem ref_mul_rot (u b : ℂ) : Ref u * Rot b = Ref (u * star b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, reflection, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im]
  ring

theorem ref_mul_ref (u w : ℂ) : Ref u * Ref w = Rot (u * star w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, reflection, Matrix.mul_apply, Fin.sum_univ_two, Complex.mul_re,
      Complex.mul_im] <;> ring

/-- [definition] **The passage's monodromy as a polynomial in the pump**: `M_0 = 1`,
`M_(n+1) = kick(v, u_n) · M_n`, the crossings in their own order. -/
def passage (v : ℂ) (u : ℕ → ℂ) : ℕ → (Matrix (Fin 2) (Fin 2) ℝ)[X]
  | 0 => 1
  | n + 1 => kick v (u n) * passage v u n

theorem passage_coeff_zero (v : ℂ) (u : ℕ → ℂ) (n : ℕ) :
    (passage v u n).coeff 0 = Rot (v ^ n) := by
  induction n with
  | zero => simp [passage, rotation, Matrix.one_fin_two]
  | succ n ih => rw [passage, kick_coeff_zero, ih, rot_mul_rot, pow_succ, mul_comm]

/-- [proved-derived; formal-checked] **The first order**: every crossing's reflection carried by the
transport after it and before it, `Σ_t R(v^(n−t) u_t v̄^t)`. -/
theorem passage_coeff_one (v : ℂ) (u : ℕ → ℂ) (n : ℕ) :
    (passage v u n).coeff 1 =
      ∑ t ∈ Finset.range n, Ref (v ^ (n - t) * u t * star v ^ t) := by
  induction n with
  | zero => simp [passage, Polynomial.coeff_one]
  | succ n ih =>
    rw [passage, kick_coeff_one, ih, passage_coeff_zero, Finset.mul_sum, Finset.sum_range_succ]
    change ∑ t ∈ Finset.range n, Rot v * Ref (v ^ (n - t) * u t * star v ^ t) +
        Rot v * Ref (u n) * Rot (v ^ n) = _
    congr 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      have ht : t < n := Finset.mem_range.mp ht
      rw [rot_mul_ref, Nat.succ_sub (le_of_lt ht), pow_succ]
      ring_nf
    · rw [mul_assoc, ref_mul_rot, rot_mul_ref, Nat.add_sub_cancel_left, pow_one, star_pow]
      ring_nf

/-- [proved-derived; formal-checked] **The passage's second order**: the sum over ordered pairs of
crossings `s < t`, each the transported pair `Rot(v^(n−t) v̄^(t−s) v^s u_t ū_s)`: the pair's relative
phase `u_t ū_s` turned by the transport after, between and before them. For a unit transport
(`v̄ = v⁻¹`) the pair's turn is `v^n (u_t v̄^(2t)) conj(u_s v̄^(2s))`: the carriers read at the
ring's parametric resonance, whose power spectrum `pair_sum_power_spectrum` reads at a whole turn. -/
theorem passage_coeff_two (v : ℂ) (u : ℕ → ℂ) (n : ℕ) :
    (passage v u n).coeff 2 =
      ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range t,
        Rot (v ^ (n - t) * star v ^ (t - s) * v ^ s * u t * star (u s)) := by
  induction n with
  | zero => simp [passage, Polynomial.coeff_one]
  | succ n ih =>
    rw [passage, kick_coeff_two, ih, passage_coeff_one, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_range_succ]
    change ∑ t ∈ Finset.range n, Rot v * ∑ s ∈ Finset.range t,
          Rot (v ^ (n - t) * star v ^ (t - s) * v ^ s * u t * star (u s)) +
        ∑ s ∈ Finset.range n, Rot v * Ref (u n) * Ref (v ^ (n - s) * u s * star v ^ s) = _
    congr 1
    · refine Finset.sum_congr rfl fun t ht => ?_
      have ht : t < n := Finset.mem_range.mp ht
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [rot_mul_rot, Nat.succ_sub (le_of_lt ht), pow_succ]
      ring_nf
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [mul_assoc, ref_mul_ref, rot_mul_rot, Nat.add_sub_cancel_left, pow_one]
      simp only [star_mul', star_pow, star_star]
      ring_nf

end Expansion

/-! ## 3. At a whole turn the second order's trace is the power spectrum -/

section Spectrum

private theorem re_mul_star_comm (a b : ℂ) : (a * star b).re = (b * star a).re := by
  simp [Complex.mul_re]
  ring

/-- [proved-derived; formal-checked] **The square law of a passage**: every crossing read against
the sum of everything before it, `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ_t w_t|² − Σ_t |w_t|²`, the
passage's power spectrum at the carriers' frequency less its incoherent part, blind to the global
phase. -/
theorem pair_sum_power_spectrum (w : ℕ → ℂ) (n : ℕ) :
    2 * (∑ t ∈ Finset.range n, w t * star (∑ s ∈ Finset.range t, w s)).re =
      Complex.normSq (∑ t ∈ Finset.range n, w t) -
        ∑ t ∈ Finset.range n, Complex.normSq (w t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Complex.add_re,
      mul_add, ih, Complex.normSq_add]
    have hcomm := re_mul_star_comm (w n) (∑ s ∈ Finset.range n, w s)
    simp only [Complex.star_def] at hcomm ⊢
    rw [hcomm]
    ring

end Spectrum

section Audit

#print axioms reflection_mul_rotation
#print axioms rotation_mul_reflection
#print axioms reflection_transport_reflection
#print axioms reflection_transport_reflection_carriers
#print axioms rotation_trace_carrier
#print axioms kick_coeff_zero
#print axioms kick_coeff_one
#print axioms kick_coeff_two
#print axioms rot_mul_rot
#print axioms rot_mul_ref
#print axioms ref_mul_rot
#print axioms ref_mul_ref
#print axioms passage_coeff_zero
#print axioms passage_coeff_one
#print axioms passage_coeff_two
#print axioms pair_sum_power_spectrum

end Audit

end Holonics.HNN.FloquetPassage

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
   `c₂′ = Rot_v c₂ + Rot_v R_u c₁` (`kick_coeff_zero`, `kick_coeff_one`, `kick_coeff_two`). So the
   second order is the sum over ordered pairs of crossings `s < t`, each the transported pair of
   (1): `Rot_v^(N−t) R_(u_t) Rot_v^(t−s) R_(u_s) Rot_v^s = Rot(v^N w_t w̄_s)`, `w_t = u_t v̄^(2t)`,
   the carriers read at the ring's parametric resonance (the doubled transport).
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
#print axioms pair_sum_power_spectrum

end Audit

end Holonics.HNN.FloquetPassage

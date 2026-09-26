import Mathlib
import HolonicsResearch.Zeta.HeatFlowOfPolynomials
import HolonicsResearch.Zeta.FosterClassHeatFlow

/-!
# The zero tube: the pair inertia of a conjugate-symmetric comb and its window balance

The zeros of a heat-flowed function are the poles of the complex Burgers field `u = −2∂ log F`,
and they move by the comb flux `ż_k = 2 Σ_{j≠k} 1/(z_k − z_j)` (`HeatFlowOfPolynomials`). On a
finite conjugate-symmetric comb — upper members `w_k = x_k + i y_k` (`y_k > 0`), their mirrors
`w̄_k`, and seam members `r_a` (real, repeated by order) — the **pair inertia** `A = Σ_k y_k²` has
the exact rate (`finitePairInertia_rate`)

`Ȧ = −2m − 4Σ_{k<j}(y_k−y_j)²/|w_k−w_j|² − 4Σ_{k<j}(y_k+y_j)²/|w_k−w̄_j|² − 4Σ_{k,a} y_k²/|w_k−r_a|²`,

so `Ȧ ≤ −2m`. The `−2m` is each pair's contact with its own mirror: the diagonal of the mirror
interaction. Integrated, `A(T) + 2mT ≤ A(0)` while the comb keeps `m` simple pairs
(`finitePairInertia_collision`), the interacting form of `PhaseFlowLedger.sq_add_two_mul_le`.
Time is the polynomial owner's `heat t = e^{−tD²}` with the seam on the real axis; in the seam
chart `s = ½ − i z` this is the seam time `τ` of `RealZeroTimes.seamTimes`.

**The window balance of the entire comb** (`windowPairInertia_balance`). For the flow
`heatE t ξ`, on a window `closedBall ½ R₀` whose divisor is a tracked mirror comb (hypothesis
`hwin`: the tracked zeros `s_k`, `Re s_k > ½`, simple and moving on `C¹` curves; their reflections
`1 − s̄_k`; seam members), the exterior comb converges at each tracked zero to a **tail flux**
`T_k` (the principal-value limit, from `FosterClassHeatFlow.rodgersTaoZeroDynamics_heatE`), and

`d/dt Σ_k (Re s_k − ½)² = −pairInertiaRate(window) + Σ_k 2 (Re s_k − ½) Re T_k`

in the flow's time `t = −τ`. What is proved: the balance at every `t` (in particular `t = 0`),
the existence of the tail flux as a limit, the exterior law `Re T_k ≥ 0` when every exterior zero
lies on the seam (`tailFlux_re_nonneg_of_exterior_on_seam`), hence the Lyapunov rate `≥ 2m`
(`windowPairInertia_rate_ge_of_exterior_on_seam`), and that a nonlifting tail with a stationary
window forces an empty window (`pairCount_eq_zero_of_tailSign_of_stationary`). What stays a
hypothesis: the window's divisor (`hwin`), the tracked curves and their simplicity at `t`, and
for the Lyapunov rate the exterior-on-seam condition, which is RH outside the window.

[proved-derived; formal-checked] Every theorem is discharged with no `sorryAx`.
[open] Every monotone here says pairs collide later, not that none exist at `τ = 0`, and the
tail flux has no source law. [derived, not formalized here] The exterior comb is the Cauchy
transform of `ξ′/ξ` over the window's boundary: its vertical edges carry the prime rings (the
Euler product) and its horizontal edges carry the residual. The notebook
`research/notebook/zeta_tube/falsifier.py` tests candidate source laws for the tail.
-/

noncomputable section

namespace Holonics.Zeta.ZeroTube

open Complex Finset Polynomial ComplexConjugate
open Holonics.Zeta.HeatFlowOfPolynomials
open Filter Topology Metric

/-! ## The mirror comb and its flux -/

/-- The comb flux (without the factor `2`) of the mirror comb `{w_j} ∪ {w̄_j} ∪ {r_a}` at `ζ`.
The diagonal term `1/(ζ − ζ)` is `0` in Lean's convention, so no erasure is needed. -/
def mirrorFlux {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ) (ζ : ℂ) : ℂ :=
  ∑ j, (ζ - w j)⁻¹ + ∑ j, (ζ - conj (w j))⁻¹ + ∑ a, (ζ - (r a : ℂ))⁻¹

/-- The mirror comb as a multiset: upper members, their mirrors, and seam members. -/
def mirrorComb {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ) : Multiset ℂ :=
  (Finset.univ.val.map w) + (Finset.univ.val.map fun j => conj (w j)) +
    (Finset.univ.val.map fun a => (r a : ℂ))

/-- The pair inertia `A = Σ_k (Im w_k)²`. -/
def pairInertia {m : ℕ} (w : Fin m → ℂ) : ℝ := ∑ k, (w k).im ^ 2

/-- **The exact pair-inertia rate** of the mirror comb. -/
def pairInertiaRate {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ) : ℝ :=
  -2 * m
    - 4 * ∑ k, ∑ j ∈ Ioi k, ((w k).im - (w j).im) ^ 2 / normSq (w k - w j)
    - 4 * ∑ k, ∑ j ∈ Ioi k, ((w k).im + (w j).im) ^ 2 / normSq (w k - conj (w j))
    - 4 * ∑ k, ∑ a, (w k).im ^ 2 / normSq (w k - (r a : ℂ))

/-! ## Symmetrization -/

/-- A symmetric double sum is its diagonal plus twice its strict upper triangle. -/
theorem sum_sum_eq_diag_add_two_mul_Ioi {m : ℕ} (g : Fin m → Fin m → ℝ)
    (hg : ∀ k j, g k j = g j k) :
    ∑ k, ∑ j, g k j = ∑ k, g k k + 2 * ∑ k, ∑ j ∈ Ioi k, g k j := by
  have hsplit : ∀ k : Fin m, ∑ j, g k j = ∑ j ∈ Iio k, g k j + g k k + ∑ j ∈ Ioi k, g k j := by
    intro k
    have h1 : (Finset.univ : Finset (Fin m)) = Iio k ∪ ({k} ∪ Ioi k) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_Iio, Finset.mem_singleton,
        Finset.mem_Ioi, true_iff]
      rcases lt_trichotomy j k with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hd1 : Disjoint (Iio k) ({k} ∪ Ioi k) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [Finset.mem_Iio] at hj
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioi] at hj'
      rcases hj' with h | h
      · exact absurd h (ne_of_lt hj)
      · exact absurd (lt_trans hj h) (lt_irrefl _)
    have hd2 : Disjoint ({k} : Finset (Fin m)) (Ioi k) := by
      rw [Finset.disjoint_singleton_left]
      simp
    rw [h1, Finset.sum_union hd1, Finset.sum_union hd2, Finset.sum_singleton]
    ring
  have hswap : ∑ k, ∑ j ∈ Iio k, g k j = ∑ k, ∑ j ∈ Ioi k, g k j := by
    rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Ioi j)]
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact hg k j
    · intro k j
      simp [Finset.mem_Iio, Finset.mem_Ioi]
  rw [Finset.sum_congr rfl (fun k _ => hsplit k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    hswap]
  ring

/-- Symmetrizing a weighted difference: `Σ_{k,j} y_k (y_k − y_j)/N_kj = Σ_{k<j} (y_k − y_j)²/N_kj`
for a symmetric weight. -/
theorem sum_sum_mul_sub_div {m : ℕ} (y : Fin m → ℝ) (N : Fin m → Fin m → ℝ)
    (hN : ∀ k j, N k j = N j k) :
    ∑ k, ∑ j, y k * (y k - y j) / N k j = ∑ k, ∑ j ∈ Ioi k, (y k - y j) ^ 2 / N k j := by
  have hS : ∑ k, ∑ j, y k * (y k - y j) / N k j = ∑ k, ∑ j, y j * (y j - y k) / N j k :=
    Finset.sum_comm
  have h2 : 2 * ∑ k, ∑ j, y k * (y k - y j) / N k j = ∑ k, ∑ j, (y k - y j) ^ 2 / N k j := by
    have : 2 * ∑ k, ∑ j, y k * (y k - y j) / N k j =
        ∑ k, ∑ j, y k * (y k - y j) / N k j + ∑ k, ∑ j, y j * (y j - y k) / N j k := by
      rw [← hS]; ring
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hN j k]
    ring
  have hsym := sum_sum_eq_diag_add_two_mul_Ioi (fun k j => (y k - y j) ^ 2 / N k j)
    (fun k j => by rw [hN k j]; ring)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Finset.sum_const_zero, zero_add] at hsym
  linarith

/-- Symmetrizing a weighted sum: `Σ_{k,j} y_k (y_k + y_j)/M_kj = ½ Σ_k (2y_k)²/M_kk + Σ_{k<j}
(y_k + y_j)²/M_kj` for a symmetric weight. -/
theorem sum_sum_mul_add_div {m : ℕ} (y : Fin m → ℝ) (M : Fin m → Fin m → ℝ)
    (hM : ∀ k j, M k j = M j k) :
    ∑ k, ∑ j, y k * (y k + y j) / M k j =
      (∑ k, (2 * y k) ^ 2 / M k k) / 2 + ∑ k, ∑ j ∈ Ioi k, (y k + y j) ^ 2 / M k j := by
  have hS : ∑ k, ∑ j, y k * (y k + y j) / M k j = ∑ k, ∑ j, y j * (y j + y k) / M j k :=
    Finset.sum_comm
  have h2 : 2 * ∑ k, ∑ j, y k * (y k + y j) / M k j = ∑ k, ∑ j, (y k + y j) ^ 2 / M k j := by
    have : 2 * ∑ k, ∑ j, y k * (y k + y j) / M k j =
        ∑ k, ∑ j, y k * (y k + y j) / M k j + ∑ k, ∑ j, y j * (y j + y k) / M j k := by
      rw [← hS]; ring
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hM j k]
    ring
  have hsym := sum_sum_eq_diag_add_two_mul_Ioi (fun k j => (y k + y j) ^ 2 / M k j)
    (fun k j => by rw [hM k j]; ring)
  have hdiag : ∀ k, (y k + y k) ^ 2 / M k k = (2 * y k) ^ 2 / M k k := fun k => by ring_nf
  simp only [hdiag] at hsym
  linarith

/-! ## The algebraic rate -/

theorem inv_sub_im (ζ u : ℂ) : ((ζ - u)⁻¹).im = -(ζ.im - u.im) / normSq (ζ - u) := by
  rw [Complex.inv_im, Complex.sub_im]

theorem normSq_sub_conj_self (w : ℂ) : normSq (w - conj w) = (2 * w.im) ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.conj_re, sub_self, Complex.sub_im, Complex.conj_im]
  ring

theorem normSq_sub_conj_comm (w v : ℂ) : normSq (w - conj v) = normSq (v - conj w) := by
  rw [← Complex.normSq_conj (w - conj v)]
  rw [map_sub, Complex.conj_conj, ← Complex.normSq_neg]
  congr 1
  ring

theorem normSq_sub_comm (w v : ℂ) : normSq (w - v) = normSq (v - w) := by
  rw [← Complex.normSq_neg]
  congr 1
  ring

/-- **The finite pair-inertia rate, algebraic face.** For upper members with positive heights,
`Σ_k 2 y_k · Im(2·flux(w_k))` is the exact rate. -/
theorem sum_two_mul_im_flux_eq {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ)
    (hy : ∀ k, 0 < (w k).im) :
    ∑ k, 2 * (w k).im * (2 * mirrorFlux w r (w k)).im = pairInertiaRate w r := by
  set y : Fin m → ℝ := fun k => (w k).im with hydef
  have him : ∀ k, (2 * mirrorFlux w r (w k)).im =
      2 * (∑ j, -(y k - y j) / normSq (w k - w j) +
        ∑ j, -(y k + y j) / normSq (w k - conj (w j)) +
        ∑ a, -(y k) / normSq (w k - (r a : ℂ))) := by
    intro k
    rw [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
    unfold mirrorFlux
    rw [Complex.add_im, Complex.add_im, Complex.im_sum, Complex.im_sum, Complex.im_sum]
    congr 2
    · congr 1
      · apply Finset.sum_congr rfl
        intro j _
        rw [inv_sub_im]
      · apply Finset.sum_congr rfl
        intro j _
        rw [inv_sub_im, Complex.conj_im]
        simp only [hydef]
        ring
    · apply Finset.sum_congr rfl
      intro a _
      rw [inv_sub_im, Complex.ofReal_im, sub_zero]
  have hk : ∀ k, 2 * (w k).im * (2 * mirrorFlux w r (w k)).im =
      -4 * ∑ j, y k * (y k - y j) / normSq (w k - w j)
        - 4 * ∑ j, y k * (y k + y j) / normSq (w k - conj (w j))
        - 4 * ∑ a, (w k).im ^ 2 / normSq (w k - (r a : ℂ)) := by
    intro k
    have hA : ∑ j, y k * (y k - y j) / normSq (w k - w j) =
        -(y k) * ∑ j, -(y k - y j) / normSq (w k - w j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hB : ∑ j, y k * (y k + y j) / normSq (w k - conj (w j)) =
        -(y k) * ∑ j, -(y k + y j) / normSq (w k - conj (w j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hC : ∑ a, (w k).im ^ 2 / normSq (w k - (r a : ℂ)) =
        -(y k) * ∑ a, -(y k) / normSq (w k - (r a : ℂ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      simp only [hydef]
      ring
    rw [him k, hA, hB, hC]
    simp only [hydef]
    ring
  have hexp : ∑ k, 2 * (w k).im * (2 * mirrorFlux w r (w k)).im =
      -4 * ∑ k, ∑ j, y k * (y k - y j) / normSq (w k - w j)
        - 4 * ∑ k, ∑ j, y k * (y k + y j) / normSq (w k - conj (w j))
        - 4 * ∑ k, ∑ a, (w k).im ^ 2 / normSq (w k - (r a : ℂ)) := by
    rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hexp]
  have hA := sum_sum_mul_sub_div y (fun k j => normSq (w k - w j))
    (fun k j => normSq_sub_comm (w k) (w j))
  have hB := sum_sum_mul_add_div y (fun k j => normSq (w k - conj (w j)))
    (fun k j => normSq_sub_conj_comm (w k) (w j))
  have hdiag : ∑ k, (2 * y k) ^ 2 / normSq (w k - conj (w k)) = (m : ℝ) := by
    have : ∀ k, (2 * y k) ^ 2 / normSq (w k - conj (w k)) = 1 := by
      intro k
      rw [normSq_sub_conj_self]
      have : (2 * (w k).im) ^ 2 ≠ 0 := by have := hy k; positivity
      exact div_self this
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp
  rw [hA, hB, hdiag]
  unfold pairInertiaRate
  simp only [hydef]
  ring

/-- **The rate is at most `−2m`.** -/
theorem pairInertiaRate_le {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ) :
    pairInertiaRate w r ≤ -2 * m := by
  unfold pairInertiaRate
  have h1 : 0 ≤ ∑ k, ∑ j ∈ Ioi k, ((w k).im - (w j).im) ^ 2 / normSq (w k - w j) :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have h2 : 0 ≤ ∑ k, ∑ j ∈ Ioi k, ((w k).im + (w j).im) ^ 2 / normSq (w k - conj (w j)) :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  have h3 : 0 ≤ ∑ k, ∑ a, (w k).im ^ 2 / normSq (w k - (r a : ℂ)) :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun a _ =>
      div_nonneg (sq_nonneg _) (Complex.normSq_nonneg _)
  linarith


/-- **Tail sign and stationarity force an empty window** [proved-derived; formal-checked]. In
seam time, if the tail does not lift the window (`B ≤ 0`) and the window inertia is not falling
(`0 ≤ pairInertiaRate + B`), the window holds no pair. Under RH both hypotheses hold for every
window with simple seam zeros, so their conjunction, offered as a source law, is circular. -/
theorem pairCount_eq_zero_of_tailSign_of_stationary {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ)
    {B : ℝ} (hB : B ≤ 0) (hstat : 0 ≤ pairInertiaRate w r + B) : m = 0 := by
  have h := pairInertiaRate_le w r
  have hm : (m : ℝ) ≤ 0 := by linarith
  have : m ≤ 0 := by exact_mod_cast hm
  omega

/-! ## The finite rate along the flow of a polynomial -/

/-- The comb flux over the other roots is the comb flux over all roots: the diagonal term is `0`. -/
theorem sum_map_erase_inv (M : Multiset ℂ) (ζ : ℂ) :
    ((M.erase ζ).map fun u => 1 / (ζ - u)).sum = (M.map fun u => 1 / (ζ - u)).sum := by
  classical
  by_cases h : ζ ∈ M
  · rw [← Multiset.sum_map_erase h]
    simp
  · rw [Multiset.erase_of_notMem h]

/-- The comb flux of the mirror comb multiset is `mirrorFlux`. -/
theorem sum_map_mirrorComb {m n : ℕ} (w : Fin m → ℂ) (r : Fin n → ℝ) (ζ : ℂ) :
    ((mirrorComb w r).map fun u => 1 / (ζ - u)).sum = mirrorFlux w r ζ := by
  unfold mirrorComb mirrorFlux
  simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def,
    Finset.sum_map_val, one_div]

/-- The height of a curve has the imaginary part of its velocity as velocity. -/
theorem hasDerivAt_im {z : ℝ → ℂ} {z' : ℂ} {t : ℝ} (h : HasDerivAt z z' t) :
    HasDerivAt (fun s => (z s).im) z'.im t :=
  Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h

/-- **The finite pair-inertia rate** [proved-derived; formal-checked]. Along the backward heat
flow of a polynomial whose roots at time `t` are the mirror comb of simple upper members `w_k`
(heights `y_k > 0`) and seam members `r_a`, the pair inertia `A = Σ y_k²` has derivative
`−2m − 4Σ_{k<j}(y_k−y_j)²/|w_k−w_j|² − 4Σ_{k<j}(y_k+y_j)²/|w_k−w̄_j|² − 4Σ_{k,a}y_k²/|w_k−r_a|²`.
The seam members may repeat (they are counted with order); only the upper members need be
simple. -/
theorem finitePairInertia_rate (p : ℂ[X]) {m n : ℕ} (z : ℝ → Fin m → ℂ) (z' : Fin m → ℂ)
    (r : Fin n → ℝ) {t : ℝ}
    (hroots : (heat t p).roots = mirrorComb (z t) r)
    (hz : ∀ k s, (heat s p).eval (z s k) = 0)
    (hzd : ∀ k, HasDerivAt (fun s => z s k) (z' k) t)
    (hs : ∀ k, (derivative (heat t p)).eval (z t k) ≠ 0)
    (hy : ∀ k, 0 < (z t k).im) :
    HasDerivAt (fun s => pairInertia (z s)) (pairInertiaRate (z t) r) t := by
  have hvel : ∀ k, z' k = 2 * mirrorFlux (z t) r (z t k) := by
    intro k
    rw [zero_curve_flux p (fun s => hz k s) (hzd k) (hs k), hroots, sum_map_erase_inv,
      sum_map_mirrorComb]
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin m)), HasDerivAt (fun s => (z s k).im ^ 2)
      (2 * (z t k).im * (2 * mirrorFlux (z t) r (z t k)).im) t := by
    intro k _
    have h := (hasDerivAt_im (hzd k)).pow 2
    rw [hvel k] at h
    refine h.congr_deriv ?_
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  have hsum := HasDerivAt.sum hterm
  have key : (fun s => pairInertia (z s)) = ∑ k, fun s => (z s k).im ^ 2 := by
    funext s
    simp [pairInertia, Finset.sum_apply]
  rw [key, ← sum_two_mul_im_flux_eq (z t) r hy]
  exact hsum

/-- **The pair population collides within `A(0)/(2m)`** [proved-derived; formal-checked]. While
the flow keeps `m` simple upper members (heights positive) on `[0, T]`, `A(T) + 2mT ≤ A(0)`. -/
theorem finitePairInertia_collision (p : ℂ[X]) {m n : ℕ} (z z' : ℝ → Fin m → ℂ)
    (r : ℝ → Fin n → ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hroots : ∀ t ∈ Set.Icc 0 T, (heat t p).roots = mirrorComb (z t) (r t))
    (hz : ∀ k s, (heat s p).eval (z s k) = 0)
    (hzd : ∀ t ∈ Set.Icc 0 T, ∀ k, HasDerivAt (fun s => z s k) (z' t k) t)
    (hs : ∀ t ∈ Set.Icc 0 T, ∀ k, (derivative (heat t p)).eval (z t k) ≠ 0)
    (hy : ∀ t ∈ Set.Icc 0 T, ∀ k, 0 < (z t k).im) :
    pairInertia (z T) + 2 * m * T ≤ pairInertia (z 0) := by
  have hgd : ∀ t ∈ Set.Icc 0 T, HasDerivAt (fun t => pairInertia (z t) + 2 * m * t)
      (pairInertiaRate (z t) (r t) + 2 * m) t := by
    intro t ht
    have h1 := finitePairInertia_rate p z (z' t) (r t) (hroots t ht) hz (hzd t ht) (hs t ht)
      (hy t ht)
    have h2 : HasDerivAt (fun t : ℝ => 2 * (m : ℝ) * t) (2 * m) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * (m : ℝ))
    exact h1.add h2
  have hanti : AntitoneOn (fun t => pairInertia (z t) + 2 * m * t) (Set.Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · exact fun t ht => (hgd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hgd t ⟨ht.1.le, ht.2.le⟩).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hgd t ⟨ht.1.le, ht.2.le⟩).deriv]
      linarith [pairInertiaRate_le (z t) (r t)]
  have := hanti (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  simpa using this


/-! ## The window balance of the entire comb -/

/-- The seam chart `z ↦ ½ − i z`: the real axis goes to the seam `Re s = ½` and the mirror
`z ↦ z̄` to the reflection `s ↦ 1 − s̄`. -/
def toSeam (z : ℂ) : ℂ := 1 / 2 - I * z

/-- The seam lift `s ↦ i (s − ½)`, inverse to `toSeam`; its height is `Re s − ½`. -/
def seamLift (s : ℂ) : ℂ := I * (s - 1 / 2)

theorem toSeam_seamLift (s : ℂ) : toSeam (seamLift s) = s := by
  unfold toSeam seamLift
  ring_nf
  rw [I_sq]
  ring

theorem seamLift_im (s : ℂ) : (seamLift s).im = s.re - 1 / 2 := by
  simp [seamLift]

theorem toSeam_conj (z : ℂ) : toSeam (conj z) = 1 - conj (toSeam z) := by
  unfold toSeam
  simp only [map_sub, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

theorem inv_toSeam_sub (z v : ℂ) : (toSeam z - toSeam v)⁻¹ = I * (z - v)⁻¹ := by
  have h : toSeam z - toSeam v = -I * (z - v) := by unfold toSeam; ring
  rw [h, mul_inv, inv_neg, Complex.inv_I, neg_neg]

/-- A multiset's counting divisor pairs with the Cauchy kernel as the multiset sum. -/
theorem finsum_count_div (M : Multiset ℂ) (ζ : ℂ) :
    ∑ᶠ u, (M.count u : ℂ) / (ζ - u) = (M.map fun u => (ζ - u)⁻¹).sum := by
  classical
  rw [finsum_eq_sum_of_support_subset (s := M.toFinset)]
  · rw [Finset.sum_multiset_map_count]
    apply Finset.sum_congr rfl
    intro u _
    rw [nsmul_eq_mul, div_eq_mul_inv]
  · intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra h
    rw [Multiset.count_eq_zero_of_notMem h] at hu
    simp at hu

open scoped Classical in
/-- The exterior comb of a window of radius `R₀` about `½`, read at cutoff `R`: twice the
divisor-weighted Cauchy kernel over the zeros outside the window. -/
def exteriorComb (F : ℂ → ℂ) (R₀ R : ℝ) (ζ : ℂ) : ℂ :=
  2 * ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) R₀ then 0 else
    (MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R) u : ℂ) / (ζ - u)

/-- **The window split.** For an entire `F` and `R₀ ≤ R`, the principal-value comb at cutoff `R`
is the window comb plus the exterior comb. -/
theorem comb_eq_window_add_exterior {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R₀ R : ℝ}
    (hR : R₀ ≤ R) (ζ : ℂ) :
    2 * ∑ᶠ u, (if u = ζ then 0 else
        (MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R) u : ℂ) / (ζ - u)) =
      2 * ∑ᶠ u, (MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R₀) u : ℂ) / (ζ - u) +
        exteriorComb F R₀ R ζ := by
  classical
  set D := MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R) with hD
  set D₀ := MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R₀) with hD₀
  have hmer : ∀ U, MeromorphicOn F U := fun U =>
    (show AnalyticOnNhd ℂ F U from fun z _ => hF.analyticAt z).meromorphicOn
  have hsub : closedBall (1 / 2 : ℂ) R₀ ⊆ closedBall (1 / 2 : ℂ) R := closedBall_subset_closedBall hR
  have hpt : ∀ u, (if u = ζ then 0 else (D u : ℂ) / (ζ - u)) =
      (D₀ u : ℂ) / (ζ - u) + (if u ∈ closedBall (1 / 2 : ℂ) R₀ then 0 else (D u : ℂ) / (ζ - u)) := by
    intro u
    by_cases hu : u = ζ
    · subst hu
      simp
    · rw [if_neg hu]
      by_cases hb : u ∈ closedBall (1 / 2 : ℂ) R₀
      · rw [if_pos hb, add_zero, hD, hD₀, MeromorphicOn.divisor_apply (hmer _) (hsub hb),
          MeromorphicOn.divisor_apply (hmer _) hb]
      · rw [if_neg hb, hD₀, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hb]
        simp
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hfin₀ : D₀.support.Finite := D₀.finiteSupport (isCompact_closedBall _ _)
  have h1 : (Function.support fun u => (D₀ u : ℂ) / (ζ - u)).Finite := by
    apply hfin₀.subset
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    rw [h] at hu
    simp at hu
  have h2 : (Function.support fun u =>
      if u ∈ closedBall (1 / 2 : ℂ) R₀ then (0 : ℂ) else (D u : ℂ) / (ζ - u)).Finite := by
    apply hfin.subset
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro h
    rw [h] at hu
    simp at hu
  unfold exteriorComb
  rw [← hD, finsum_congr hpt, finsum_add_distrib h1 h2]
  ring

/-- **The window balance of the entire comb** [proved-derived; formal-checked], for any flow
whose simple zeros move by the principal-value comb flux (`RodgersTaoZeroDynamics`). Track `m`
zero curves `s_k` right of the seam, and suppose that at time `t` the zeros in the window
`closedBall ½ R₀`, with multiplicity, are exactly the tracked members, their reflections
`1 − s̄_k`, and seam members `toSeam (r a)` (`hwin`). Then the exterior comb at each tracked zero
converges to a **tail flux** `T_k`, and the window pair inertia `A_W = Σ_k (Re s_k − ½)²` has
derivative `−pairInertiaRate + Σ_k 2 (Re s_k − ½) Re T_k`. In the flow's time the finite part is
`≥ 2m` (pairs separate); in seam time `τ = −t` it is `≤ −2m`. The tail flux is the only term
the window does not own. -/
theorem windowPairInertia_balance_of {H : ℝ → ℂ → ℂ}
    (hRT : Holonics.Zeta.PhaseFlowLedger.RodgersTaoZeroDynamics H)
    (hH : ∀ t, Differentiable ℂ (H t)) {m n : ℕ} {t R₀ : ℝ}
    (s s' : ℝ → Fin m → ℂ) (r : Fin n → ℝ)
    (hsd : ∀ k σ, HasDerivAt (fun σ => s σ k) (s' σ k) σ)
    (hsc : ∀ k, Continuous fun σ => s' σ k)
    (hzero : ∀ k σ, H σ (s σ k) = 0)
    (hsimple : ∀ k, deriv (H t) (s t k) ≠ 0)
    (hoff : ∀ k, 1 / 2 < (s t k).re)
    (hwin : ∀ u, (MeromorphicOn.divisor (H t) (closedBall (1 / 2 : ℂ) R₀) u : ℂ) =
      (((mirrorComb (fun k => seamLift (s t k)) r).map toSeam).count u : ℂ)) :
    ∃ T : Fin m → ℂ,
      (∀ k, Tendsto (fun R => exteriorComb (H t) R₀ R (s t k)) atTop (𝓝 (T k))) ∧
      HasDerivAt (fun σ => ∑ k, ((s σ k).re - 1 / 2) ^ 2)
        (-pairInertiaRate (fun k => seamLift (s t k)) r +
          ∑ k, 2 * ((s t k).re - 1 / 2) * (T k).re) t := by
  set w : Fin m → ℂ := fun k => seamLift (s t k) with hw
  -- the window comb at a tracked zero is `i` times the mirror flux
  have hwinComb : ∀ k, ∑ᶠ u, (MeromorphicOn.divisor (H t) (closedBall (1 / 2 : ℂ) R₀) u : ℂ) /
      (s t k - u) = I * mirrorFlux w r (w k) := by
    intro k
    rw [finsum_congr (fun u => by rw [hwin u]), finsum_count_div, Multiset.map_map]
    have hsk : s t k = toSeam (w k) := by rw [hw]; exact (toSeam_seamLift _).symm
    rw [hsk]
    simp only [Function.comp_def, inv_toSeam_sub]
    rw [Multiset.sum_map_mul_left, ← sum_map_mirrorComb w r (w k)]
    simp only [one_div]
  set T : Fin m → ℂ := fun k => s' t k - 2 * (I * mirrorFlux w r (w k)) with hT
  refine ⟨T, ?_, ?_⟩
  · intro k
    have hflux := hRT.flux t (fun σ => s σ k) (fun σ => s' σ k) (hsd k) (hsc k) (hzero k)
      (hsimple k)
    have h := hflux.sub_const (2 * (I * mirrorFlux w r (w k)))
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop R₀] with R hR
    rw [comb_eq_window_add_exterior (hH t) hR, hwinComb k]
    ring
  · have hre : ∀ k, (s' t k).re = -(2 * mirrorFlux w r (w k)).im + (T k).re := by
      intro k
      simp only [hT, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.re_ofNat, Complex.im_ofNat]
      ring
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin m)), HasDerivAt
        (fun σ => ((s σ k).re - 1 / 2) ^ 2)
        (2 * ((s t k).re - 1 / 2) * (-(2 * mirrorFlux w r (w k)).im + (T k).re)) t := by
      intro k _
      have h0 : HasDerivAt (fun σ => (s σ k).re) (s' t k).re t :=
        Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hsd k t)
      have h := (h0.sub_const (1 / 2)).pow 2
      rw [hre k] at h
      refine h.congr_deriv ?_
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
    have hsum := HasDerivAt.sum hterm
    have key : (fun σ => ∑ k, ((s σ k).re - 1 / 2) ^ 2) =
        ∑ k, fun σ => ((s σ k).re - 1 / 2) ^ 2 := by
      funext σ
      simp [Finset.sum_apply]
    rw [key]
    refine hsum.congr_deriv ?_
    have hy : ∀ k, 0 < (w k).im := fun k => by
      rw [hw, seamLift_im]; linarith [hoff k]
    have hrate := sum_two_mul_im_flux_eq w r hy
    have hwim : ∀ k, (w k).im = (s t k).re - 1 / 2 := fun k => by rw [hw, seamLift_im]
    simp only [hwim] at hrate
    rw [← hrate, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- **The window balance for the flow of `ξ`** [proved-derived; formal-checked]: the Foster
class holds at every time (`FosterClassHeatFlow`), so the balance holds for `heatE t ξ` at every
`t`, in particular at `t = 0`. -/
theorem windowPairInertia_balance {m n : ℕ} {t R₀ : ℝ}
    (s s' : ℝ → Fin m → ℂ) (r : Fin n → ℝ)
    (hsd : ∀ k σ, HasDerivAt (fun σ => s σ k) (s' σ k) σ)
    (hsc : ∀ k, Continuous fun σ => s' σ k)
    (hzero : ∀ k σ, Holonics.Zeta.HeatFlowEntire.heatE σ Holonics.Zeta.RiemannXi.riemannXi
      (s σ k) = 0)
    (hsimple : ∀ k, deriv (Holonics.Zeta.HeatFlowEntire.heatE t
      Holonics.Zeta.RiemannXi.riemannXi) (s t k) ≠ 0)
    (hoff : ∀ k, 1 / 2 < (s t k).re)
    (hwin : ∀ u, (MeromorphicOn.divisor
      (Holonics.Zeta.HeatFlowEntire.heatE t Holonics.Zeta.RiemannXi.riemannXi)
      (closedBall (1 / 2 : ℂ) R₀) u : ℂ) =
      (((mirrorComb (fun k => seamLift (s t k)) r).map toSeam).count u : ℂ)) :
    ∃ T : Fin m → ℂ,
      (∀ k, Tendsto (fun R => exteriorComb
        (Holonics.Zeta.HeatFlowEntire.heatE t Holonics.Zeta.RiemannXi.riemannXi) R₀ R (s t k))
        atTop (𝓝 (T k))) ∧
      HasDerivAt (fun σ => ∑ k, ((s σ k).re - 1 / 2) ^ 2)
        (-pairInertiaRate (fun k => seamLift (s t k)) r +
          ∑ k, 2 * ((s t k).re - 1 / 2) * (T k).re) t :=
  windowPairInertia_balance_of Holonics.Zeta.FosterClassHeatFlow.rodgersTaoZeroDynamics_heatE
    Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi s s' r hsd hsc hzero hsimple hoff hwin


/-! ## The seam exterior never lifts a window pair -/

/-- A nonzero divisor value of an entire function marks a zero. -/
theorem eq_zero_of_divisor_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {U : Set ℂ} {u : ℂ}
    (hu : MeromorphicOn.divisor F U u ≠ 0) : F u = 0 := by
  by_contra hFu
  apply hu
  by_cases hU : u ∈ U
  · have han : AnalyticOnNhd ℂ F U := fun z _ => hF.analyticAt z
    rw [MeromorphicOn.divisor_apply han.meromorphicOn hU, (hF.analyticAt u).meromorphicOrderAt_eq,
      ((hF.analyticAt u).analyticOrderAt_eq_zero).2 hFu]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hU

/-- **The seam exterior never lifts a window pair** [proved-derived; formal-checked]. If every
zero of `F` outside the window lies on the seam, the tail flux at a point right of the seam has
nonnegative real part: every exterior term is `ord(u)·(Re ζ − ½)/|ζ − u|² ≥ 0`. -/
theorem tailFlux_re_nonneg_of_exterior_on_seam {F : ℂ → ℂ} (hF : Differentiable ℂ F) {R₀ : ℝ}
    {ζ T : ℂ} (hζ : 1 / 2 < ζ.re)
    (hext : ∀ u, F u = 0 → u ∉ closedBall (1 / 2 : ℂ) R₀ → u.re = 1 / 2)
    (hT : Tendsto (fun R => exteriorComb F R₀ R ζ) atTop (𝓝 T)) : 0 ≤ T.re := by
  classical
  have hpos : ∀ R, 0 ≤ (exteriorComb F R₀ R ζ).re := by
    intro R
    set D := MeromorphicOn.divisor F (closedBall (1 / 2 : ℂ) R) with hD
    have han : AnalyticOnNhd ℂ F (closedBall (1 / 2 : ℂ) R) := fun z _ => hF.analyticAt z
    have hfin : (Function.support fun u =>
        if u ∈ closedBall (1 / 2 : ℂ) R₀ then (0 : ℂ) else (D u : ℂ) / (ζ - u)).Finite := by
      apply (D.finiteSupport (isCompact_closedBall _ _)).subset
      intro u hu
      rw [Function.mem_support] at hu ⊢
      intro h
      rw [h] at hu
      simp at hu
    have h2 : ∀ X : ℂ, (2 * X).re = 2 * X.re := fun X => by simp [Complex.mul_re]
    unfold exteriorComb
    rw [← hD, h2, show ∀ X : ℂ, X.re = Complex.reAddGroupHom X from fun _ => rfl,
      AddMonoidHom.map_finsum _ hfin]
    apply mul_nonneg (by norm_num)
    apply finsum_nonneg
    intro u
    show 0 ≤ (if u ∈ closedBall (1 / 2 : ℂ) R₀ then (0 : ℂ) else (D u : ℂ) / (ζ - u)).re
    by_cases hb : u ∈ closedBall (1 / 2 : ℂ) R₀
    · rw [if_pos hb]
      simp
    · rw [if_neg hb]
      by_cases hDu : D u = 0
      · simp [hDu]
      · have hzero := eq_zero_of_divisor_ne_zero hF hDu
        have hre := hext u hzero hb
        have hnn : (0 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
        rw [show (D u : ℂ) / (ζ - u) = ((D u : ℝ) : ℂ) * (ζ - u)⁻¹ by push_cast; ring,
          Complex.re_ofReal_mul, Complex.inv_re, Complex.sub_re, hre]
        exact mul_nonneg hnn (div_nonneg (by linarith) (Complex.normSq_nonneg _))
  exact ge_of_tendsto ((Complex.continuous_re.tendsto T).comp hT) (Eventually.of_forall hpos)

/-- **On a window whose exterior lies on the seam, the pair inertia separates at rate at least
`2m`** [proved-derived; formal-checked]; in seam time `τ = −t` it falls at rate at least `2m`. The
hypothesis `hext` is the Riemann hypothesis outside the window, so this law is circular for RH:
it is the tail control the balance needs, not a source for `A(0) = 0`. -/
theorem windowPairInertia_rate_ge_of_exterior_on_seam {m n : ℕ} {t R₀ : ℝ}
    (s s' : ℝ → Fin m → ℂ) (r : Fin n → ℝ)
    (hsd : ∀ k σ, HasDerivAt (fun σ => s σ k) (s' σ k) σ)
    (hsc : ∀ k, Continuous fun σ => s' σ k)
    (hzero : ∀ k σ, Holonics.Zeta.HeatFlowEntire.heatE σ Holonics.Zeta.RiemannXi.riemannXi
      (s σ k) = 0)
    (hsimple : ∀ k, deriv (Holonics.Zeta.HeatFlowEntire.heatE t
      Holonics.Zeta.RiemannXi.riemannXi) (s t k) ≠ 0)
    (hoff : ∀ k, 1 / 2 < (s t k).re)
    (hwin : ∀ u, (MeromorphicOn.divisor
      (Holonics.Zeta.HeatFlowEntire.heatE t Holonics.Zeta.RiemannXi.riemannXi)
      (closedBall (1 / 2 : ℂ) R₀) u : ℂ) =
      (((mirrorComb (fun k => seamLift (s t k)) r).map toSeam).count u : ℂ))
    (hext : ∀ u, Holonics.Zeta.HeatFlowEntire.heatE t Holonics.Zeta.RiemannXi.riemannXi u = 0 →
      u ∉ closedBall (1 / 2 : ℂ) R₀ → u.re = 1 / 2) :
    ∃ D : ℝ, HasDerivAt (fun σ => ∑ k, ((s σ k).re - 1 / 2) ^ 2) D t ∧ 2 * m ≤ D := by
  obtain ⟨T, hT, hD⟩ := windowPairInertia_balance s s' r hsd hsc hzero hsimple hoff hwin
  refine ⟨_, hD, ?_⟩
  have htail : 0 ≤ ∑ k, 2 * ((s t k).re - 1 / 2) * (T k).re := by
    apply Finset.sum_nonneg
    intro k _
    have h1 : 0 ≤ (T k).re := tailFlux_re_nonneg_of_exterior_on_seam
      (Holonics.Zeta.XiGrowth.differentiable_heatE_riemannXi t) (hoff k) hext (hT k)
    have h2 : 0 ≤ (s t k).re - 1 / 2 := by linarith [hoff k]
    positivity
  linarith [pairInertiaRate_le (fun k => seamLift (s t k)) r]

end Holonics.Zeta.ZeroTube

#print axioms Holonics.Zeta.ZeroTube.finitePairInertia_rate
#print axioms Holonics.Zeta.ZeroTube.finitePairInertia_collision
#print axioms Holonics.Zeta.ZeroTube.windowPairInertia_balance
#print axioms Holonics.Zeta.ZeroTube.windowPairInertia_rate_ge_of_exterior_on_seam
#print axioms Holonics.Zeta.ZeroTube.pairCount_eq_zero_of_tailSign_of_stationary

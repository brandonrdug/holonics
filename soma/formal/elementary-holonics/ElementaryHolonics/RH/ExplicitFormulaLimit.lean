import ElementaryHolonics.RH.ExplicitFormulaFiniteHeight
import ElementaryHolonics.RH.FactorizationMultiplicity
import ElementaryHolonics.RH.EdgeIntegralVanishes

/-!
# The explicit formula in the limit

Along a sequence of selected heights `T_n ∈ [n + 2, n + 3]`, the weighted divisor sum of `ξ`
over the open rectangle `(−δ, 1 + δ) × (−T_n, T_n)` differs from the prime side (the two
prime-comb edges with weights `h(s)` and `h(1 − s)`, each the archimedean integral minus the
von Mangoldt sum) by the two horizontal edges, whose norm is `O(1/n)` for a weight of decay
`(1 + |t|)⁻⁵` on the strip.  The difference tends to zero: the zero comb is asymptotically the
prime comb, with the divisor of `ξ` and nothing else on the zero side.
-/

open Complex Metric Set Finset Filter Topology
open scoped Interval Classical
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.RiemannXiGrowth
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.XiEdgeDecomposition
open Soma.Holonics.RH.PrimeSideVertical
open Soma.Holonics.RH.ExplicitFormulaFiniteHeight
open Soma.Holonics.RH.FactorizationMultiplicity
open Soma.Holonics.RH.EdgeIntegralVanishes

namespace Soma.Holonics.RH.ExplicitFormulaLimit

theorem riemannXi_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : riemannXi s ≠ 0 := by
  rw [riemannXi_eq_mul_zeta hs]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (XiEdgeDecomposition.ne_zero_of_one_lt_re hs))
    (sub_ne_zero.mpr (XiEdgeDecomposition.ne_one_of_one_lt_re hs)))
    (Gammaℝ_ne_zero_of_re_pos (lt_trans zero_lt_one hs))) (riemannZeta_ne_zero_of_one_lt_re hs)

theorem riemannXi_ne_zero_of_re_lt_zero {s : ℂ} (hs : s.re < 0) : riemannXi s ≠ 0 := by
  rw [← riemannXi_one_sub]
  apply riemannXi_ne_zero_of_one_lt_re
  simp only [sub_re, one_re]
  linarith

theorem im_edge (σ t : ℝ) : (edge σ t).im = t := by simp [edge]

/-- The prime side of the explicit formula at height `T`, on the line `Re s = 1 + δ`. -/
noncomputable def primeSide (δ : ℝ) (h : ℂ → ℂ) (T : ℝ) : ℂ :=
  I • ((∫ t in (-T)..T, h (((1 + δ : ℝ) : ℂ) + t * I) * archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
      ∑' n, ∫ t in (-T)..T, h (((1 + δ : ℝ) : ℂ) + t * I) *
        LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n) +
    I • ((∫ t in (-T)..T, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) *
        archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
      ∑' n, ∫ t in (-T)..T, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) *
        LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n)

/-- The zero side: the divisor of `ξ` on the open rectangle, weighted by `h`. -/
noncomputable def zeroSide (δ : ℝ) (h : ℂ → ℂ) (T : ℝ) : ℂ :=
  ∑ᶠ u, (MeromorphicOn.divisor riemannXi (openRect (edge (-δ) (-T)) (edge (1 + δ) T)) u : ℂ) * h u

/-- The zeros of a factorization of `ξ` are zeros of `ξ`. -/
theorem riemannXi_eq_zero_of_mem {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (Z : ZeroFactorization riemannXi z₀ r) {ρ : ℂ} (hρ : ρ ∈ Z.zeros) : riemannXi ρ = 0 := by
  have hρr : ρ ∈ ball z₀ r := by
    have := Z.zeros_mem ρ hρ
    rw [mem_closedBall_iff_norm] at this
    rw [mem_ball_iff_norm]
    linarith
  rw [Z.factor ρ hρr]
  apply mul_eq_zero_of_left
  exact Finset.prod_eq_zero hρ (by
    rw [sub_self, zero_pow (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ hρ))])

/-- A boundary point of the rectangle lies on one of the four edges. -/
theorem boundaryRect_cases {z w ζ : ℂ} (hzw : z.re < w.re ∧ z.im < w.im)
    (hζ : ζ ∈ boundaryRect z w) :
    (ζ.re ∈ Icc z.re w.re ∧ ζ.im ∈ Icc z.im w.im) ∧
      (ζ.re = z.re ∨ ζ.re = w.re ∨ ζ.im = z.im ∨ ζ.im = w.im) := by
  obtain ⟨hc, ho⟩ := hζ
  rw [closedRect, Complex.mem_reProdIm, Set.uIcc_of_le hzw.1.le, Set.uIcc_of_le hzw.2.le] at hc
  rw [openRect, Complex.mem_reProdIm, min_eq_left hzw.1.le, max_eq_right hzw.1.le,
    min_eq_left hzw.2.le, max_eq_right hzw.2.le] at ho
  refine ⟨hc, ?_⟩
  by_contra hne
  push Not at hne
  apply ho
  constructor
  · exact ⟨lt_of_le_of_ne hc.1.1 (Ne.symm hne.1), lt_of_le_of_ne hc.1.2 hne.2.1⟩
  · exact ⟨lt_of_le_of_ne hc.2.1 (Ne.symm hne.2.2.1), lt_of_le_of_ne hc.2.2 hne.2.2.2⟩

/-- **The explicit formula at a selected height, with the divisor of `ξ` on the zero side.** -/
theorem explicit_formula_at_height {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ z : ℂ, Real.log ‖riemannXi z‖ ≤ C * (‖z‖ + 3) * Real.log (‖z‖ + 3))
    {δ : ℝ} (hδ : 0 < δ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ, ‖h (x + t * I)‖ ≤ K / (1 + |t|) ^ 5)
    {T₀ : ℝ} (hT₀ : 2 ≤ T₀) :
    ∃ T ∈ Icc T₀ (T₀ + 1),
      ‖2 * Real.pi * I * zeroSide δ h T - primeSide δ h T‖ ≤
        2 * (K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀)) := by
  obtain ⟨T, hT, hne, hbot, htop⟩ := exists_height_edges_small hC hgrowth hδ hK hdecay hT₀
  have hTpos : 0 < T := by linarith [hT.1]
  refine ⟨T, hT, ?_⟩
  set z : ℂ := edge (-δ) (-T) with hz
  set w : ℂ := edge (1 + δ) T with hw
  have hzre : z.re = -δ := by rw [hz, re_edge]
  have hwre : w.re = 1 + δ := by rw [hw, re_edge]
  have hzim : z.im = -T := by rw [hz, im_edge]
  have hwim : w.im = T := by rw [hw, im_edge]
  have hzw : z.re < w.re ∧ z.im < w.im := by
    rw [hzre, hwre, hzim, hwim]
    constructor <;> linarith
  have hr : 0 < 2 * (2 + δ + T) := by linarith
  obtain ⟨Z⟩ := exists_zeroFactorization_riemannXi_zero hr
  -- no zero of ξ on the boundary
  have hξb : ∀ ζ ∈ boundaryRect z w, riemannXi ζ ≠ 0 := by
    intro ζ hζ
    obtain ⟨⟨hre, him⟩, hcase⟩ := boundaryRect_cases hzw hζ
    rw [hzre, hwre] at hre
    rw [hzim, hwim] at him
    have hζeq : ζ = (ζ.re : ℂ) + (ζ.im : ℂ) * I := (Complex.re_add_im ζ).symm
    rcases hcase with hc | hc | hc | hc
    · exact riemannXi_ne_zero_of_re_lt_zero (by rw [hc, hzre]; linarith)
    · exact riemannXi_ne_zero_of_one_lt_re (by rw [hc, hwre]; linarith)
    · rw [hζeq, hc, hzim]
      exact (hne ζ.re hre).2
    · rw [hζeq, hc, hwim]
      exact (hne ζ.re hre).1
  have hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w :=
    fun ρ hρ hb => hξb ρ hb (riemannXi_eq_zero_of_mem hr Z hρ)
  have hmain := explicit_formula_finite_height hh hδ hTpos hzre hwre hzim hwim Z hbd
  -- the interior sum is the divisor sum
  have hU : openRect z w ⊆ ball (0 : ℂ) (2 * (2 + δ + T) / 2) :=
    (openRect_subset_closedRect z w).trans (closedRect_subset_ball hδ hTpos hzre hwre hzim hwim)
  have hdiv := finsum_divisor_eq Z differentiable_riemannXi.differentiableOn hr hU h
  rw [← hdiv] at hmain
  rw [hwre, hzim, hwim, hzre] at hmain
  have hzero : zeroSide δ h T = ∑ᶠ u, (MeromorphicOn.divisor riemannXi (openRect z w) u : ℂ) * h u := rfl
  have hprime : primeSide δ h T =
      I • ((∫ t in (-T)..T, h (((1 + δ : ℝ) : ℂ) + t * I) * archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
        ∑' n, ∫ t in (-T)..T, h (((1 + δ : ℝ) : ℂ) + t * I) *
          LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n) +
      I • ((∫ t in (-T)..T, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) *
          archimedean (((1 + δ : ℝ) : ℂ) + t * I)) -
        ∑' n, ∫ t in (-T)..T, h (1 - (((1 + δ : ℝ) : ℂ) + t * I)) *
          LSeries.term vonMangoldtC (((1 + δ : ℝ) : ℂ) + t * I) n) := rfl
  rw [hzero, hprime, hmain]
  have e : ∀ A B P Q : ℂ, A - B + P + Q - (P + Q) = A - B := fun A B P Q => by ring
  rw [e]
  calc ‖(∫ x : ℝ in (-δ)..(1 + δ), h (x + ((-T : ℝ) : ℂ) * I) *
          logDeriv riemannXi (x + ((-T : ℝ) : ℂ) * I)) -
        ∫ x : ℝ in (-δ)..(1 + δ), h (x + T * I) * logDeriv riemannXi (x + T * I)‖
      ≤ ‖∫ x : ℝ in (-δ)..(1 + δ), h (x + ((-T : ℝ) : ℂ) * I) *
          logDeriv riemannXi (x + ((-T : ℝ) : ℂ) * I)‖ +
        ‖∫ x : ℝ in (-δ)..(1 + δ), h (x + T * I) * logDeriv riemannXi (x + T * I)‖ :=
        norm_sub_le _ _
    _ ≤ K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) + K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀) :=
        add_le_add htop hbot
    _ = 2 * (K * edgeConst C δ * (1 + 2 * δ) / (1 + T₀)) := by ring

/-- **The explicit formula in the limit.**  For a weight of decay `(1 + |t|)⁻⁵` on the strip,
along heights `T_n ∈ [n + 2, n + 3]` the weighted divisor sum of `ξ` over the rectangle differs
from the prime side by a quantity tending to zero. -/
theorem explicit_formula_limit {δ : ℝ} (hδ : 0 < δ) {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {K : ℝ} (hK : 0 ≤ K)
    (hdecay : ∀ x ∈ Icc (-δ) (1 + δ), ∀ t : ℝ, ‖h (x + t * I)‖ ≤ K / (1 + |t|) ^ 5) :
    ∃ T : ℕ → ℝ, (∀ n : ℕ, T n ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 3)) ∧
      Tendsto (fun n => 2 * Real.pi * I * zeroSide δ h (T n) - primeSide δ h (T n)) atTop
        (𝓝 0) := by
  obtain ⟨C, hC, hgrowth⟩ := pointwiseAbscissaGrowthOfRiemannXiHolds
  have hex : ∀ n : ℕ, ∃ T ∈ Icc ((n : ℝ) + 2) ((n : ℝ) + 2 + 1),
      ‖2 * Real.pi * I * zeroSide δ h T - primeSide δ h T‖ ≤
        2 * (K * edgeConst C δ * (1 + 2 * δ) / (1 + ((n : ℝ) + 2))) := fun n =>
    explicit_formula_at_height hC hgrowth hδ hh hK hdecay (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  choose T hT hbound using hex
  refine ⟨T, fun n => ⟨(hT n).1, by linarith [(hT n).2]⟩, ?_⟩
  apply squeeze_zero_norm hbound
  have : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ) + 2)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have h0 := (tendsto_const_nhds (x := K * edgeConst C δ * (1 + 2 * δ))).div_atTop this
  have := h0.const_mul 2
  simpa using this

end Soma.Holonics.RH.ExplicitFormulaLimit

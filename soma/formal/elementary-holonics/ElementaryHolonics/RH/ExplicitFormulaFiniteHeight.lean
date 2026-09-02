import ElementaryHolonics.RH.RectangleArgumentPrinciple
import ElementaryHolonics.RH.XiEdgeDecomposition
import ElementaryHolonics.RH.ZeroFactorizationExists

/-!
# The explicit formula at finite height

On the rectangle `[−δ, 1 + δ] × [−T, T]`, whose boundary meets no zero of `ξ`, the weighted
zero comb inside equals the two horizontal edges plus the two prime-comb edges: the right edge
with the weight `h(s)` and the reflected left edge with the weight `h(1 − s)`, each written as
the archimedean integral minus the von Mangoldt sum.  Every piece is one of the previous owners:
the rectangle argument principle for the zero factorization of `ξ` on the disc about `0`, the
fold of the vertical edges, and the prime comb on the right edge.

The factorization of `ξ` on the disc exists because `ξ(0) = 1/2 ≠ 0`.
-/

open Complex Metric Set MeasureTheory intervalIntegral Finset
open scoped Interval Classical
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists
open Soma.Holonics.RH.RectangleCauchy
open Soma.Holonics.RH.RectangleArgumentPrinciple
open Soma.Holonics.RH.XiEdgeDecomposition
open Soma.Holonics.RH.PrimeSideVertical

namespace Soma.Holonics.RH.ExplicitFormulaFiniteHeight

/-- `ξ` factorizes on every disc about `0`, since `ξ(0) = 1/2`. -/
theorem exists_zeroFactorization_riemannXi_zero {r : ℝ} (hr : 0 < r) :
    Nonempty (ZeroFactorization riemannXi 0 r) :=
  exists_zeroFactorization differentiable_riemannXi hr
    (by rw [riemannXi_zero_and_one.1]; norm_num)

/-- The rectangle `[−δ, 1 + δ] × [−T, T]` lies in the open disc of radius `2 + δ + T` about `0`. -/
theorem closedRect_subset_ball {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) {z w : ℂ}
    (hzre : z.re = -δ) (hwre : w.re = 1 + δ) (hzim : z.im = -T) (hwim : w.im = T) :
    closedRect z w ⊆ ball (0 : ℂ) (2 * (2 + δ + T) / 2) := by
  intro ζ hζ
  rw [closedRect, Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le (by linarith),
    Set.uIcc_of_le (by linarith)] at hζ
  rw [mem_ball_zero_iff]
  calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := Complex.norm_le_abs_re_add_abs_im ζ
    _ ≤ (1 + δ) + T :=
        add_le_add (abs_le.mpr ⟨by linarith [hζ.1.1], hζ.1.2⟩) (abs_le.mpr ⟨hζ.2.1, hζ.2.2⟩)
    _ < 2 * (2 + δ + T) / 2 := by linarith

/-- **The explicit formula at finite height.**  For an entire weight `h`, the rectangle
`[−δ, 1 + δ] × [−T, T]` whose boundary meets no zero of the factorization, the weighted zero comb
inside equals the horizontal edges plus the two prime-comb edges. -/
theorem explicit_formula_finite_height {h : ℂ → ℂ} (hh : Differentiable ℂ h) {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 < T) {z w : ℂ} (hzre : z.re = -δ) (hwre : w.re = 1 + δ)
    (hzim : z.im = -T) (hwim : w.im = T)
    (Z : ZeroFactorization riemannXi 0 (2 * (2 + δ + T)))
    (hbd : ∀ ρ ∈ Z.zeros, ρ ∉ boundaryRect z w) :
    2 * Real.pi * I * ∑ ρ ∈ Z.zeros, (if ρ ∈ openRect z w then (Z.mult ρ : ℂ) * h ρ else 0) =
      (∫ x : ℝ in z.re..w.re, h (x + z.im * I) * logDeriv riemannXi (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, h (x + w.im * I) * logDeriv riemannXi (x + w.im * I)) +
      I • ((∫ t in z.im..w.im, h (w.re + t * I) * archimedean (w.re + t * I)) -
        ∑' n, ∫ t in z.im..w.im,
          h (w.re + t * I) * LSeries.term vonMangoldtC (w.re + t * I) n) +
      I • ((∫ t in z.im..w.im, h (1 - (w.re + t * I)) * archimedean (w.re + t * I)) -
        ∑' n, ∫ t in z.im..w.im,
          h (1 - (w.re + t * I)) * LSeries.term vonMangoldtC (w.re + t * I) n) := by
  have hr : 0 < 2 * (2 + δ + T) := by linarith
  have hzw : z.re < w.re ∧ z.im < w.im := by
    rw [hzre, hwre, hzim, hwim]
    constructor <;> linarith
  have hrect := closedRect_subset_ball hδ hT hzre hwre hzim hwim
  have hsym : z.re + w.re = 1 := by rw [hzre, hwre]; ring
  have hT' : z.im = -w.im := by rw [hzim, hwim]
  rw [← rectIntegral_mul_logDeriv Z hr hzw hrect hh.differentiableOn hbd,
    rectIntegral_riemannXi_fold hsym hT']
  have hσ : 1 < w.re := by rw [hwre]; linarith
  have hc : Continuous h := hh.continuous
  have e1 := (hasSum_right_edge hc hσ z.im w.im).tsum_eq
  have e2 := (hasSum_right_edge (g := fun s => h (1 - s)) (by fun_prop) hσ z.im w.im).tsum_eq
  unfold edge at e1 e2
  beta_reduce at e2
  rw [e1, e2]
  simp only [smul_eq_mul]
  ring

end Soma.Holonics.RH.ExplicitFormulaFiniteHeight

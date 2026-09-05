import Mathlib
import ElementaryHolonics.RH.HeatKernelPhi

/-!
# A positive-half-line folded theta source

This owner records the elementary term and its separated majorant.  The index is `n + 1`, so
`n : ℕ` represents a positive theta index without introducing a zero-index side condition.
No statement here performs the half-line integration or identifies the assembled kernel.
-/

noncomputable section

namespace Soma.Holonics.RH.FoldedSourceBounds

open Real Set Filter Topology MeasureTheory Complex
open Soma.Holonics.RH.HeatKernelPhi

/-- The positive-index folded theta summand on the positive half-line. -/
def foldedPhiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) -
      3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u)) *
    Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u))

/-- The flowed complex source term used by the pointwise majorant. -/
def foldedSourceTerm (t : ℝ) (z : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  (Real.exp (t * u ^ 2) : ℂ) * (foldedPhiTerm n u : ℂ) * Complex.cos (z * (u : ℂ))

theorem foldedPhiPolynomial_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) -
      3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hn2 : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by nlinarith
  have he4 : (1 : ℝ) ≤ Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpoly : 0 ≤
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) -
        3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) := by
    have hpi : (3 : ℝ) < π := Real.pi_gt_three
    have hfactor : 3 ≤ 2 * π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr he4)]
    have he9' : Real.exp (9 * u) = Real.exp (5 * u) * Real.exp (4 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he9']
    have hfac : 0 ≤ 2 * π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) - 3 := by
      linarith
    have hrewrite :
        2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * (Real.exp (5 * u) * Real.exp (4 * u)) -
            3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) =
          π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) *
            (2 * π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) - 3) := by ring
    rw [hrewrite]
    positivity
  exact hpoly

theorem foldedPhiTerm_nonneg {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ foldedPhiTerm n u := by
  unfold foldedPhiTerm
  exact mul_nonneg (foldedPhiPolynomial_nonneg hu) (Real.exp_pos _).le

theorem foldedPhiTerm_le_exp_source {n : ℕ} {u : ℝ} (hu : 0 ≤ u) :
    foldedPhiTerm n u ≤
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
        Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u)) := by
  unfold foldedPhiTerm
  have hpoly := foldedPhiPolynomial_nonneg (n := n) hu
  have hsub :
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) -
          3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) ≤
        2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) := by
    have : 0 ≤ 3 * π * (n + 1 : ℝ) ^ 2 * Real.exp (5 * u) := by positivity
    linarith
  exact mul_le_mul_of_nonneg_right hsub (Real.exp_pos _).le

/-! ## The elementary complex oscillatory factor -/

theorem norm_cos_le_exp_abs_im (w : ℂ) :
    ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  calc
    ‖Complex.cos w‖ = ‖(2 : ℂ) * Complex.cos w‖ / 2 := by norm_num
    _ = ‖Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)‖ / 2 := by
      rw [Complex.two_cos]
    _ ≤ (‖Complex.exp (w * Complex.I)‖ + ‖Complex.exp (-w * Complex.I)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ = (Real.exp (-w.im) + Real.exp (w.im)) / 2 := by
      rw [Complex.norm_exp, Complex.norm_exp]
      simp [Complex.mul_re]
    _ ≤ Real.exp |w.im| := by
      have h₁ : Real.exp (-w.im) ≤ Real.exp |w.im| :=
        Real.exp_le_exp.mpr (neg_le_abs _)
      have h₂ : Real.exp w.im ≤ Real.exp |w.im| :=
        Real.exp_le_exp.mpr (le_abs_self _)
      nlinarith [Real.exp_pos |w.im|]

theorem norm_cos_mul_real_le_exp {z : ℂ} {u : ℝ} :
    ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (|z.im| * |u|) := by
  have h := norm_cos_le_exp_abs_im (z * (u : ℂ))
  simpa [Complex.mul_im, abs_mul] using h

/-! ## The separated pointwise majorant -/

theorem norm_foldedSourceTerm_le
    {T R t : ℝ} {z : ℂ} {n : ℕ} {u : ℝ}
    (_hT : 0 ≤ T) (hR : 0 ≤ R) (hu : 0 ≤ u)
    (ht : |t| ≤ T) (hz : |z.im| ≤ R) :
    ‖foldedSourceTerm t z n u‖ ≤
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
        Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2) := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      linarith
    nlinarith
  have he : (1 : ℝ) ≤ Real.exp (4 * u) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hsplit :
      (n + 1 : ℝ) ^ 2 / 2 + Real.exp (4 * u) / 2 ≤
        (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) := by
    have hprod : 0 ≤ ((n + 1 : ℝ) ^ 2 - 1) * (Real.exp (4 * u) - 1) :=
      mul_nonneg (sub_nonneg.mpr hn) (sub_nonneg.mpr he)
    have hboth : 1 ≤ (n + 1 : ℝ) ^ 2 * Real.exp (4 * u) := by
      simpa using (mul_le_mul hn he (by positivity) (by positivity))
    nlinarith
  have hexp_split :
      Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u)) ≤
        Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
          Real.exp (-π * Real.exp (4 * u) / 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hphi := foldedPhiTerm_le_exp_source (n := n) hu
  have hcos : ‖Complex.cos (z * (u : ℂ))‖ ≤ Real.exp (R * u) := by
    apply le_trans norm_cos_mul_real_le_exp
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hu]
    exact mul_le_mul hz le_rfl (by positivity) hR
  unfold foldedSourceTerm
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (foldedPhiTerm_nonneg hu)]
  have ht' : t * u ^ 2 ≤ T * u ^ 2 := by
    apply mul_le_mul_of_nonneg_right
    exact (le_trans (le_abs_self t) ht)
    positivity
  have hbase :
      foldedPhiTerm n u ≤
        2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
          (Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
            Real.exp (-π * Real.exp (4 * u) / 2)) := by
    calc
      foldedPhiTerm n u ≤
          2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
            Real.exp (-π * (n + 1 : ℝ) ^ 2 * Real.exp (4 * u)) := hphi
      _ ≤ 2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
          (Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
            Real.exp (-π * Real.exp (4 * u) / 2)) := by
        gcongr
  calc
    Real.exp (t * u ^ 2) * foldedPhiTerm n u * ‖Complex.cos (z * (u : ℂ))‖ ≤
        Real.exp (t * u ^ 2) *
          (2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
            (Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
              Real.exp (-π * Real.exp (4 * u) / 2))) * Real.exp (R * u) := by
      gcongr
    _ ≤ Real.exp (T * u ^ 2) *
          (2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (9 * u) *
            (Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
              Real.exp (-π * Real.exp (4 * u) / 2))) * Real.exp (R * u) := by
      gcongr
    _ = 2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2) *
        Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2) := by
      have hexp : Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2) =
          Real.exp (T * u ^ 2) * Real.exp (9 * u) * Real.exp (R * u) *
            Real.exp (-π * Real.exp (4 * u) / 2) := by
        have harg : T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2 =
            T * u ^ 2 + 9 * u + R * u + (-π * Real.exp (4 * u) / 2) := by ring
        rw [harg, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [hexp]
      ring

/-! ## The separated summable and integrable factors -/

theorem summable_foldedPhiCoefficient :
    Summable (fun n : ℕ ↦
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2)) := by
  have hZ := summable_pow_mul_exp_neg_sq (c := π / 2) (by positivity) 4
  have hN : Summable (fun n : ℕ ↦
      |((n : ℤ) : ℝ)| ^ 4 * Real.exp (-(π / 2) * ((n : ℤ) : ℝ) ^ 2)) := by
    exact hZ.comp_injective Int.ofNat_injective
  have hN' : Summable (fun n : ℕ ↦
      (n : ℝ) ^ 4 * Real.exp (-(π / 2) * (n : ℝ) ^ 2)) := by
    have heq : (fun n : ℕ ↦ |((n : ℤ) : ℝ)| ^ 4 *
        Real.exp (-(π / 2) * ((n : ℤ) : ℝ) ^ 2)) =
        (fun n : ℕ ↦ (n : ℝ) ^ 4 * Real.exp (-(π / 2) * (n : ℝ) ^ 2)) := by
      funext n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      norm_num [Int.cast_natCast, abs_of_nonneg hn0]
    exact heq ▸ hN
  have hshift : Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(π / 2) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hN'
  have hshift' : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ 4 * Real.exp (-(π / 2) * (n + 1 : ℝ) ^ 2)) := by
    simpa using hshift
  have hfun : (fun n : ℕ ↦
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2)) =
      (fun n : ℕ ↦ 2 * π ^ 2 * ((n + 1 : ℝ) ^ 4 *
        Real.exp (-(π / 2) * (n + 1 : ℝ) ^ 2))) := by
    funext n
    ring_nf
  rw [hfun]
  exact hshift'.mul_left (2 * π ^ 2)

/-- The quarter-Gaussian coefficient used to control coefficient tails. -/
def foldedQuarterCoefficient (n : ℕ) : ℝ :=
  2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 4)

/-- The full quarter-Gaussian coefficient sum. -/
def foldedQuarterConstant : ℝ := ∑' n : ℕ, foldedQuarterCoefficient n

theorem summable_foldedQuarterCoefficient : Summable foldedQuarterCoefficient := by
  have hZ := summable_pow_mul_exp_neg_sq (c := π / 4) (by positivity) 4
  have hN : Summable (fun n : ℕ ↦
      |((n : ℤ) : ℝ)| ^ 4 * Real.exp (-(π / 4) * ((n : ℤ) : ℝ) ^ 2)) := by
    exact hZ.comp_injective Int.ofNat_injective
  have hN' : Summable (fun n : ℕ ↦
      (n : ℝ) ^ 4 * Real.exp (-(π / 4) * (n : ℝ) ^ 2)) := by
    have heq : (fun n : ℕ ↦ |((n : ℤ) : ℝ)| ^ 4 *
        Real.exp (-(π / 4) * ((n : ℤ) : ℝ) ^ 2)) =
        (fun n : ℕ ↦ (n : ℝ) ^ 4 * Real.exp (-(π / 4) * (n : ℝ) ^ 2)) := by
      funext n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      norm_num [Int.cast_natCast, abs_of_nonneg hn0]
    exact heq ▸ hN
  have hshift : Summable (fun n : ℕ ↦
      ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(π / 4) * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr hN'
  have hshift' : Summable (fun n : ℕ ↦
      (n + 1 : ℝ) ^ 4 * Real.exp (-(π / 4) * (n + 1 : ℝ) ^ 2)) := by
    simpa using hshift
  change Summable (fun n : ℕ ↦
    2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 4))
  have hfun : (fun n : ℕ ↦
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 4)) =
      (fun n : ℕ ↦ 2 * π ^ 2 * ((n + 1 : ℝ) ^ 4 *
        Real.exp (-(π / 4) * (n + 1 : ℝ) ^ 2))) := by
    funext n
    ring_nf
  rw [hfun]
  exact hshift'.mul_left (2 * π ^ 2)

theorem foldedQuarterCoefficient_nonneg (n : ℕ) : 0 ≤ foldedQuarterCoefficient n := by
  unfold foldedQuarterCoefficient
  positivity

theorem foldedQuarterConstant_nonneg : 0 ≤ foldedQuarterConstant := by
  unfold foldedQuarterConstant
  exact tsum_nonneg (fun n => foldedQuarterCoefficient_nonneg n)

theorem foldedPhiCoefficient_tail_le (N : ℕ) :
    (∑' j : ℕ, 2 * π ^ 2 * (j + N + 1 : ℝ) ^ 4 *
      Real.exp (-π * (j + N + 1 : ℝ) ^ 2 / 2)) ≤
      foldedQuarterConstant * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4) := by
  let half : ℕ → ℝ := fun n =>
    2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2)
  let quarter : ℕ → ℝ := fun n => foldedQuarterCoefficient n
  have hhalf : Summable half := by
    change Summable (fun n : ℕ =>
      2 * π ^ 2 * (n + 1 : ℝ) ^ 4 * Real.exp (-π * (n + 1 : ℝ) ^ 2 / 2))
    exact summable_foldedPhiCoefficient
  have hquarter : Summable quarter := by
    exact summable_foldedQuarterCoefficient
  have hquarterTail : Summable (fun j : ℕ => quarter (j + N)) :=
    (summable_nat_add_iff N).mpr hquarter
  let factor : ℝ := Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4)
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  have hterm : ∀ j : ℕ, half (j + N) ≤ quarter (j + N) * factor := by
    intro j
    have hsq : ((N : ℝ) + 1) ^ 2 ≤ (((j + N : ℕ) : ℝ) + 1) ^ 2 := by
      have hj : (0 : ℝ) ≤ j := by positivity
      have hN : (0 : ℝ) ≤ N := by positivity
      have hbase : (N : ℝ) + 1 ≤ ((j + N : ℕ) : ℝ) + 1 := by
        norm_num [Nat.cast_add]
      have hprod : 0 ≤ (((j + N : ℕ) : ℝ) + 1 - ((N : ℝ) + 1)) *
          (((j + N : ℕ) : ℝ) + 1 + ((N : ℝ) + 1)) := by positivity
      nlinarith
    have hexp : Real.exp (-π * (((j + N : ℕ) : ℝ) + 1) ^ 2 / 2) ≤
        Real.exp (-π * (((j + N : ℕ) : ℝ) + 1) ^ 2 / 4) * factor := by
      dsimp [factor]
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos, hsq]
    dsimp [half, quarter]
    calc
      2 * π ^ 2 * (↑(j + N) + 1) ^ 4 *
          Real.exp (-π * (↑(j + N) + 1) ^ 2 / 2) =
          (2 * π ^ 2 * (↑(j + N) + 1) ^ 4 *
            Real.exp (-π * (↑(j + N) + 1) ^ 2 / 4)) *
            Real.exp (-π * (↑(j + N) + 1) ^ 2 / 4) := by
              have heq : Real.exp (-π * (↑(j + N) + 1) ^ 2 / 2) =
                  Real.exp (-π * (↑(j + N) + 1) ^ 2 / 4) *
                    Real.exp (-π * (↑(j + N) + 1) ^ 2 / 4) := by
                rw [← Real.exp_add]
                congr 1
                ring
              rw [heq]
              ring
      _ ≤ (2 * π ^ 2 * (↑(j + N) + 1) ^ 4 *
            Real.exp (-π * (↑(j + N) + 1) ^ 2 / 4)) * factor := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.mpr
              nlinarith [Real.pi_pos, hsq]
      _ = foldedQuarterCoefficient (j + N) * factor := by rfl
  have hquarterC : (∑' j : ℕ, quarter (j + N)) ≤ foldedQuarterConstant := by
    have hsum : HasSum (fun j : ℕ => quarter (j + N))
        (foldedQuarterConstant - ∑ i ∈ Finset.range N, quarter i) := by
      apply (hasSum_nat_add_iff N).2
      have hfull : HasSum quarter foldedQuarterConstant := by
        exact (summable_foldedQuarterCoefficient.hasSum)
      convert hfull using 1 <;> first | rfl | ring
    rw [hsum.tsum_eq]
    have hprefix : 0 ≤ ∑ i ∈ Finset.range N, quarter i := by
      exact Finset.sum_nonneg (fun i _ => foldedQuarterCoefficient_nonneg i)
    linarith
  have hright : Summable (fun j : ℕ => quarter (j + N) * factor) :=
    hquarterTail.mul_right factor
  have hcalc : (∑' j : ℕ, half (j + N)) ≤
      foldedQuarterConstant * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4) := by
    calc
    (∑' j : ℕ, half (j + N)) ≤ ∑' j : ℕ, quarter (j + N) * factor :=
      Summable.tsum_le_tsum hterm ((summable_nat_add_iff N).mpr hhalf) hright
    _ = (∑' j : ℕ, quarter (j + N)) * factor := by rw [tsum_mul_right]
    _ ≤ foldedQuarterConstant * factor := by
      exact mul_le_mul_of_nonneg_right hquarterC hfactor
    _ = foldedQuarterConstant * Real.exp (-π * (N + 1 : ℝ) ^ 2 / 4) := by rfl
  simpa [half, Nat.cast_add] using hcalc

theorem integrableOn_foldedSourceMajorant {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) :
    IntegrableOn
      (fun u : ℝ => Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2))
      (Ioi 0) := by
  let K : ℝ := (T + 1 + (R + 9)) + (T + 1 + (R + 9)) ^ 2
  have hgauss : Integrable (fun u : ℝ => Real.exp K * Real.exp (-u ^ 2)) := by
    convert (integrable_exp_neg_mul_sq one_pos).const_mul (Real.exp K) using 1
    funext u
    ring_nf
  have hcont : Continuous
      (fun u : ℝ => Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2)) := by
    fun_prop
  change Integrable
    (fun u : ℝ => Real.exp (T * u ^ 2 + (R + 9) * u - π * Real.exp (4 * u) / 2))
    (volume.restrict (Ioi 0))
  refine (hgauss.mono_measure Measure.restrict_le_self).mono' hcont.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu0 : 0 ≤ u := hu.le
  have hquart : u ^ 4 ≤ π / 2 * Real.exp (4 * u) := by
    have hfac := Real.pow_div_factorial_le_exp (4 * u) (by positivity) 4
    norm_num [Nat.factorial] at hfac
    have hrewrite : (4 * u) ^ 4 / 24 = (32 / 3 : ℝ) * u ^ 4 := by ring
    rw [hrewrite] at hfac
    have hpi := Real.pi_gt_three
    have hfac' : u ^ 4 ≤ (3 / 32 : ℝ) * Real.exp (4 * u) := by
      nlinarith
    have hconst : (3 / 32 : ℝ) ≤ π / 2 := by nlinarith
    have hconst' := mul_le_mul_of_nonneg_right hconst (Real.exp_pos (4 * u)).le
    nlinarith
  have hdom := quartic_dominates (A := T + 1) (B := R + 9)
    (by linarith) (by linarith) u
  rw [abs_of_nonneg hu0] at hdom
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [K]
  nlinarith

section Audit

#print axioms foldedPhiTerm_nonneg
#print axioms foldedPhiTerm_le_exp_source
#print axioms norm_cos_le_exp_abs_im
#print axioms norm_foldedSourceTerm_le
#print axioms summable_foldedPhiCoefficient
#print axioms integrableOn_foldedSourceMajorant
#print axioms summable_foldedQuarterCoefficient
#print axioms foldedQuarterCoefficient_nonneg
#print axioms foldedQuarterConstant_nonneg
#print axioms foldedPhiCoefficient_tail_le

end Audit

end Soma.Holonics.RH.FoldedSourceBounds

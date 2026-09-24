import Mathlib
import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.ZeroComb
import ElementaryHolonics.RH.FosterCount

/-!
# FT2: the paired canonical product of the zeros of `ξ`

Over the zeros of `ξ` repeated by multiplicity, `Idx := Σ u : Zero, Fin m_u`, the paired factor
`1 − ((z − ½)/(u − ½))²` vanishes exactly at the pair `{u, 1 − u}`.  Its norm on the disc of radius
`R` about `½` is at most `R² / |u − ½|²`, and `Σ m_u |u − ½|^{−2} < ∞` (`FosterCount`), so the product

```text
P(z) = ∏'_{i : Idx} (1 − ((z − ½)/(u_i − ½))²)
```

converges locally uniformly on every disc.  This owner returns: `P` is entire; `P(1 − z) = P(z)`;
`P` vanishes at every zero of `ξ` and nowhere else; and off the zeros its logarithmic derivative is
the convergent Foster series `Σ_u m_u · 2(z − ½)/((z − ½)² − (u − ½)²)`, the sum over all zeros
of the tank of the pair counted from both members.  Each pair contributes twice to `P`, so `P` is
the paired product squared; FT3 compares `P` with `ξ²`.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterProduct

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.FosterCount

/-! ## The index and the factor -/

/-- The zeros repeated by multiplicity. -/
abbrev Idx := Σ u : Zero, Fin (mult (u : ℂ)).toNat

/-- The centred zero of an index. -/
def ctr (i : Idx) : ℂ := ((i.1 : Zero) : ℂ) - 1 / 2

theorem ctr_ne_zero (i : Idx) : ctr i ≠ 0 := sub_ne_zero.mpr (i.1).ne_half

theorem norm_ctr_pos (i : Idx) : 0 < ‖ctr i‖ := norm_pos_iff.mpr (ctr_ne_zero i)

/-- The paired term `−((z − ½)/(u − ½))²`. -/
def a (i : Idx) (z : ℂ) : ℂ := -(((z - 1 / 2) / ctr i) ^ 2)

theorem a_symm (i : Idx) (z : ℂ) : a i (1 - z) = a i z := by
  unfold a
  have : (1 - z - 1 / 2) / ctr i = -((z - 1 / 2) / ctr i) := by ring
  rw [this, neg_sq]

theorem norm_a (i : Idx) (z : ℂ) : ‖a i z‖ = ‖z - 1 / 2‖ ^ 2 * invSq ((i.1 : Zero) : ℂ) := by
  unfold a invSq ctr
  rw [norm_neg, norm_pow, norm_div, div_pow]
  rfl

theorem continuous_a (i : Idx) : Continuous (a i) := by
  unfold a
  fun_prop

theorem differentiable_a (i : Idx) : Differentiable ℂ (a i) := by
  unfold a
  fun_prop

/-- The factor as a quotient of the two members of the pair. -/
theorem one_add_a_eq (i : Idx) (z : ℂ) :
    1 + a i z = (ctr i - (z - 1 / 2)) * (ctr i + (z - 1 / 2)) / ctr i ^ 2 := by
  have hc : ctr i ≠ 0 := ctr_ne_zero i
  unfold a
  field_simp
  ring

/-- The factor vanishes exactly at the pair of its zero. -/
theorem one_add_a_eq_zero_iff (i : Idx) (z : ℂ) :
    1 + a i z = 0 ↔ z = ((i.1 : Zero) : ℂ) ∨ z = 1 - ((i.1 : Zero) : ℂ) := by
  have hc : ctr i ≠ 0 := ctr_ne_zero i
  rw [one_add_a_eq, div_eq_zero_iff, or_iff_left (pow_ne_zero 2 hc), mul_eq_zero, sub_eq_zero,
    add_eq_zero_iff_eq_neg]
  unfold ctr
  constructor
  · rintro (h | h)
    · left
      linear_combination -h
    · right
      linear_combination h
  · rintro (h | h)
    · left
      rw [h]
    · right
      rw [h]
      ring

/-! ## Summability over the repeated index -/

theorem mult_toNat_pos (u : Zero) : 0 < (mult (u : ℂ)).toNat := by
  have h1 := mult_nonneg (u : ℂ)
  have h2 := u.2
  omega

/-- A nonnegative function of the zero, summed over the repeated index, is the multiplicity-weighted
sum over the zeros. -/
theorem summable_idx_of_summable {h : Zero → ℝ} (hh : ∀ u, 0 ≤ h u)
    (hs : Summable (fun u : Zero => ((mult (u : ℂ)).toNat : ℝ) * h u)) :
    Summable (fun i : Idx => h i.1) := by
  have hnn : ∀ i : Idx, 0 ≤ (fun i : Idx => h i.1) i := fun i => hh i.1
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun u => Summable.of_finite, ?_⟩
  refine hs.congr ?_
  intro u
  simp [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The multiplicity-weighted inverse squares, over the zeros. -/
theorem summable_mult_invSq : Summable (fun u : Zero => ((mult (u : ℂ)).toNat : ℝ) * invSq (u : ℂ)) := by
  refine summable_inverse_square.congr ?_
  intro u
  unfold term
  congr 1
  have := mult_nonneg (u : ℂ)
  exact_mod_cast (Int.toNat_of_nonneg this).symm

/-- The norm of the paired term is summable over the repeated index, at every point. -/
theorem summable_norm_a (z : ℂ) : Summable (fun i : Idx => ‖a i z‖) := by
  have h := summable_idx_of_summable (h := fun u => ‖z - 1 / 2‖ ^ 2 * invSq (u : ℂ))
    (fun u => mul_nonneg (by positivity) (invSq_nonneg _)) (by
      have := summable_mult_invSq.mul_left (‖z - 1 / 2‖ ^ 2)
      refine this.congr ?_
      intro u
      ring)
  refine h.congr ?_
  intro i
  rw [norm_a]

/-- The uniform majorant on the disc of radius `R`. -/
theorem summable_majorant_disc (R : ℝ) :
    Summable (fun i : Idx => R ^ 2 * invSq ((i.1 : Zero) : ℂ)) :=
  summable_idx_of_summable (h := fun u => R ^ 2 * invSq (u : ℂ))
    (fun u => mul_nonneg (by positivity) (invSq_nonneg _)) (by
    have := summable_mult_invSq.mul_left (R ^ 2)
    refine this.congr ?_
    intro u
    ring)

theorem norm_a_le_of_mem_ball {R : ℝ} {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) R) (i : Idx) :
    ‖a i z‖ ≤ R ^ 2 * invSq ((i.1 : Zero) : ℂ) := by
  rw [norm_a]
  have hd : ‖z - 1 / 2‖ < R := by
    rw [mem_ball, Complex.dist_eq] at hz
    exact hz
  have h0 : 0 ≤ ‖z - 1 / 2‖ := norm_nonneg _
  have hsq : ‖z - 1 / 2‖ ^ 2 ≤ R ^ 2 := by nlinarith
  exact mul_le_mul_of_nonneg_right hsq (invSq_nonneg _)

/-! ## The product -/

/-- **The paired canonical product.** -/
def P (z : ℂ) : ℂ := ∏' i : Idx, (1 + a i z)

theorem multipliable_factors (z : ℂ) : Multipliable (fun i : Idx => 1 + a i z) :=
  multipliable_one_add_of_summable (summable_norm_a z)

/-- The product converges locally uniformly on every centred disc. -/
theorem hasProdLocallyUniformlyOn (R : ℝ) :
    HasProdLocallyUniformlyOn (fun i x => 1 + a i x) P (ball (1 / 2 : ℂ) R) :=
  Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball (summable_majorant_disc R)
    (Eventually.of_forall fun i x hx => norm_a_le_of_mem_ball hx i)
    (fun i => (continuous_a i).continuousOn)

theorem multipliableLocallyUniformlyOn (R : ℝ) :
    MultipliableLocallyUniformlyOn (fun i x => 1 + a i x) (ball (1 / 2 : ℂ) R) :=
  ⟨P, hasProdLocallyUniformlyOn R⟩

/-- **`P` is entire.** -/
theorem differentiable_P : Differentiable ℂ P := by
  intro z
  set R : ℝ := ‖z - 1 / 2‖ + 1 with hR
  have hz : z ∈ ball (1 / 2 : ℂ) R := by
    rw [mem_ball, Complex.dist_eq, hR]
    linarith
  have hloc := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn).mp
    (hasProdLocallyUniformlyOn R)
  have hdiff : DifferentiableOn ℂ P (ball (1 / 2 : ℂ) R) := by
    refine hloc.differentiableOn ?_ isOpen_ball
    refine Eventually.of_forall fun t => ?_
    apply Differentiable.differentiableOn
    have hfun : (fun x : ℂ => ∏ i ∈ t, (1 + a i x)) = ∏ i ∈ t, (fun x : ℂ => 1 + a i x) := by
      funext x
      rw [Finset.prod_apply]
    rw [hfun]
    apply Differentiable.finset_prod
    intro i _
    exact (differentiable_const _).add (differentiable_a i)
  exact hdiff.differentiableAt (isOpen_ball.mem_nhds hz)

/-- **`P` is reflection symmetric.** -/
theorem P_symm (z : ℂ) : P (1 - z) = P z := by
  unfold P
  congr 1
  funext i
  rw [a_symm]

/-- **`P` vanishes at every zero of `ξ`.** -/
theorem P_eq_zero (u : Zero) : P (u : ℂ) = 0 := by
  have hi₀ : 1 + a ⟨u, ⟨0, mult_toNat_pos u⟩⟩ (u : ℂ) = 0 :=
    (one_add_a_eq_zero_iff ⟨u, ⟨0, mult_toNat_pos u⟩⟩ (u : ℂ)).mpr (Or.inl rfl)
  have h0 : HasProd (fun i : Idx => 1 + a i (u : ℂ)) 0 := by
    show Tendsto (fun s : Finset Idx => ∏ i ∈ s, (1 + a i (u : ℂ))) atTop (𝓝 0)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ({⟨u, ⟨0, mult_toNat_pos u⟩⟩} : Finset Idx)]
      with s hs
    exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self _)) hi₀).symm
  exact h0.tprod_eq

/-- The reflection of a zero has the same multiplicity. -/
theorem mult_one_sub (u : ℂ) : mult (1 - u) = mult u := by
  unfold mult
  rw [meromorphicOrderAt_riemannXi_one_sub]

/-- Off the zeros every factor is nonzero. -/
theorem one_add_a_ne_zero {z : ℂ} (hz : mult z = 0) (i : Idx) : 1 + a i z ≠ 0 := by
  intro h
  rcases (one_add_a_eq_zero_iff i z).mp h with h1 | h1
  · exact (i.1).2 (h1 ▸ hz)
  · apply (i.1).2
    have : mult (1 - ((i.1 : Zero) : ℂ)) = 0 := by
      rw [← h1]
      exact hz
    rwa [mult_one_sub] at this

/-- **`P` vanishes nowhere else.** -/
theorem P_ne_zero {z : ℂ} (hz : mult z = 0) : P z ≠ 0 :=
  tprod_one_add_ne_zero_of_summable (one_add_a_ne_zero hz) (summable_norm_a z)

/-! ## The finite population inside a disc -/

/-- Finitely many zeros lie inside any disc. -/
theorem finite_zero_ball (r : ℝ) : {u : Zero | ‖(u : ℂ) - 1 / 2‖ < r}.Finite := by
  classical
  have hfin := (MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) r)).finiteSupport
    (isCompact_closedBall _ _)
  refine (hfin.preimage (Subtype.val_injective.injOn)).subset ?_
  intro u hu
  simp only [mem_setOf_eq] at hu
  show (u : ℂ) ∈ Function.support (MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) r))
  rw [Function.mem_support]
  have hmem : (u : ℂ) ∈ closedBall (1 / 2 : ℂ) r := by
    rw [mem_closedBall, Complex.dist_eq]
    exact hu.le
  rw [mult_eq_divisor hmem]
  exact u.2

theorem finite_idx_ball (r : ℝ) : {i : Idx | ‖ctr i‖ < r}.Finite := by
  have h := (finite_zero_ball r).biUnion
    (t := fun u : Zero => Set.range (fun j : Fin (mult (u : ℂ)).toNat => (⟨u, j⟩ : Idx)))
    (fun _ _ => Set.finite_range _)
  refine h.subset ?_
  intro i hi
  simp only [mem_setOf_eq] at hi
  exact Set.mem_biUnion (x := i.1) hi (Set.mem_range.mpr ⟨i.2, rfl⟩)

/-! ## The logarithmic derivative -/

/-- The tank of an index at `z`. -/
def tank (i : Idx) (z : ℂ) : ℂ := 2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 - ctr i ^ 2)

/-- The logarithmic derivative of one factor is its tank. -/
theorem logDeriv_factor {z : ℂ} (i : Idx) (hz : 1 + a i z ≠ 0) :
    logDeriv (fun w => 1 + a i w) z = tank i z := by
  have hc : ctr i ≠ 0 := ctr_ne_zero i
  set c : ℂ := -1 / ctr i ^ 2 with hcdef
  have ha : (fun w => 1 + a i w) = fun w => 1 + c * ((w - 1 / 2) * (w - 1 / 2)) := by
    funext w
    unfold a
    rw [hcdef]
    field_simp
    all_goals ring
  have hderiv : HasDerivAt (fun w => 1 + c * ((w - 1 / 2) * (w - 1 / 2)))
      (c * (1 * (z - 1 / 2) + (z - 1 / 2) * 1)) z := by
    have h1 : HasDerivAt (fun w : ℂ => w - 1 / 2) 1 z := (hasDerivAt_id z).sub_const _
    exact ((h1.mul h1).const_mul c).const_add 1
  have hden : (z - 1 / 2) ^ 2 - ctr i ^ 2 ≠ 0 := by
    intro h0
    apply hz
    rw [one_add_a_eq]
    have : (ctr i - (z - 1 / 2)) * (ctr i + (z - 1 / 2)) = ctr i ^ 2 - (z - 1 / 2) ^ 2 := by ring
    rw [this, div_eq_zero_iff]
    left
    linear_combination -h0
  have hden' : ctr i ^ 2 - (z - 1 / 2) ^ 2 ≠ 0 := by
    intro h0
    apply hden
    linear_combination -h0
  rw [ha, logDeriv_apply, hderiv.deriv]
  unfold tank
  have hnum : c * (1 * (z - 1 / 2) + (z - 1 / 2) * 1) = -(2 * (z - 1 / 2)) / ctr i ^ 2 := by
    rw [hcdef]
    ring
  have hd : 1 + c * ((z - 1 / 2) * (z - 1 / 2)) = (ctr i ^ 2 - (z - 1 / 2) ^ 2) / ctr i ^ 2 := by
    rw [hcdef, eq_div_iff (pow_ne_zero 2 hc)]
    field_simp
    all_goals ring
  rw [hnum, hd, div_div_div_cancel_right₀ (pow_ne_zero 2 hc), div_eq_div_iff hden' hden]
  ring

/-- The tank is bounded by `4 |z − ½| / |u − ½|²` once `|u − ½|² ≥ 2 |z − ½|²`. -/
theorem norm_tank_le {z : ℂ} {i : Idx} (h : 2 * ‖z - 1 / 2‖ ^ 2 ≤ ‖ctr i‖ ^ 2) :
    ‖tank i z‖ ≤ 4 * ‖z - 1 / 2‖ * invSq ((i.1 : Zero) : ℂ) := by
  unfold tank invSq
  have hc : 0 < ‖ctr i‖ := norm_ctr_pos i
  have hden : ‖ctr i‖ ^ 2 / 2 ≤ ‖(z - 1 / 2) ^ 2 - ctr i ^ 2‖ := by
    calc ‖ctr i‖ ^ 2 / 2 ≤ ‖ctr i‖ ^ 2 - ‖z - 1 / 2‖ ^ 2 := by linarith
      _ = ‖ctr i ^ 2‖ - ‖(z - 1 / 2) ^ 2‖ := by rw [norm_pow, norm_pow]
      _ ≤ ‖(z - 1 / 2) ^ 2 - ctr i ^ 2‖ := by
          have := norm_sub_norm_le (ctr i ^ 2) ((z - 1 / 2) ^ 2)
          rw [norm_sub_rev] at this
          linarith
  have hden0 : 0 < ‖(z - 1 / 2) ^ 2 - ctr i ^ 2‖ := by
    have : 0 < ‖ctr i‖ ^ 2 / 2 := by positivity
    linarith
  rw [norm_div, norm_mul, Complex.norm_ofNat]
  have hctr : ctr i = ((i.1 : Zero) : ℂ) - 1 / 2 := rfl
  rw [div_le_iff₀ hden0]
  calc 2 * ‖z - 1 / 2‖ = 4 * ‖z - 1 / 2‖ * (‖ctr i‖ ^ 2)⁻¹ * (‖ctr i‖ ^ 2 / 2) := by
        field_simp
        ring
    _ ≤ 4 * ‖z - 1 / 2‖ * (‖ctr i‖ ^ 2)⁻¹ * ‖(z - 1 / 2) ^ 2 - ctr i ^ 2‖ := by
        gcongr
    _ = 4 * ‖z - 1 / 2‖ * (‖((i.1 : Zero) : ℂ) - 1 / 2‖ ^ 2)⁻¹ *
          ‖(z - 1 / 2) ^ 2 - ctr i ^ 2‖ := by rw [hctr]

/-- The tanks are summable at every point. -/
theorem summable_tank (z : ℂ) : Summable (fun i : Idx => tank i z) := by
  have hmaj : Summable (fun i : Idx => 4 * ‖z - 1 / 2‖ * invSq ((i.1 : Zero) : ℂ)) :=
    summable_idx_of_summable (h := fun u => 4 * ‖z - 1 / 2‖ * invSq (u : ℂ))
      (fun u => mul_nonneg (by positivity) (invSq_nonneg _)) (by
        have := summable_mult_invSq.mul_left (4 * ‖z - 1 / 2‖)
        refine this.congr ?_
        intro u
        ring)
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin := finite_idx_ball (Real.sqrt 2 * ‖z - 1 / 2‖)
  rw [eventually_cofinite]
  refine hfin.subset ?_
  intro i hi
  simp only [mem_setOf_eq] at hi ⊢
  by_contra hlt
  push_neg at hlt
  apply hi
  apply norm_tank_le
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h0 : 0 ≤ ‖z - 1 / 2‖ := norm_nonneg _
  have hs : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc 2 * ‖z - 1 / 2‖ ^ 2 = (Real.sqrt 2 * ‖z - 1 / 2‖) ^ 2 := by rw [mul_pow, h2]
    _ ≤ ‖ctr i‖ ^ 2 := by gcongr

/-- **FT2: the logarithmic derivative of `P` is the Foster series.**  Off the zeros of `ξ`,
`P′/P(z) = Σ_i 2(z − ½)/((z − ½)² − (u_i − ½)²)` over the repeated index. -/
theorem logDeriv_P {z : ℂ} (hz : mult z = 0) : logDeriv P z = ∑' i : Idx, tank i z := by
  set R : ℝ := ‖z - 1 / 2‖ + 1 with hR
  have hzR : z ∈ ball (1 / 2 : ℂ) R := by
    rw [mem_ball, Complex.dist_eq, hR]
    linarith
  have hne := one_add_a_ne_zero hz
  have h := logDeriv_tprod_eq_tsum (f := fun i w => 1 + a i w) isOpen_ball hzR hne
    (fun i => ((differentiable_const (1 : ℂ)).add (differentiable_a i)).differentiableOn)
    (by
      refine (summable_tank z).congr ?_
      intro i
      exact (logDeriv_factor i (hne i)).symm)
    (multipliableLocallyUniformlyOn R) (P_ne_zero hz)
  beta_reduce at h
  unfold P
  rw [h]
  apply tsum_congr
  intro i
  exact logDeriv_factor i (hne i)

/-- The Foster series collapses to the sum over the zeros with multiplicity. -/
theorem tsum_tank_eq (z : ℂ) :
    ∑' i : Idx, tank i z =
      ∑' u : Zero, ((mult (u : ℂ)).toNat : ℂ) *
        (2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2)) := by
  rw [(summable_tank z).tsum_sigma]
  apply tsum_congr
  intro u
  rw [tsum_fintype]
  have hconst : ∀ j : Fin (mult (u : ℂ)).toNat, tank ⟨u, j⟩ z =
      2 * (z - 1 / 2) / ((z - 1 / 2) ^ 2 - ((u : ℂ) - 1 / 2) ^ 2) := fun j => rfl
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Soma.Holonics.RH.FosterProduct

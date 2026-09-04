import Mathlib
import ElementaryHolonics.RH.FosterTanks
import ElementaryHolonics.RH.FosterCount
import ElementaryHolonics.RH.FosterProduct

/-!
# FT3 (i): the product splits on a disc, and the log-derivative defect is analytic and bounded

On the disc of radius `R` about `½` the symmetric factorization of FT0 writes `ξ = Q · g` with `Q`
the polynomial of the zeros in the closed half disc and `g` analytic, nonvanishing on the open half
disc.  The paired product of FT2 splits over the same population: `P = c · Q² · tail`, with `tail`
the product over the indices outside the half disc, analytic and nonvanishing on the open half
disc, and `c` a nonzero constant.  Hence off the zeros

```text
2 ξ′/ξ − P′/P = 2 g′/g − tail′/tail,
```

and the right side, `F_R`, is analytic on the open half disc.  Landau's remainder (FT0) and the
tail of the Foster series (FT1, FT2) bound it on the disc of radius `R/8` by
`2 · landau R + (R/2) · tailInvSq R`, where `tailInvSq R → 0`.  FT3 (ii) lets `R → ∞`.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterSplit

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.LandauXi
open Soma.Holonics.RH.JensenCountsTheComb
open Soma.Holonics.RH.FosterTanks
open Soma.Holonics.RH.FosterCount
open Soma.Holonics.RH.FosterProduct
open scoped Classical

/-! ## Landau's remainder as one function of the radius -/

/-- Landau's remainder bound at radius `R`, at the fixed envelope constant. -/
def landau (R : ℝ) : ℝ :=
  16 * (xiBudget pointC (1 / 2) R +
    Real.log (jensenCeiling pointC (1 / 2) R / ‖riemannXi (1 / 2)‖) / Real.log (3 / 2) *
      Real.log 2) / R

/-- The symmetric factorization at radius `R`, chosen once. -/
def Zfac {R : ℝ} (hR : 0 < R) : SymmetricZeroFactorization R :=
  Classical.choose (exists_paired_foster_form_fixed hR)

theorem Zfac_landau {R : ℝ} (hR : 0 < R) :
    ∀ z ∈ closedBall (1 / 2 : ℂ) (R / 8), riemannXi z ≠ 0 →
      ‖logDeriv riemannXi z -
          ∑ ρ ∈ (Zfac hR).zeros, ((Zfac hR).mult ρ : ℂ) *
            ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))‖ ≤ landau R :=
  (Classical.choose_spec (exists_paired_foster_form_fixed hR)).2

/-! ## The population of the factorization is the population of the product -/

theorem mult_eq_divisor_ball {c u : ℂ} {R : ℝ} (hu : u ∈ ball c R) :
    MeromorphicOn.divisor riemannXi (ball c R) u = mult u :=
  MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu

theorem mem_zeros_iff {R : ℝ} (hR : 0 < R) (ρ : ℂ) :
    ρ ∈ (Zfac hR).zeros ↔ (mult ρ ≠ 0 ∧ ρ ∈ closedBall (1 / 2 : ℂ) (R / 2)) := by
  rw [(Zfac hR).mem_zeros_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hb : ρ ∈ ball (1 / 2 : ℂ) R := closedBall_subset_ball (by linarith) h2
    rwa [mult_eq_divisor_ball hb] at h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hb : ρ ∈ ball (1 / 2 : ℂ) R := closedBall_subset_ball (by linarith) h2
    rwa [mult_eq_divisor_ball hb]

theorem Zfac_mult_eq {R : ℝ} (hR : 0 < R) {ρ : ℂ} (hρ : ρ ∈ (Zfac hR).zeros) :
    (Zfac hR).mult ρ = (mult ρ).toNat := by
  have h := (Zfac hR).mult_eq_div ρ
  have hb : ρ ∈ ball (1 / 2 : ℂ) R :=
    closedBall_subset_ball (by linarith) ((mem_zeros_iff hR ρ).mp hρ).2
  rw [mult_eq_divisor_ball hb] at h
  have := mult_nonneg ρ
  omega

theorem Zfac_ne_half {R : ℝ} (hR : 0 < R) {ρ : ℂ} (hρ : ρ ∈ (Zfac hR).zeros) : ρ - 1 / 2 ≠ 0 := by
  intro h
  have h1 := ((mem_zeros_iff hR ρ).mp hρ).1
  apply h1
  rw [sub_eq_zero.mp h]
  exact mult_half

/-- The finite index population of the half disc, as a finset of the repeated index. -/
def T {R : ℝ} (hR : 0 < R) : Finset Idx :=
  ((Zfac hR).zeros.subtype (fun u : ℂ => mult u ≠ 0)).sigma (fun u => Finset.univ)

theorem mem_T {R : ℝ} (hR : 0 < R) (i : Idx) : i ∈ T hR ↔ ((i.1 : Zero) : ℂ) ∈ (Zfac hR).zeros := by
  unfold T
  obtain ⟨u, j⟩ := i
  rw [Finset.mem_sigma, Finset.mem_subtype]
  simp

theorem mem_T_iff_norm {R : ℝ} (hR : 0 < R) (i : Idx) : i ∈ T hR ↔ ‖ctr i‖ ≤ R / 2 := by
  rw [mem_T, mem_zeros_iff hR]
  constructor
  · rintro ⟨_, h⟩
    rw [mem_closedBall, Complex.dist_eq] at h
    exact h
  · intro h
    refine ⟨(i.1).2, ?_⟩
    rw [mem_closedBall, Complex.dist_eq]
    exact h

/-- A product over the finite population is the multiplicity-weighted product over the comb. -/
theorem prod_T {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) :
    ∏ i ∈ T hR, f ((i.1 : Zero) : ℂ) = ∏ ρ ∈ (Zfac hR).zeros, f ρ ^ (Zfac hR).mult ρ := by
  unfold T
  rw [Finset.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ∏ u ∈ (Zfac hR).zeros.subtype (fun u : ℂ => mult u ≠ 0), f (u : ℂ) ^ (mult (u : ℂ)).toNat =
      ∏ u ∈ ((Zfac hR).zeros.subtype (fun u : ℂ => mult u ≠ 0)).map
        (Function.Embedding.subtype _), f u ^ (mult u).toNat := by
    rw [Finset.prod_map]
    rfl
  rw [h1, Finset.subtype_map, Finset.filter_true_of_mem (fun ρ hρ => ((mem_zeros_iff hR ρ).mp hρ).1)]
  apply Finset.prod_congr rfl
  intro ρ hρ
  rw [Zfac_mult_eq hR hρ]

/-- A sum over the finite population is the multiplicity-weighted sum over the comb. -/
theorem sum_T {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ) :
    ∑ i ∈ T hR, f ((i.1 : Zero) : ℂ) = ∑ ρ ∈ (Zfac hR).zeros, ((Zfac hR).mult ρ : ℂ) * f ρ := by
  unfold T
  rw [Finset.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ u ∈ (Zfac hR).zeros.subtype (fun u : ℂ => mult u ≠ 0),
      ((mult (u : ℂ)).toNat : ℂ) * f (u : ℂ) =
      ∑ u ∈ ((Zfac hR).zeros.subtype (fun u : ℂ => mult u ≠ 0)).map
        (Function.Embedding.subtype _), ((mult u).toNat : ℂ) * f u := by
    rw [Finset.sum_map]
    rfl
  rw [h1, Finset.subtype_map, Finset.filter_true_of_mem (fun ρ hρ => ((mem_zeros_iff hR ρ).mp hρ).1)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [Zfac_mult_eq hR hρ]

/-! ## The split of the product -/

/-- The tail of the product: the indices outside the half disc. -/
def tail {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  ∏' i : ↥((↑(T hR) : Set Idx)ᶜ), (1 + a (i : Idx) z)

theorem P_split {R : ℝ} (hR : 0 < R) (z : ℂ) :
    P z = (∏ i ∈ T hR, (1 + a i z)) * tail hR z := by
  have h1 : HasProd ((fun i : Idx => 1 + a i z) ∘ (Subtype.val : ↥(↑(T hR) : Set Idx) → Idx))
      (∏ i ∈ T hR, (1 + a i z)) := by
    have := hasProd_fintype ((fun i : Idx => 1 + a i z) ∘ (Subtype.val : ↥(↑(T hR) : Set Idx) → Idx))
    rwa [show (∏ b : ↥(↑(T hR) : Set Idx), ((fun i : Idx => 1 + a i z) ∘ Subtype.val) b) =
      ∏ i ∈ T hR, (1 + a i z) from Finset.prod_coe_sort (T hR) (fun i => 1 + a i z)] at this
  have h2 : HasProd ((fun i : Idx => 1 + a i z) ∘ (Subtype.val : ↥(↑(T hR) : Set Idx)ᶜ → Idx))
      (tail hR z) :=
    (multipliable_one_add_of_summable (f := fun i : ↥(↑(T hR) : Set Idx)ᶜ => a (i : Idx) z)
      ((summable_norm_a z).subtype _)).hasProd
  unfold P
  exact (h1.mul_compl h2).tprod_eq

theorem one_add_a_ne_zero_of_far {z : ℂ} {i : Idx} (h : ‖z - 1 / 2‖ < ‖ctr i‖) : 1 + a i z ≠ 0 := by
  intro h0
  rcases (one_add_a_eq_zero_iff i z).mp h0 with h1 | h1
  · apply lt_irrefl ‖ctr i‖
    calc ‖ctr i‖ = ‖z - 1 / 2‖ := by rw [h1]; rfl
      _ < ‖ctr i‖ := h
  · apply lt_irrefl ‖ctr i‖
    calc ‖ctr i‖ = ‖z - 1 / 2‖ := by
          rw [h1]
          unfold ctr
          rw [show (1 : ℂ) - ((i.1 : Zero) : ℂ) - 1 / 2 = -(((i.1 : Zero) : ℂ) - 1 / 2) by ring,
            norm_neg]
      _ < ‖ctr i‖ := h

theorem norm_ctr_of_notMem {R : ℝ} (hR : 0 < R) {i : Idx} (hi : i ∉ T hR) : R / 2 < ‖ctr i‖ := by
  rw [mem_T_iff_norm] at hi
  exact lt_of_not_ge hi

theorem tail_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    tail hR z ≠ 0 := by
  unfold tail
  apply tprod_one_add_ne_zero_of_summable
  · intro i
    apply one_add_a_ne_zero_of_far
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_ctr_of_notMem hR (i.2)
    linarith
  · exact (summable_norm_a z).subtype _

theorem tail_hasProdLocallyUniformlyOn {R : ℝ} (hR : 0 < R) :
    HasProdLocallyUniformlyOn (fun (i : ↥(↑(T hR) : Set Idx)ᶜ) x => 1 + a (i : Idx) x)
      (tail hR) (ball (1 / 2 : ℂ) (R / 2)) :=
  Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball
    (u := fun i : ↥(↑(T hR) : Set Idx)ᶜ => (R / 2) ^ 2 * invSq (((i : Idx).1 : Zero) : ℂ))
    ((summable_majorant_disc (R / 2)).subtype _)
    (Eventually.of_forall fun i x hx => norm_a_le_of_mem_ball hx (i : Idx))
    (fun i => (continuous_a (i : Idx)).continuousOn)

theorem tail_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (tail hR) (ball (1 / 2 : ℂ) (R / 2)) := by
  have hloc := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn).mp
    (tail_hasProdLocallyUniformlyOn hR)
  refine hloc.differentiableOn ?_ isOpen_ball
  refine Eventually.of_forall fun t => ?_
  apply Differentiable.differentiableOn
  have hfun : (fun x : ℂ => ∏ i ∈ t, (1 + a (i : Idx) x)) =
      ∏ i ∈ t, (fun x : ℂ => 1 + a (i : Idx) x) := by
    funext x
    rw [Finset.prod_apply]
  rw [hfun]
  apply Differentiable.finset_prod
  intro i _
  exact (differentiable_const _).add (differentiable_a (i : Idx))

/-- The tail of the inverse squares outside the half disc. -/
def tailInvSq (R : ℝ) : ℝ := ∑' i : ↥{i : Idx | R / 2 < ‖ctr i‖}, invSq (((i : Idx).1 : Zero) : ℂ)

theorem compl_T_eq {R : ℝ} (hR : 0 < R) : ((↑(T hR) : Set Idx)ᶜ) = {i : Idx | R / 2 < ‖ctr i‖} := by
  ext i
  simp only [mem_compl_iff, Finset.mem_coe, mem_setOf_eq, mem_T_iff_norm]
  exact not_le

theorem tailInvSq_nonneg (R : ℝ) : 0 ≤ tailInvSq R :=
  tsum_nonneg fun _ => invSq_nonneg _

theorem logDeriv_tail {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv (tail hR) z = ∑' i : ↥(↑(T hR) : Set Idx)ᶜ, tank (i : Idx) z := by
  have hne : ∀ i : ↥(↑(T hR) : Set Idx)ᶜ, 1 + a (i : Idx) z ≠ 0 := by
    intro i
    apply one_add_a_ne_zero_of_far
    rw [mem_ball, Complex.dist_eq] at hz
    have := norm_ctr_of_notMem hR (i.2)
    linarith
  have h := logDeriv_tprod_eq_tsum (f := fun (i : ↥(↑(T hR) : Set Idx)ᶜ) w => 1 + a (i : Idx) w)
    isOpen_ball hz hne
    (fun i => ((differentiable_const (1 : ℂ)).add (differentiable_a (i : Idx))).differentiableOn)
    (by
      refine ((summable_tank z).subtype _).congr ?_
      intro i
      exact (logDeriv_factor (i : Idx) (hne i)).symm)
    ⟨_, tail_hasProdLocallyUniformlyOn hR⟩ (tail_ne_zero hR hz)
  beta_reduce at h
  unfold tail
  rw [h]
  apply tsum_congr
  intro i
  exact logDeriv_factor (i : Idx) (hne i)

theorem norm_logDeriv_tail_le {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv (tail hR) z‖ ≤ 4 * ‖z - 1 / 2‖ * tailInvSq R := by
  have hz' : z ∈ ball (1 / 2 : ℂ) (R / 2) := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  rw [logDeriv_tail hR hz']
  have hzd : ‖z - 1 / 2‖ ≤ R / 8 := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hbound : ∀ i : ↥(↑(T hR) : Set Idx)ᶜ,
      ‖tank (i : Idx) z‖ ≤ 4 * ‖z - 1 / 2‖ * invSq (((i : Idx).1 : Zero) : ℂ) := by
    intro i
    apply norm_tank_le
    have h1 := norm_ctr_of_notMem hR (i.2)
    have h0 : 0 ≤ ‖z - 1 / 2‖ := norm_nonneg _
    nlinarith
  calc ‖∑' i : ↥(↑(T hR) : Set Idx)ᶜ, tank (i : Idx) z‖
      ≤ ∑' i : ↥(↑(T hR) : Set Idx)ᶜ, ‖tank (i : Idx) z‖ :=
        norm_tsum_le_tsum_norm ((summable_tank z).subtype _).norm
    _ ≤ ∑' i : ↥(↑(T hR) : Set Idx)ᶜ, 4 * ‖z - 1 / 2‖ * invSq (((i : Idx).1 : Zero) : ℂ) :=
        Summable.tsum_le_tsum hbound ((summable_tank z).subtype _).norm
          (((summable_majorant_disc 1).subtype _).mul_left (4 * ‖z - 1 / 2‖) |>.congr
            (fun i => by simp only [Function.comp]; ring))
    _ = 4 * ‖z - 1 / 2‖ * tailInvSq R := by
        rw [tsum_mul_left]
        unfold tailInvSq
        congr 1
        exact tsum_congr_set_coe (fun i : Idx => invSq ((i.1 : Zero) : ℂ)) (compl_T_eq hR)

/-- **The tail of the inverse squares vanishes at infinity.** -/
theorem tailInvSq_tendsto : Tendsto tailInvSq atTop (𝓝 0) := by
  have hsum : Summable (fun i : Idx => invSq ((i.1 : Zero) : ℂ)) := by
    have := summable_majorant_disc 1
    refine this.congr ?_
    intro i
    ring
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun R => lt_of_lt_of_le ha (tailInvSq_nonneg R), ?_⟩
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i ∈ s, ‖ctr i‖ ≤ M :=
    ⟨∑ i ∈ s, ‖ctr i‖, fun i hi => Finset.single_le_sum (fun j _ => norm_nonneg (ctr j)) hi⟩
  rw [Filter.eventually_atTop]
  refine ⟨2 * M + 2, fun R hR => ?_⟩
  have hle : tailInvSq R ≤ ε / 2 := by
    unfold tailInvSq
    apply Real.tsum_le_of_sum_le (fun _ => invSq_nonneg _)
    intro t
    have hdisj : Disjoint (t.map (Function.Embedding.subtype _)) s := by
      rw [Finset.disjoint_left]
      intro i hi his
      rw [Finset.mem_map] at hi
      obtain ⟨j, _, rfl⟩ := hi
      have h1 : R / 2 < ‖ctr ((Function.Embedding.subtype _) j)‖ := j.2
      have h2 := hM _ his
      linarith
    have := hs _ hdisj
    simp only [Finset.sum_map, Function.Embedding.coe_subtype] at this
    have hnn : 0 ≤ ∑ j ∈ t, invSq ((((j : Idx).1 : Zero) : ℂ)) :=
      Finset.sum_nonneg (fun _ _ => invSq_nonneg _)
    rw [Real.norm_of_nonneg hnn] at this
    exact this.le
  linarith

/-! ## The finite part is the square of the factorization's polynomial -/

/-- The constant of the finite part. -/
def cst {R : ℝ} (hR : 0 < R) : ℂ :=
  ∏ ρ ∈ (Zfac hR).zeros, (-1 / (ρ - 1 / 2) ^ 2) ^ (Zfac hR).mult ρ

theorem cst_ne_zero {R : ℝ} (hR : 0 < R) : cst hR ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
    pow_ne_zero _ (div_ne_zero (by norm_num) (pow_ne_zero _ (Zfac_ne_half hR hρ)))

theorem finitePart_eq {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∏ i ∈ T hR, (1 + a i z) = cst hR * (Zfac hR).poly z ^ 2 := by
  have h1 : ∏ i ∈ T hR, (1 + a i z) =
      ∏ i ∈ T hR, (fun ρ : ℂ => 1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2) ((i.1 : Zero) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [a, ctr]
    ring
  rw [h1, prod_T hR (fun ρ : ℂ => 1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2), pow_two ((Zfac hR).poly z)]
  have h2 : ∀ ρ ∈ (Zfac hR).zeros, (1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2) ^ (Zfac hR).mult ρ =
      (-1 / (ρ - 1 / 2) ^ 2) ^ (Zfac hR).mult ρ *
        ((z - ρ) ^ (Zfac hR).mult ρ * (z - (1 - ρ)) ^ (Zfac hR).mult ρ) := by
    intro ρ hρ
    rw [← mul_pow, ← mul_pow]
    congr 1
    have hne := Zfac_ne_half hR hρ
    obtain ⟨w, rfl⟩ : ∃ w, ρ = w + 1 / 2 := ⟨ρ - 1 / 2, by ring⟩
    have hw : w ≠ 0 := by
      intro h
      apply hne
      rw [h]
      ring
    have hinv : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
    linear_combination (-(1 + w * w⁻¹)) * hinv
  rw [Finset.prod_congr rfl h2, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  unfold cst ZeroFactorization.poly
  congr 2
  refine Finset.prod_nbij' (fun ρ => 1 - ρ) (fun ρ => 1 - ρ) ?_ ?_ ?_ ?_ ?_
  · intro ρ hρ
    exact (Zfac hR).refl_mem ρ hρ
  · intro ρ hρ
    exact (Zfac hR).refl_mem ρ hρ
  · intro ρ _
    ring
  · intro ρ _
    ring
  · intro ρ hρ
    rw [(Zfac hR).refl_mult ρ hρ]

theorem mult_eq_zero_of_ne_zero {z : ℂ} (hz : riemannXi z ≠ 0) : mult z = 0 := by
  unfold mult
  have ha := differentiable_riemannXi.analyticAt z
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hz]
  simp

theorem poly_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hξ : riemannXi z ≠ 0) :
    (Zfac hR).poly z ≠ 0 := by
  unfold ZeroFactorization.poly
  rw [Finset.prod_ne_zero_iff]
  intro ρ hρ
  apply pow_ne_zero
  intro h
  rw [sub_eq_zero] at h
  subst h
  exact ((mem_zeros_iff hR z).mp hρ).1 (mult_eq_zero_of_ne_zero hξ)

theorem poly_differentiable {R : ℝ} (hR : 0 < R) : Differentiable ℂ (Zfac hR).poly := by
  unfold ZeroFactorization.poly
  have hfun : (fun z : ℂ => ∏ ρ ∈ (Zfac hR).zeros, (z - ρ) ^ (Zfac hR).mult ρ) =
      ∏ ρ ∈ (Zfac hR).zeros, (fun z : ℂ => (z - ρ) ^ (Zfac hR).mult ρ) := by
    funext z
    rw [Finset.prod_apply]
  rw [hfun]
  apply Differentiable.finset_prod
  intro ρ _
  exact (differentiable_id.sub_const ρ).pow _

/-! ## The defect `F_R = 2 g′/g − tail′/tail` -/

/-- The defect: analytic on the open half disc, equal to `2 ξ′/ξ − P′/P` off the zeros. -/
def F {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  2 * logDeriv (Zfac hR).unit z - logDeriv (tail hR) z

theorem logDeriv_differentiableOn {f : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hf : DifferentiableOn ℂ f s) (hne : ∀ z ∈ s, f z ≠ 0) :
    DifferentiableOn ℂ (logDeriv f) s := by
  have hd : DifferentiableOn ℂ (deriv f) s := (hf.analyticOnNhd hs).deriv.differentiableOn
  show DifferentiableOn ℂ (fun z => deriv f z / f z) s
  exact hd.div hf hne

theorem logDeriv_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : logDeriv f z = logDeriv g z := by
  simp only [logDeriv_apply]
  rw [h.deriv_eq, h.eq_of_nhds]

theorem unit_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (Zfac hR).unit (ball (1 / 2 : ℂ) (R / 2)) :=
  (Zfac hR).unit_diff.mono (ball_subset_ball (by linarith))

theorem F_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (F hR) (ball (1 / 2 : ℂ) (R / 2)) := by
  unfold F
  exact ((logDeriv_differentiableOn isOpen_ball (unit_differentiableOn hR)
    (fun z hz => (Zfac hR).unit_ne z hz)).const_mul 2).sub
    (logDeriv_differentiableOn isOpen_ball (tail_differentiableOn hR)
      (fun z hz => tail_ne_zero hR hz))

theorem F_eq {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2))
    (hξ : riemannXi z ≠ 0) :
    F hR z = 2 * logDeriv riemannXi z - logDeriv P z := by
  have hzR : z ∈ ball (1 / 2 : ℂ) R := ball_subset_ball (by linarith) hz
  have hpd := poly_differentiable hR
  have hpoly_ne : (Zfac hR).poly z ≠ 0 := poly_ne_zero hR hξ
  have hunit_ne : (Zfac hR).unit z ≠ 0 := (Zfac hR).unit_ne z hz
  have hunit_diff : DifferentiableAt ℂ (Zfac hR).unit z :=
    (Zfac hR).unit_diff.differentiableAt (isOpen_ball.mem_nhds hzR)
  have htail_ne : tail hR z ≠ 0 := tail_ne_zero hR hz
  have htail_diff : DifferentiableAt ℂ (tail hR) z :=
    (tail_differentiableOn hR).differentiableAt (isOpen_ball.mem_nhds hz)
  have h1 : logDeriv riemannXi z = logDeriv (Zfac hR).poly z + logDeriv (Zfac hR).unit z := by
    have hev : riemannXi =ᶠ[𝓝 z] (fun w => (Zfac hR).poly w * (Zfac hR).unit w) := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw
      exact (Zfac hR).factor w hw
    rw [logDeriv_congr hev]
    exact logDeriv_mul z hpoly_ne hunit_ne (hpd z) hunit_diff
  have h2 : logDeriv P z = 2 * logDeriv (Zfac hR).poly z + logDeriv (tail hR) z := by
    have hP : P = fun w => (cst hR * ((Zfac hR).poly w * (Zfac hR).poly w)) * tail hR w := by
      funext w
      rw [P_split hR w, finitePart_eq hR w, sq]
    have hpp : DifferentiableAt ℂ (fun w => (Zfac hR).poly w * (Zfac hR).poly w) z :=
      (hpd z).mul (hpd z)
    have hcpp : DifferentiableAt ℂ (fun w => cst hR * ((Zfac hR).poly w * (Zfac hR).poly w)) z :=
      (differentiableAt_const _).mul hpp
    have hcpp_ne : cst hR * ((Zfac hR).poly z * (Zfac hR).poly z) ≠ 0 :=
      mul_ne_zero (cst_ne_zero hR) (mul_ne_zero hpoly_ne hpoly_ne)
    rw [hP, logDeriv_mul (f := fun w => cst hR * ((Zfac hR).poly w * (Zfac hR).poly w))
        (g := tail hR) z hcpp_ne htail_ne hcpp htail_diff,
      logDeriv_mul (f := fun _ => cst hR) (g := fun w => (Zfac hR).poly w * (Zfac hR).poly w) z
        (cst_ne_zero hR) (mul_ne_zero hpoly_ne hpoly_ne) (differentiableAt_const _) hpp,
      logDeriv_mul (f := (Zfac hR).poly) (g := (Zfac hR).poly) z hpoly_ne hpoly_ne (hpd z) (hpd z),
      logDeriv_const, Pi.zero_apply]
    ring
  unfold F
  rw [h1, h2]
  ring

/-! ## The uniform bound on the disc of radius `R/8` -/

/-- The bound of `F_R` on the open disc of radius `R/8`. -/
def bound (R : ℝ) : ℝ := 2 * landau R + (R / 2) * tailInvSq R

/-- The tank series splits into the finite population of the half disc and the tail's
log-derivative. -/
theorem tsum_tank_split {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ∑' i : Idx, FosterProduct.tank i z =
      (∑ i ∈ T hR, FosterProduct.tank i z) + logDeriv (tail hR) z := by
  rw [logDeriv_tail hR hz]
  have h1 : HasSum ((fun i : Idx => FosterProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T hR) : Set Idx) → Idx)) (∑ i ∈ T hR, FosterProduct.tank i z) := by
    have := hasSum_fintype ((fun i : Idx => FosterProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T hR) : Set Idx) → Idx))
    rwa [show (∑ b : ↥(↑(T hR) : Set Idx), ((fun i : Idx => FosterProduct.tank i z) ∘ Subtype.val) b) =
      ∑ i ∈ T hR, FosterProduct.tank i z from
        Finset.sum_coe_sort (T hR) (fun i => FosterProduct.tank i z)] at this
  have h2 : HasSum ((fun i : Idx => FosterProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T hR) : Set Idx)ᶜ → Idx))
      (∑' i : ↥(↑(T hR) : Set Idx)ᶜ, FosterProduct.tank (i : Idx) z) :=
    ((summable_tank z).subtype _).hasSum
  exact (h1.add_compl h2).tsum_eq

/-- The finite tank sum of the half disc is twice the paired Landau sum. -/
theorem sum_tank_T {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∑ i ∈ T hR, FosterProduct.tank i z = 2 * ∑ ρ ∈ (Zfac hR).zeros, ((Zfac hR).mult ρ : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) := by
  have h1 : ∑ i ∈ T hR, FosterProduct.tank i z = ∑ i ∈ T hR,
      (fun ρ : ℂ => 2 * ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))) ((i.1 : Zero) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [FosterProduct.tank, ctr]
    ring
  rw [h1, sum_T hR (fun ρ : ℂ => 2 * ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem norm_F_le_of_ne {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hξ : riemannXi z ≠ 0) : ‖F hR z‖ ≤ bound R := by
  have hz' : z ∈ ball (1 / 2 : ℂ) (R / 2) := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hzd : ‖z - 1 / 2‖ ≤ R / 8 := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hm : mult z = 0 := mult_eq_zero_of_ne_zero hξ
  set S : ℂ := ∑ ρ ∈ (Zfac hR).zeros, ((Zfac hR).mult ρ : ℂ) *
    ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) with hS
  have hsplit : logDeriv P z = (∑ i ∈ T hR, FosterProduct.tank i z) + logDeriv (tail hR) z := by
    rw [logDeriv_P hm, tsum_tank_split hR hz']
  have hfin : ∑ i ∈ T hR, FosterProduct.tank i z = 2 * S := sum_tank_T hR z
  have hL : ‖logDeriv riemannXi z - S‖ ≤ landau R := Zfac_landau hR z hz hξ
  have hT := norm_logDeriv_tail_le hR hz
  rw [F_eq hR hz' hξ, hsplit, hfin]
  calc ‖2 * logDeriv riemannXi z - (2 * S + logDeriv (tail hR) z)‖
      = ‖2 * (logDeriv riemannXi z - S) - logDeriv (tail hR) z‖ := by
        congr 1
        ring
    _ ≤ ‖2 * (logDeriv riemannXi z - S)‖ + ‖logDeriv (tail hR) z‖ := norm_sub_le _ _
    _ = 2 * ‖logDeriv riemannXi z - S‖ + ‖logDeriv (tail hR) z‖ := by
        rw [norm_mul]
        norm_num
    _ ≤ 2 * landau R + 4 * ‖z - 1 / 2‖ * tailInvSq R := by gcongr
    _ ≤ bound R := by
        unfold bound
        have := tailInvSq_nonneg R
        nlinarith

theorem eventually_ne_zero (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, riemannXi w ≠ 0 := by
  have ha := differentiable_riemannXi.analyticAt z
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall : EqOn riemannXi 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun x _ => differentiable_riemannXi.analyticAt x) isPreconnected_univ (mem_univ z) h
    exact XiCentre.riemannXi_one_half_ne_zero (hall (mem_univ _))
  · exact h

/-- **The defect is bounded on the open disc of radius `R/8`**, at the zeros by continuity. -/
theorem norm_F_le {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 8)) :
    ‖F hR z‖ ≤ bound R := by
  by_cases hξ : riemannXi z ≠ 0
  · exact norm_F_le_of_ne hR (ball_subset_closedBall hz) hξ
  · push_neg at hξ
    have hcont : ContinuousAt (F hR) z :=
      ((F_differentiableOn hR).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hz))).continuousAt
    have hlim : Tendsto (fun w => ‖F hR w‖) (𝓝[≠] z) (𝓝 ‖F hR z‖) :=
      hcont.norm.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ ball (1 / 2 : ℂ) (R / 8) :=
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)
    filter_upwards [h1, eventually_ne_zero z] with w hw hw'
    exact norm_F_le_of_ne hR (ball_subset_closedBall hw) hw'

end Soma.Holonics.RH.FosterSplit

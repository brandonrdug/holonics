import Mathlib
import ElementaryHolonics.RH.FosterClassProduct

/-!
# FT3 (i): the product splits on a disc, and the log-derivative defect is analytic and bounded

On the disc of radius `R` about `½` the symmetric factorization of FT0 writes `ξ = Q · g` with `Q`
the polynomial of the zeros in the closed half disc and `g` analytic, nonvanishing on the open half
disc.  The paired product of FT2 splits over the same population: `P f = c · Q² · tail`, with `tail`
the product over the indices outside the half disc, analytic and nonvanishing on the open half
disc, and `c` a nonzero constant.  Hence off the zeros

```text
2 ξ′/ξ − P′/P f = 2 g′/g − tail′/tail,
```

and the right side, `F_R`, is analytic on the open half disc.  Landau's remainder (FT0) and the
(tail (f := f)) of the Foster series (FT1, FT2) bound it on the disc of radius `R/8` by
`2 · landau f A B σ R + (R/2) · tailInvSq f R`, where `tailInvSq f R → 0`.  FT3 (ii) lets `R → ∞`.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassSplit

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.FosterTanks
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassCount
open Soma.Holonics.RH.FosterClassProduct
open scoped Classical

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-! ## Landau's remainder as one function of the radius -/

/-- The symmetric factorization at radius `R`, chosen once. -/
def Zfac {R : ℝ} (hR : 0 < R) : SymmetricZeroFactorizationOf f R :=
  Classical.choose (exists_paired_foster_form (f := f) hR)

theorem Zfac_landau {R : ℝ} (hR : 0 < R) :
    ∀ z ∈ closedBall (1 / 2 : ℂ) (R / 8), f z ≠ 0 →
      ‖logDeriv f z -
          ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) *
            ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))‖ ≤ landau f A B σ R :=
  (Classical.choose_spec (exists_paired_foster_form (f := f) hR)).2

/-! ## The population of the factorization is the population of the product -/

theorem mult_eq_divisor_ball {c u : ℂ} {R : ℝ} (hu : u ∈ ball c R) :
    MeromorphicOn.divisor f (ball c R) u = mult f u :=
  MeromorphicOn.divisor_apply (hf.meromorphicOn _) hu

theorem mem_zeros_iff {R : ℝ} (hR : 0 < R) (ρ : ℂ) :
    ρ ∈ (Zfac (f := f) hR).zeros ↔ (mult f ρ ≠ 0 ∧ ρ ∈ closedBall (1 / 2 : ℂ) (R / 2)) := by
  rw [(Zfac (f := f) hR).mem_zeros_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hb : ρ ∈ ball (1 / 2 : ℂ) R := closedBall_subset_ball (by linarith) h2
    rwa [(mult_eq_divisor_ball (f := f)) hb] at h1
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have hb : ρ ∈ ball (1 / 2 : ℂ) R := closedBall_subset_ball (by linarith) h2
    rwa [(mult_eq_divisor_ball (f := f)) hb]

theorem Zfac_mult_eq {R : ℝ} (hR : 0 < R) {ρ : ℂ} (hρ : ρ ∈ (Zfac (f := f) hR).zeros) :
    (Zfac (f := f) hR).mult ρ = (mult f ρ).toNat := by
  have h := (Zfac (f := f) hR).mult_eq_div ρ
  have hb : ρ ∈ ball (1 / 2 : ℂ) R :=
    closedBall_subset_ball (by linarith) ((mem_zeros_iff (f := f) hR ρ).mp hρ).2
  rw [(mult_eq_divisor_ball (f := f)) hb] at h
  have := (mult_nonneg (f := f)) ρ
  omega

theorem Zfac_ne_half {R : ℝ} (hR : 0 < R) {ρ : ℂ} (hρ : ρ ∈ (Zfac (f := f) hR).zeros) : ρ - 1 / 2 ≠ 0 := by
  intro h
  have h1 := ((mem_zeros_iff (f := f) hR ρ).mp hρ).1
  apply h1
  rw [sub_eq_zero.mp h]
  exact (mult_half (f := f))

/-- The finite index population of the half disc, as a finset of the repeated index. -/
def T {R : ℝ} (hR : 0 < R) : Finset (Idx f) :=
  ((Zfac (f := f) hR).zeros.subtype (fun u : ℂ => mult f u ≠ 0)).sigma (fun u => Finset.univ)

theorem mem_T {R : ℝ} (hR : 0 < R) (i : Idx f) : i ∈ (T (f := f)) hR ↔ ((i.1 : Zero f) : ℂ) ∈ (Zfac (f := f) hR).zeros := by
  unfold T
  obtain ⟨u, j⟩ := i
  rw [Finset.mem_sigma, Finset.mem_subtype]
  simp

theorem mem_T_iff_norm {R : ℝ} (hR : 0 < R) (i : Idx f) : i ∈ (T (f := f)) hR ↔ ‖ctr i‖ ≤ R / 2 := by
  rw [mem_T, (mem_zeros_iff (f := f)) hR]
  constructor
  · rintro ⟨_, h⟩
    rw [mem_closedBall, Complex.dist_eq] at h
    exact h
  · intro h
    refine ⟨(i.1).2, ?_⟩
    rw [mem_closedBall, Complex.dist_eq]
    exact h

/-- A product over the finite population is the multiplicity-weighted product over the comb. -/
theorem prod_T {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) :
    ∏ i ∈ (T (f := f)) hR, g ((i.1 : Zero f) : ℂ) = ∏ ρ ∈ (Zfac (f := f) hR).zeros, g ρ ^ (Zfac (f := f) hR).mult ρ := by
  unfold T
  rw [Finset.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ∏ u ∈ (Zfac (f := f) hR).zeros.subtype (fun u : ℂ => mult f u ≠ 0), g (u : ℂ) ^ (mult f (u : ℂ)).toNat =
      ∏ u ∈ ((Zfac (f := f) hR).zeros.subtype (fun u : ℂ => mult f u ≠ 0)).map
        (Function.Embedding.subtype _), g u ^ (mult f u).toNat := by
    rw [Finset.prod_map]
    rfl
  rw [h1, Finset.subtype_map, Finset.filter_true_of_mem (fun ρ hρ => ((mem_zeros_iff (f := f) hR ρ).mp hρ).1)]
  apply Finset.prod_congr rfl
  intro ρ hρ
  rw [(Zfac_mult_eq (f := f)) hR hρ]

/-- A sum over the finite population is the multiplicity-weighted sum over the comb. -/
theorem sum_T {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) :
    ∑ i ∈ (T (f := f)) hR, g ((i.1 : Zero f) : ℂ) = ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) * g ρ := by
  unfold T
  rw [Finset.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h1 : ∑ u ∈ (Zfac (f := f) hR).zeros.subtype (fun u : ℂ => mult f u ≠ 0),
      ((mult f (u : ℂ)).toNat : ℂ) * g (u : ℂ) =
      ∑ u ∈ ((Zfac (f := f) hR).zeros.subtype (fun u : ℂ => mult f u ≠ 0)).map
        (Function.Embedding.subtype _), ((mult f u).toNat : ℂ) * g u := by
    rw [Finset.sum_map]
    rfl
  rw [h1, Finset.subtype_map, Finset.filter_true_of_mem (fun ρ hρ => ((mem_zeros_iff (f := f) hR ρ).mp hρ).1)]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [(Zfac_mult_eq (f := f)) hR hρ]

/-! ## The split of the product -/

/-- The (tail (f := f)) of the product: the indices outside the half disc. -/
def tail {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  ∏' i : ↥((↑(T (f := f) hR) : Set (Idx f))ᶜ), (1 + a (i : Idx f) z)

theorem P_split {R : ℝ} (hR : 0 < R) (z : ℂ) :
    P f z = (∏ i ∈ (T (f := f)) hR, (1 + a i z)) * (tail (f := f)) hR z := by
  have h1 : HasProd ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f)) → Idx f))
      (∏ i ∈ (T (f := f)) hR, (1 + a i z)) := by
    have := hasProd_fintype ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f)) → Idx f))
    rwa [show (∏ b : ↥(↑(T (f := f) hR) : Set (Idx f)), ((fun i : Idx f => 1 + a i z) ∘ Subtype.val) b) =
      ∏ i ∈ (T (f := f)) hR, (1 + a i z) from Finset.prod_coe_sort (T (f := f) hR) (fun i => 1 + a i z)] at this
  have h2 : HasProd ((fun i : Idx f => 1 + a i z) ∘ (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ → Idx f))
      (tail (f := f) hR z) :=
    (multipliable_one_add_of_summable (f := fun i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ => a (i : Idx f) z)
      ((summable_norm_a (f := f) z).subtype _)).hasProd
  unfold P
  exact (h1.mul_compl h2).tprod_eq

theorem one_add_a_ne_zero_of_far {z : ℂ} {i : Idx f} (h : ‖z - 1 / 2‖ < ‖ctr i‖) : 1 + a i z ≠ 0 := by
  intro h0
  rcases (one_add_a_eq_zero_iff i z).mp h0 with h1 | h1
  · apply lt_irrefl ‖ctr i‖
    calc ‖ctr i‖ = ‖z - 1 / 2‖ := by rw [h1]; rfl
      _ < ‖ctr i‖ := h
  · apply lt_irrefl ‖ctr i‖
    calc ‖ctr i‖ = ‖z - 1 / 2‖ := by
          rw [h1]
          unfold ctr
          rw [show (1 : ℂ) - ((i.1 : Zero f) : ℂ) - 1 / 2 = -(((i.1 : Zero f) : ℂ) - 1 / 2) by ring,
            norm_neg]
      _ < ‖ctr i‖ := h

theorem norm_ctr_of_notMem {R : ℝ} (hR : 0 < R) {i : Idx f} (hi : i ∉ (T (f := f)) hR) : R / 2 < ‖ctr i‖ := by
  rw [mem_T_iff_norm] at hi
  exact lt_of_not_ge hi

theorem tail_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    (tail (f := f)) hR z ≠ 0 := by
  unfold tail
  apply tprod_one_add_ne_zero_of_summable
  · intro i
    apply (one_add_a_ne_zero_of_far (f := f))
    rw [mem_ball, Complex.dist_eq] at hz
    have := (norm_ctr_of_notMem (f := f)) hR (i.2)
    linarith
  · exact (summable_norm_a (f := f) z).subtype _

theorem tail_hasProdLocallyUniformlyOn {R : ℝ} (hR : 0 < R) :
    HasProdLocallyUniformlyOn (fun (i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ) x => 1 + a (i : Idx f) x)
      (tail (f := f) hR) (ball (1 / 2 : ℂ) (R / 2)) :=
  Summable.hasProdLocallyUniformlyOn_one_add isOpen_ball
    (u := fun i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ => (R / 2) ^ 2 * invSq (((i : Idx f).1 : Zero f) : ℂ))
    ((summable_majorant_disc (f := f) (R / 2)).subtype _)
    (Eventually.of_forall fun i x hx => norm_a_le_of_mem_ball hx (i : Idx f))
    (fun i => (continuous_a (i : Idx f)).continuousOn)

theorem tail_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (tail (f := f) hR) (ball (1 / 2 : ℂ) (R / 2)) := by
  have hloc := (hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn).mp
    (tail_hasProdLocallyUniformlyOn (f := f) hR)
  refine hloc.differentiableOn ?_ isOpen_ball
  refine Eventually.of_forall fun t => ?_
  apply Differentiable.differentiableOn
  have hfun : (fun x : ℂ => ∏ i ∈ t, (1 + a (i : Idx f) x)) =
      ∏ i ∈ t, (fun x : ℂ => 1 + a (i : Idx f) x) := by
    funext x
    rw [Finset.prod_apply]
  rw [hfun]
  apply Differentiable.finset_prod
  intro i _
  exact (differentiable_const _).add (differentiable_a (i : Idx f))

omit hf in
/-- The (tail (f := f)) of the inverse squares outside the half disc. -/
def tailInvSq (f : ℂ → ℂ) (R : ℝ) : ℝ := ∑' i : ↥{i : Idx f | R / 2 < ‖ctr i‖}, invSq (((i : Idx f).1 : Zero f) : ℂ)

theorem compl_T_eq {R : ℝ} (hR : 0 < R) : ((↑(T (f := f) hR) : Set (Idx f))ᶜ) = {i : Idx f | R / 2 < ‖ctr i‖} := by
  ext i
  simp only [mem_compl_iff, Finset.mem_coe, mem_setOf_eq, mem_T_iff_norm]
  exact not_le

theorem tailInvSq_nonneg (R : ℝ) : 0 ≤ tailInvSq f R :=
  tsum_nonneg fun _ => invSq_nonneg _

theorem logDeriv_tail {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv (tail (f := f) hR) z = ∑' i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, tank (i : Idx f) z := by
  have hne : ∀ i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, 1 + a (i : Idx f) z ≠ 0 := by
    intro i
    apply (one_add_a_ne_zero_of_far (f := f))
    rw [mem_ball, Complex.dist_eq] at hz
    have := (norm_ctr_of_notMem (f := f)) hR (i.2)
    linarith
  have h := logDeriv_tprod_eq_tsum (f := fun (i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ) w => 1 + a (i : Idx f) w)
    isOpen_ball hz hne
    (fun i => ((differentiable_const (1 : ℂ)).add (differentiable_a (i : Idx f))).differentiableOn)
    (by
      refine ((summable_tank (f := f) z).subtype _).congr ?_
      intro i
      exact (logDeriv_factor (i : Idx f) (hne i)).symm)
    ⟨_, (tail_hasProdLocallyUniformlyOn (f := f)) hR⟩ (tail_ne_zero (f := f) hR hz)
  beta_reduce at h
  unfold tail
  rw [h]
  apply tsum_congr
  intro i
  exact logDeriv_factor (i : Idx f) (hne i)

theorem norm_logDeriv_tail_le {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv (tail (f := f) hR) z‖ ≤ 4 * ‖z - 1 / 2‖ * tailInvSq f R := by
  have hz' : z ∈ ball (1 / 2 : ℂ) (R / 2) := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  rw [(logDeriv_tail (f := f)) hR hz']
  have hzd : ‖z - 1 / 2‖ ≤ R / 8 := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hbound : ∀ i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ,
      ‖tank (i : Idx f) z‖ ≤ 4 * ‖z - 1 / 2‖ * invSq (((i : Idx f).1 : Zero f) : ℂ) := by
    intro i
    apply norm_tank_le
    have h1 := (norm_ctr_of_notMem (f := f)) hR (i.2)
    have h0 : 0 ≤ ‖z - 1 / 2‖ := norm_nonneg _
    nlinarith
  calc ‖∑' i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, tank (i : Idx f) z‖
      ≤ ∑' i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, ‖tank (i : Idx f) z‖ :=
        norm_tsum_le_tsum_norm ((summable_tank (f := f) z).subtype _).norm
    _ ≤ ∑' i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, 4 * ‖z - 1 / 2‖ * invSq (((i : Idx f).1 : Zero f) : ℂ) :=
        Summable.tsum_le_tsum hbound ((summable_tank (f := f) z).subtype _).norm
          (((summable_majorant_disc (f := f) 1).subtype _).mul_left (4 * ‖z - 1 / 2‖) |>.congr
            (fun i => by simp only [Function.comp]; ring))
    _ = 4 * ‖z - 1 / 2‖ * tailInvSq f R := by
        rw [tsum_mul_left]
        unfold tailInvSq
        congr 1
        exact tsum_congr_set_coe (fun i : Idx f => invSq ((i.1 : Zero f) : ℂ)) (compl_T_eq (f := f) hR)

/-- **The (tail (f := f)) of the inverse squares vanishes at infinity.** -/
theorem tailInvSq_tendsto : Tendsto (tailInvSq f) atTop (𝓝 0) := by
  have hsum : Summable (fun i : Idx f => invSq ((i.1 : Zero f) : ℂ)) := by
    have := (summable_majorant_disc (f := f)) 1
    refine this.congr ?_
    intro i
    ring
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun R => lt_of_lt_of_le ha (tailInvSq_nonneg (f := f) R), ?_⟩
  intro ε hε
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hsum (ε / 2) (by positivity)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ i ∈ s, ‖ctr i‖ ≤ M :=
    ⟨∑ i ∈ s, ‖ctr i‖, fun i hi => Finset.single_le_sum (fun j _ => norm_nonneg (ctr j)) hi⟩
  rw [Filter.eventually_atTop]
  refine ⟨2 * M + 2, fun R hR => ?_⟩
  have hle : tailInvSq f R ≤ ε / 2 := by
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
    have hnn : 0 ≤ ∑ j ∈ t, invSq ((((j : Idx f).1 : Zero f) : ℂ)) :=
      Finset.sum_nonneg (fun _ _ => invSq_nonneg _)
    rw [Real.norm_of_nonneg hnn] at this
    exact this.le
  linarith

/-! ## The finite part is the square of the factorization's polynomial -/

/-- The constant of the finite part. -/
def cst {R : ℝ} (hR : 0 < R) : ℂ :=
  ∏ ρ ∈ (Zfac (f := f) hR).zeros, (-1 / (ρ - 1 / 2) ^ 2) ^ (Zfac (f := f) hR).mult ρ

theorem cst_ne_zero {R : ℝ} (hR : 0 < R) : (cst (f := f)) hR ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun ρ hρ =>
    pow_ne_zero _ (div_ne_zero (by norm_num) (pow_ne_zero _ (Zfac_ne_half (f := f) hR hρ)))

theorem finitePart_eq {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∏ i ∈ (T (f := f)) hR, (1 + a i z) = (cst (f := f)) hR * (Zfac (f := f) hR).poly z ^ 2 := by
  have h1 : ∏ i ∈ (T (f := f)) hR, (1 + a i z) =
      ∏ i ∈ (T (f := f)) hR, (fun ρ : ℂ => 1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2) ((i.1 : Zero f) : ℂ) := by
    apply Finset.prod_congr rfl
    intro i _
    simp only [a, ctr]
    ring
  rw [h1, (prod_T (f := f)) hR (fun ρ : ℂ => 1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2), pow_two ((Zfac (f := f) hR).poly z)]
  have h2 : ∀ ρ ∈ (Zfac (f := f) hR).zeros, (1 - ((z - 1 / 2) / (ρ - 1 / 2)) ^ 2) ^ (Zfac (f := f) hR).mult ρ =
      (-1 / (ρ - 1 / 2) ^ 2) ^ (Zfac (f := f) hR).mult ρ *
        ((z - ρ) ^ (Zfac (f := f) hR).mult ρ * (z - (1 - ρ)) ^ (Zfac (f := f) hR).mult ρ) := by
    intro ρ hρ
    rw [← mul_pow, ← mul_pow]
    congr 1
    have hne := (Zfac_ne_half (f := f)) hR hρ
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
    exact (Zfac (f := f) hR).refl_mem ρ hρ
  · intro ρ hρ
    exact (Zfac (f := f) hR).refl_mem ρ hρ
  · intro ρ _
    ring
  · intro ρ _
    ring
  · intro ρ hρ
    rw [(Zfac (f := f) hR).refl_mult ρ hρ]

theorem mult_eq_zero_of_ne_zero {z : ℂ} (hz : f z ≠ 0) : mult f z = 0 := by
  unfold mult
  have ha := hf.diff.analyticAt z
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hz]
  simp

theorem poly_ne_zero {R : ℝ} (hR : 0 < R) {z : ℂ} (hξ : f z ≠ 0) :
    (Zfac (f := f) hR).poly z ≠ 0 := by
  unfold ZeroFactorization.poly
  rw [Finset.prod_ne_zero_iff]
  intro ρ hρ
  apply pow_ne_zero
  intro h
  rw [sub_eq_zero] at h
  subst h
  exact ((mem_zeros_iff (f := f) hR z).mp hρ).1 (mult_eq_zero_of_ne_zero (f := f) hξ)

theorem poly_differentiable {R : ℝ} (hR : 0 < R) : Differentiable ℂ (Zfac (f := f) hR).poly := by
  unfold ZeroFactorization.poly
  have hfun : (fun z : ℂ => ∏ ρ ∈ (Zfac (f := f) hR).zeros, (z - ρ) ^ (Zfac (f := f) hR).mult ρ) =
      ∏ ρ ∈ (Zfac (f := f) hR).zeros, (fun z : ℂ => (z - ρ) ^ (Zfac (f := f) hR).mult ρ) := by
    funext z
    rw [Finset.prod_apply]
  rw [hfun]
  apply Differentiable.finset_prod
  intro ρ _
  exact (differentiable_id.sub_const ρ).pow _

/-! ## The defect `F_R = 2 g′/g − tail′/tail` -/

/-- The defect: analytic on the open half disc, equal to `2 ξ′/ξ − P′/P` off the zeros. -/
def F {R : ℝ} (hR : 0 < R) (z : ℂ) : ℂ :=
  2 * logDeriv (Zfac (f := f) hR).unit z - logDeriv (tail (f := f) hR) z

omit hf in
theorem logDeriv_differentiableOn {φ : ℂ → ℂ} {s : Set ℂ} (hs : IsOpen s)
    (hφ : DifferentiableOn ℂ φ s) (hne : ∀ z ∈ s, φ z ≠ 0) :
    DifferentiableOn ℂ (logDeriv φ) s := by
  have hd : DifferentiableOn ℂ (deriv φ) s := (hφ.analyticOnNhd hs).deriv.differentiableOn
  show DifferentiableOn ℂ (fun z => deriv φ z / φ z) s
  exact hd.div hφ hne

omit hf in
theorem logDeriv_congr {φ g : ℂ → ℂ} {z : ℂ} (h : φ =ᶠ[𝓝 z] g) : logDeriv φ z = logDeriv g z := by
  simp only [logDeriv_apply]
  rw [h.deriv_eq, h.eq_of_nhds]

theorem unit_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (Zfac (f := f) hR).unit (ball (1 / 2 : ℂ) (R / 2)) :=
  (Zfac (f := f) hR).unit_diff.mono (ball_subset_ball (by linarith))

theorem F_differentiableOn {R : ℝ} (hR : 0 < R) :
    DifferentiableOn ℂ (F (f := f) hR) (ball (1 / 2 : ℂ) (R / 2)) := by
  unfold F
  exact ((logDeriv_differentiableOn isOpen_ball (unit_differentiableOn (f := f) hR)
    (fun z hz => (Zfac (f := f) hR).unit_ne z hz)).const_mul 2).sub
    (logDeriv_differentiableOn isOpen_ball (tail_differentiableOn (f := f) hR)
      (fun z hz => (tail_ne_zero (f := f)) hR hz))

theorem F_eq {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2))
    (hξ : f z ≠ 0) :
    (F (f := f)) hR z = 2 * logDeriv f z - logDeriv (P f) z := by
  have hzR : z ∈ ball (1 / 2 : ℂ) R := ball_subset_ball (by linarith) hz
  have hpd := (poly_differentiable (f := f)) hR
  have hpoly_ne : (Zfac (f := f) hR).poly z ≠ 0 := (poly_ne_zero (f := f)) hR hξ
  have hunit_ne : (Zfac (f := f) hR).unit z ≠ 0 := (Zfac (f := f) hR).unit_ne z hz
  have hunit_diff : DifferentiableAt ℂ (Zfac (f := f) hR).unit z :=
    (Zfac (f := f) hR).unit_diff.differentiableAt (isOpen_ball.mem_nhds hzR)
  have htail_ne : (tail (f := f)) hR z ≠ 0 := (tail_ne_zero (f := f)) hR hz
  have htail_diff : DifferentiableAt ℂ (tail (f := f) hR) z :=
    (tail_differentiableOn (f := f) hR).differentiableAt (isOpen_ball.mem_nhds hz)
  have h1 : logDeriv f z = logDeriv (Zfac (f := f) hR).poly z + logDeriv (Zfac (f := f) hR).unit z := by
    have hev : f =ᶠ[𝓝 z] (fun w => (Zfac (f := f) hR).poly w * (Zfac (f := f) hR).unit w) := by
      filter_upwards [isOpen_ball.mem_nhds hzR] with w hw
      exact (Zfac (f := f) hR).factor w hw
    rw [logDeriv_congr hev]
    exact logDeriv_mul z hpoly_ne hunit_ne (hpd z) hunit_diff
  have h2 : logDeriv (P f) z = 2 * logDeriv (Zfac (f := f) hR).poly z + logDeriv (tail (f := f) hR) z := by
    have hP : P f = fun w => (cst (f := f) hR * ((Zfac (f := f) hR).poly w * (Zfac (f := f) hR).poly w)) * (tail (f := f)) hR w := by
      funext w
      rw [(P_split (f := f)) hR w, (finitePart_eq (f := f)) hR w, sq]
    have hpp : DifferentiableAt ℂ (fun w => (Zfac (f := f) hR).poly w * (Zfac (f := f) hR).poly w) z :=
      (hpd z).mul (hpd z)
    have hcpp : DifferentiableAt ℂ (fun w => (cst (f := f)) hR * ((Zfac (f := f) hR).poly w * (Zfac (f := f) hR).poly w)) z :=
      (differentiableAt_const _).mul hpp
    have hcpp_ne : (cst (f := f)) hR * ((Zfac (f := f) hR).poly z * (Zfac (f := f) hR).poly z) ≠ 0 :=
      mul_ne_zero (cst_ne_zero (f := f) hR) (mul_ne_zero hpoly_ne hpoly_ne)
    rw [hP, logDeriv_mul (f := fun w => (cst (f := f)) hR * ((Zfac (f := f) hR).poly w * (Zfac (f := f) hR).poly w))
        (g := (tail (f := f)) hR) z hcpp_ne htail_ne hcpp htail_diff,
      logDeriv_mul (f := fun _ => (cst (f := f)) hR) (g := fun w => (Zfac (f := f) hR).poly w * (Zfac (f := f) hR).poly w) z
        (cst_ne_zero (f := f) hR) (mul_ne_zero hpoly_ne hpoly_ne) (differentiableAt_const _) hpp,
      logDeriv_mul (f := (Zfac (f := f) hR).poly) (g := (Zfac (f := f) hR).poly) z hpoly_ne hpoly_ne (hpd z) (hpd z),
      logDeriv_const, Pi.zero_apply]
    ring
  unfold F
  rw [h1, h2]
  ring

/-! ## The uniform bound on the disc of radius `R/8` -/

omit hf in
/-- The bound of `F_R` on the open disc of radius `R/8`. -/
def bound (f : ℂ → ℂ) (A B σ R : ℝ) : ℝ := 2 * landau f A B σ R + (R / 2) * tailInvSq f R

/-- The tank series splits into the finite population of the half disc and the tail's
log-derivative. -/
theorem tsum_tank_split {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ∑' i : Idx f, FosterClassProduct.tank i z =
      (∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z) + logDeriv (tail (f := f) hR) z := by
  rw [(logDeriv_tail (f := f)) hR hz]
  have h1 : HasSum ((fun i : Idx f => FosterClassProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f)) → Idx f)) (∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z) := by
    have := hasSum_fintype ((fun i : Idx f => FosterClassProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f)) → Idx f))
    rwa [show (∑ b : ↥(↑(T (f := f) hR) : Set (Idx f)), ((fun i : Idx f => FosterClassProduct.tank i z) ∘ Subtype.val) b) =
      ∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z from
        Finset.sum_coe_sort (T (f := f) hR) (fun i => FosterClassProduct.tank i z)] at this
  have h2 : HasSum ((fun i : Idx f => FosterClassProduct.tank i z) ∘
      (Subtype.val : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ → Idx f))
      (∑' i : ↥(↑(T (f := f) hR) : Set (Idx f))ᶜ, FosterClassProduct.tank (i : Idx f) z) :=
    ((summable_tank (f := f) z).subtype _).hasSum
  exact (h1.add_compl h2).tsum_eq

/-- The finite tank sum of the half disc is twice the paired Landau sum. -/
theorem sum_tank_T {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z = 2 * ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) *
      ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) := by
  have h1 : ∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z = ∑ i ∈ (T (f := f)) hR,
      (fun ρ : ℂ => 2 * ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))) ((i.1 : Zero f) : ℂ) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [FosterClassProduct.tank, ctr]
    ring
  rw [h1, (sum_T (f := f)) hR (fun ρ : ℂ => 2 * ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  ring

theorem norm_F_le_of_ne {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hξ : f z ≠ 0) : ‖(F (f := f)) hR z‖ ≤ bound f A B σ R := by
  have hz' : z ∈ ball (1 / 2 : ℂ) (R / 2) := by
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hzd : ‖z - 1 / 2‖ ≤ R / 8 := by
    rw [mem_closedBall, Complex.dist_eq] at hz
    exact hz
  have hm : mult f z = 0 := (mult_eq_zero_of_ne_zero (f := f)) hξ
  set S : ℂ := ∑ ρ ∈ (Zfac (f := f) hR).zeros, ((Zfac (f := f) hR).mult ρ : ℂ) *
    ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) with hS
  have hsplit : logDeriv (P f) z = (∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z) + logDeriv (tail (f := f) hR) z := by
    rw [(logDeriv_P (f := f)) hm, (tsum_tank_split (f := f)) hR hz']
  have hfin : ∑ i ∈ (T (f := f)) hR, FosterClassProduct.tank i z = 2 * S := (sum_tank_T (f := f)) hR z
  have hL : ‖logDeriv f z - S‖ ≤ landau f A B σ R := (Zfac_landau (f := f)) hR z hz hξ
  have hT := (norm_logDeriv_tail_le (f := f)) hR hz
  rw [(F_eq (f := f)) hR hz' hξ, hsplit, hfin]
  calc ‖2 * logDeriv f z - (2 * S + logDeriv (tail (f := f) hR) z)‖
      = ‖2 * (logDeriv f z - S) - logDeriv (tail (f := f) hR) z‖ := by
        congr 1
        ring
    _ ≤ ‖2 * (logDeriv f z - S)‖ + ‖logDeriv (tail (f := f) hR) z‖ := norm_sub_le _ _
    _ = 2 * ‖logDeriv f z - S‖ + ‖logDeriv (tail (f := f) hR) z‖ := by
        rw [norm_mul]
        norm_num
    _ ≤ 2 * landau f A B σ R + 4 * ‖z - 1 / 2‖ * tailInvSq f R := by gcongr
    _ ≤ bound f A B σ R := by
        unfold bound
        have := (tailInvSq_nonneg (f := f)) R
        nlinarith

theorem eventually_ne_zero (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, f w ≠ 0 := by
  have ha := hf.diff.analyticAt z
  rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hall : EqOn f 0 univ :=
      AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (fun x _ => hf.diff.analyticAt x) isPreconnected_univ (mem_univ z) h
    exact hf.centre (hall (mem_univ _))
  · exact h

/-- **The defect is bounded on the open disc of radius `R/8`**, at the zeros by continuity. -/
theorem norm_F_le {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : z ∈ ball (1 / 2 : ℂ) (R / 8)) :
    ‖(F (f := f)) hR z‖ ≤ bound f A B σ R := by
  by_cases hξ : f z ≠ 0
  · exact (norm_F_le_of_ne (f := f)) hR (ball_subset_closedBall hz) hξ
  · push_neg at hξ
    have hcont : ContinuousAt (F (f := f) hR) z :=
      ((F_differentiableOn (f := f) hR).differentiableAt
        (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hz))).continuousAt
    have hlim : Tendsto (fun w => ‖(F (f := f)) hR w‖) (𝓝[≠] z) (𝓝 ‖(F (f := f)) hR z‖) :=
      hcont.norm.tendsto.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    have h1 : ∀ᶠ w in 𝓝[≠] z, w ∈ ball (1 / 2 : ℂ) (R / 8) :=
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz)
    filter_upwards [h1, (eventually_ne_zero (f := f)) z] with w hw hw'
    exact (norm_F_le_of_ne (f := f)) hR (ball_subset_closedBall hw) hw'

end Soma.Holonics.RH.FosterClassSplit

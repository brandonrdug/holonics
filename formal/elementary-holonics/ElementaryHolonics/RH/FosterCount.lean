import Mathlib
import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.AbscissaGrowth
import ElementaryHolonics.RH.RiemannXiGrowth
import ElementaryHolonics.RH.RiemannXiZeroCounting
import ElementaryHolonics.RH.XiCentre

/-!
# FT1 (ii, iii): the count `N(R) ≤ K · R log R` and the exponent of convergence

The order-one envelope of `ξ` gives, through Jensen, the unconditional count of zeros in the
centred disc of radius `R` (`RiemannXiZeroCounting`).  This owner fixes the envelope's constant
once (`growthC`), reads the count against the global multiplicity `mult u`, the order of `ξ` at
`u`, and returns

* `count_le`: for `R ≥ 3`, `N(R) ≤ K · R · log R` with `K` exhibited from `growthC` and the
  centre value;
* `summable_inverse_square`: `Σ_ρ m_ρ / |ρ − ½|² < ∞` over the zeros of `ξ`, the exponent of
  convergence at most two, by dyadic shells: the shell `2^k ≤ |ρ − ½| < 2^{k+1}` carries at most
  `N(2^{k+1})` multiplicity at weight `4^{−k}`, and `Σ (k+1) 2^{−k}` converges.

The centre value `ξ(½) ≠ 0` of `XiCentre` keeps every zero away from the centre.  Every theorem is
discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterCount

open Complex Metric Set Real
open scoped Classical
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.AbscissaGrowth
open Soma.Holonics.RH.RiemannXiGrowth
open Soma.Holonics.RH.RiemannXiZeroCounting
open Soma.Holonics.RH.XiCentre

/-! ## The global multiplicity -/

/-- The multiplicity of `ξ` at a point: the order, as an integer. -/
def mult (u : ℂ) : ℤ := (meromorphicOrderAt riemannXi u).untop₀

theorem mult_eq_divisor {c u : ℂ} {R : ℝ} (hu : u ∈ closedBall c R) :
    MeromorphicOn.divisor riemannXi (closedBall c R) u = mult u :=
  MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu

theorem mult_nonneg (u : ℂ) : 0 ≤ mult u := by
  rw [← mult_eq_divisor (mem_closedBall_self (zero_le_one : (0 : ℝ) ≤ 1))]
  exact (divisor_riemannXi_nonnegative (closedBall u 1)) u

/-- **The centre is not a zero.** -/
theorem mult_half : mult (1 / 2 : ℂ) = 0 := by
  unfold mult
  have ha := differentiable_riemannXi.analyticAt (1 / 2 : ℂ)
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr riemannXi_one_half_ne_zero]
  simp

/-- The zeros of `ξ`, indexed by nonzero multiplicity. -/
abbrev Zero := {u : ℂ // mult u ≠ 0}

theorem Zero.ne_half (u : Zero) : (u : ℂ) ≠ 1 / 2 := by
  intro h
  apply u.2
  rw [h]
  exact mult_half

theorem Zero.dist_pos (u : Zero) : 0 < ‖(u : ℂ) - 1 / 2‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr u.ne_half)

/-! ## The count with the global multiplicity -/

/-- The multiplicity-weighted count of the zeros in the centred closed disc of radius `R`. -/
def N (R : ℝ) : ℝ := ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) R then (mult u : ℝ) else 0

theorem N_eq_inner {R : ℝ} (hR : 0 ≤ R) : N R = innerRiemannXiZeroCount (1 / 2) R := by
  classical
  unfold N innerRiemannXiZeroCount
  apply finsum_congr
  intro u
  by_cases hu : u ∈ closedBall (1 / 2 : ℂ) R
  · rw [if_pos hu, if_pos hu]
    have hu' : u ∈ closedBall (1 / 2 : ℂ) |2 * R| := by
      rw [mem_closedBall] at hu ⊢
      rw [abs_of_nonneg (by positivity)]
      linarith
    rw [mult_eq_divisor hu']
  · rw [if_neg hu, if_neg hu]

/-- The finite support of the counted population. -/
theorem support_finite (w : ℂ → ℝ) (R : ℝ) :
    (Function.support (fun u => if u ∈ closedBall (1 / 2 : ℂ) R then (mult u : ℝ) * w u
      else 0)).Finite := by
  classical
  apply ((MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R)).finiteSupport
    (isCompact_closedBall _ _)).subset
  intro u hu
  rw [Function.mem_support] at hu ⊢
  by_cases hmem : u ∈ closedBall (1 / 2 : ℂ) R
  · rw [if_pos hmem] at hu
    rw [mult_eq_divisor hmem]
    intro h0
    apply hu
    rw [h0]
    simp
  · rw [if_neg hmem] at hu
    exact absurd rfl hu

/-- **A finite family of zeros in the disc is dominated by the weighted count.**  For a nonnegative
weight `w`, the sum of `m_ρ w(ρ)` over any finset of zeros inside the disc is at most the finsum
of the same weight over the disc. -/
theorem sum_le_weighted_finsum {w : ℂ → ℝ} (hw : ∀ u, 0 ≤ w u) {R : ℝ} {ι : Type*}
    (φ : ι → Zero) (hφ : Function.Injective φ) (s : Finset ι)
    (hs : ∀ i ∈ s, ((φ i : Zero) : ℂ) ∈ closedBall (1 / 2 : ℂ) R) :
    ∑ i ∈ s, (mult (φ i : ℂ) : ℝ) * w (φ i : ℂ) ≤
      ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) R then (mult u : ℝ) * w u else 0 := by
  classical
  set g : ℂ → ℝ := fun u => if u ∈ closedBall (1 / 2 : ℂ) R then (mult u : ℝ) * w u else 0
    with hg
  have hinj : Function.Injective (fun i => ((φ i : Zero) : ℂ)) :=
    Subtype.val_injective.comp hφ
  set T : Finset ℂ := (support_finite w R).toFinset ∪ s.image (fun i => ((φ i : Zero) : ℂ))
    with hT
  have hsupp : Function.support g ⊆ ↑T := by
    intro u hu
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hu
  rw [finsum_eq_sum_of_support_subset g hsupp]
  have himg : ∑ i ∈ s, (mult (φ i : ℂ) : ℝ) * w (φ i : ℂ) =
      ∑ u ∈ s.image (fun i => ((φ i : Zero) : ℂ)), g u := by
    rw [Finset.sum_image (fun i _ j _ h => hinj h)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hg]
    simp only
    rw [if_pos (hs i hi)]
  rw [himg]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro u hu
    rw [hT, Finset.mem_union]
    exact Or.inr hu
  · intro u _ _
    rw [hg]
    simp only
    split_ifs
    · exact mul_nonneg (by exact_mod_cast mult_nonneg u) (hw u)
    · exact le_rfl

/-! ## The growth constant, fixed once -/

/-- The order-one envelope's constant, chosen once. -/
def growthC : ℝ := Classical.choose abscissaGrowthOfRiemannXiHolds

theorem growthC_pos : 0 < growthC := (Classical.choose_spec abscissaGrowthOfRiemannXiHolds).1

theorem growthC_spec (c : ℂ) {R : ℝ} (hR : 1 ≤ R) :
    circleAverage (fun z => Real.log ‖riemannXi z‖) c R
      ≤ growthC * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2) :=
  (Classical.choose_spec abscissaGrowthOfRiemannXiHolds).2 c R hR

theorem norm_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real]
  norm_num

/-- The weighted Jensen count at the fixed constant. -/
theorem weightedCount_le {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : riemannXi c ≠ 0) :
    ∑ᶠ u, (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℝ) *
        Real.log (R * ‖c - u‖⁻¹)
      ≤ growthC * (‖c‖ + R + 2) * Real.log (‖c‖ + R + 2) - Real.log ‖riemannXi c‖ := by
  rw [weightedRiemannXiZeros_eq_boundaryAverage (ne_of_gt (by linarith : (0 : ℝ) < R)) hc]
  linarith [growthC_spec c hR]

/-- The inner count at the fixed constant, centred at `½`. -/
theorem logTwo_mul_N_le {R : ℝ} (hR : 1 ≤ R) :
    Real.log 2 * N R ≤
      growthC * (1 / 2 + 2 * R + 2) * Real.log (1 / 2 + 2 * R + 2) - Real.log ‖riemannXi (1 / 2)‖ := by
  rw [N_eq_inner (by linarith)]
  have h1 := logTwo_mul_innerRiemannXiZeroCount_le_weightedOuterCount (c := (1 / 2 : ℂ)) (R := R)
    (by linarith) riemannXi_one_half_ne_zero
  have h2 := weightedCount_le (c := (1 / 2 : ℂ)) (R := 2 * R) (by linarith)
    riemannXi_one_half_ne_zero
  rw [norm_half] at h2
  exact h1.trans h2

/-- The centre's logarithmic debt. -/
def L₀ : ℝ := max 0 (-Real.log ‖riemannXi (1 / 2)‖)

/-- **The exhibited constant** of `N(R) ≤ K R log R`. -/
def K : ℝ := (6 * growthC + L₀) / Real.log 2

theorem K_pos : 0 < K := by
  unfold K
  have h1 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : 0 ≤ L₀ := le_max_left _ _
  have := growthC_pos
  positivity

/-- **FT1 (ii): the count is at most `K · R · log R` for `R ≥ 3`.** -/
theorem count_le {R : ℝ} (hR : 3 ≤ R) : N R ≤ K * (R * Real.log R) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmain := logTwo_mul_N_le (R := R) (by linarith)
  set a : ℝ := 1 / 2 + 2 * R + 2 with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have ha3 : a ≤ 3 * R := by rw [ha]; linarith
  have hlogR : 1 < Real.log R := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlog3 : Real.log 3 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hmono : a * Real.log a ≤ 3 * R * Real.log (3 * R) := mulLog_mono_on_one ha1 ha3
  have hsplit : Real.log (3 * R) = Real.log 3 + Real.log R :=
    Real.log_mul (by norm_num) (by linarith)
  have hR0 : 0 ≤ R := by linarith
  have hbound : a * Real.log a ≤ 6 * (R * Real.log R) := by
    calc a * Real.log a ≤ 3 * R * Real.log (3 * R) := hmono
      _ = 3 * R * (Real.log 3 + Real.log R) := by rw [hsplit]
      _ ≤ 3 * R * (Real.log R + Real.log R) := by gcongr
      _ = 6 * (R * Real.log R) := by ring
  have hL : -Real.log ‖riemannXi (1 / 2)‖ ≤ L₀ := le_max_right _ _
  have hRlog : 1 ≤ R * Real.log R := by nlinarith
  have hL' : L₀ ≤ L₀ * (R * Real.log R) := by
    have h0 : 0 ≤ L₀ := le_max_left _ _
    nlinarith
  have hC := growthC_pos
  have key : Real.log 2 * N R ≤ (6 * growthC + L₀) * (R * Real.log R) := by
    calc Real.log 2 * N R
        ≤ growthC * a * Real.log a - Real.log ‖riemannXi (1 / 2)‖ := hmain
      _ = growthC * (a * Real.log a) + (-Real.log ‖riemannXi (1 / 2)‖) := by ring
      _ ≤ growthC * (6 * (R * Real.log R)) + L₀ * (R * Real.log R) := by
          gcongr
          linarith
      _ = (6 * growthC + L₀) * (R * Real.log R) := by ring
  unfold K
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  linarith

/-! ## FT1 (iii): the exponent of convergence -/

/-- The inverse-square weight from the centre. -/
def invSq (u : ℂ) : ℝ := (‖u - 1 / 2‖ ^ 2)⁻¹

theorem invSq_nonneg (u : ℂ) : 0 ≤ invSq u := by
  unfold invSq
  positivity

/-- The dyadic shell of a zero: `k` with `2^k ≤ |ρ − ½| < 2^{k+1}`, and `0` below `2`. -/
def shell (u : Zero) : ℕ := (Int.log 2 ‖(u : ℂ) - 1 / 2‖).toNat

theorem lt_two_pow_shell_succ (u : Zero) : ‖(u : ℂ) - 1 / 2‖ < 2 ^ (shell u + 1) := by
  have h := Int.lt_zpow_succ_log_self (b := 2) (R := ℝ) (by norm_num) ‖(u : ℂ) - 1 / 2‖
  have hle : Int.log 2 ‖(u : ℂ) - 1 / 2‖ + 1 ≤ ((shell u + 1 : ℕ) : ℤ) := by
    unfold shell
    push_cast
    linarith [Int.self_le_toNat (Int.log 2 ‖(u : ℂ) - 1 / 2‖)]
  calc ‖(u : ℂ) - 1 / 2‖ < (2 : ℝ) ^ (Int.log 2 ‖(u : ℂ) - 1 / 2‖ + 1) := by exact_mod_cast h
    _ ≤ (2 : ℝ) ^ ((shell u + 1 : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
    _ = 2 ^ (shell u + 1) := by rw [zpow_natCast]

theorem two_pow_shell_le {u : Zero} (hk : 1 ≤ shell u) : (2 : ℝ) ^ shell u ≤ ‖(u : ℂ) - 1 / 2‖ := by
  have hpos := u.dist_pos
  have h := Int.zpow_log_le_self (b := 2) (R := ℝ) (by norm_num) hpos
  have hlog : Int.log 2 ‖(u : ℂ) - 1 / 2‖ = (shell u : ℤ) := by
    unfold shell at hk ⊢
    have : 0 ≤ Int.log 2 ‖(u : ℂ) - 1 / 2‖ := by
      by_contra hneg
      push_neg at hneg
      have : (Int.log 2 ‖(u : ℂ) - 1 / 2‖).toNat = 0 := Int.toNat_of_nonpos hneg.le
      omega
    exact (Int.toNat_of_nonneg this).symm
  calc (2 : ℝ) ^ shell u = (2 : ℝ) ^ ((shell u : ℕ) : ℤ) := by rw [zpow_natCast]
    _ = (2 : ℝ) ^ Int.log 2 ‖(u : ℂ) - 1 / 2‖ := by rw [hlog]
    _ ≤ ‖(u : ℂ) - 1 / 2‖ := by exact_mod_cast h

/-- On shell `k ≥ 1` the weight is at most `4^{−k}`. -/
theorem invSq_le_of_shell {u : Zero} (hk : 1 ≤ shell u) :
    invSq (u : ℂ) ≤ ((4 : ℝ) ^ shell u)⁻¹ := by
  unfold invSq
  have h := two_pow_shell_le hk
  have h2 : (0 : ℝ) < 2 ^ shell u := by positivity
  have hsq : (4 : ℝ) ^ shell u ≤ ‖(u : ℂ) - 1 / 2‖ ^ 2 := by
    calc (4 : ℝ) ^ shell u = ((2 : ℝ) ^ shell u) ^ 2 := by
          rw [← pow_mul, mul_comm, pow_mul]
          norm_num
      _ ≤ ‖(u : ℂ) - 1 / 2‖ ^ 2 := by gcongr
  exact inv_anti₀ (by positivity) hsq

/-- Every zero of shell `k` lies in the closed disc of radius `2^{k+1}`. -/
theorem mem_closedBall_of_shell (u : Zero) :
    (u : ℂ) ∈ closedBall (1 / 2 : ℂ) (2 ^ (shell u + 1)) := by
  rw [mem_closedBall, Complex.dist_eq]
  exact (lt_two_pow_shell_succ u).le

/-- The weighted term of a zero. -/
def term (u : Zero) : ℝ := (mult (u : ℂ) : ℝ) * invSq (u : ℂ)

theorem term_nonneg (u : Zero) : 0 ≤ term u :=
  mul_nonneg (by exact_mod_cast mult_nonneg _) (invSq_nonneg _)

/-- The fibre of a shell. -/
abbrev Fibre (k : ℕ) := {u : Zero // shell u = k}

/-- **The partial sums over shell `k ≥ 1` are at most `4^{−k} N(2^{k+1})`.** -/
theorem fibre_sum_le {k : ℕ} (hk : 1 ≤ k) (s : Finset (Fibre k)) :
    ∑ v ∈ s, term (v : Zero) ≤ ((4 : ℝ) ^ k)⁻¹ * N (2 ^ (k + 1)) := by
  classical
  have hstep : ∑ v ∈ s, term (v : Zero) ≤ ∑ v ∈ s, (mult ((v : Zero) : ℂ) : ℝ) * ((4 : ℝ) ^ k)⁻¹ := by
    apply Finset.sum_le_sum
    intro v _
    unfold term
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast mult_nonneg _)
    have := invSq_le_of_shell (u := (v : Zero)) (by rw [v.2]; exact hk)
    rwa [v.2] at this
  refine hstep.trans ?_
  rw [← Finset.sum_mul, mul_comm (((4 : ℝ) ^ k)⁻¹) (N _)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := sum_le_weighted_finsum (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (R := 2 ^ (k + 1)) (fun v : Fibre k => (v : Zero)) Subtype.val_injective s
    (fun v _ => by
      have := mem_closedBall_of_shell (v : Zero)
      rwa [v.2] at this)
  simp only [mul_one] at this
  unfold N
  exact this

/-- The weighted finsum over the disc of radius two, bounding the inner shell. -/
def M₀ : ℝ := ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) 2 then (mult u : ℝ) * invSq u else 0

/-- **The partial sums over the inner shell are at most `M₀`.** -/
theorem fibre_zero_sum_le (s : Finset (Fibre 0)) : ∑ v ∈ s, term (v : Zero) ≤ M₀ := by
  classical
  unfold M₀
  have := sum_le_weighted_finsum (w := invSq) invSq_nonneg (R := 2)
    (fun v : Fibre 0 => (v : Zero)) Subtype.val_injective s
    (fun v _ => by
      have h := mem_closedBall_of_shell (v : Zero)
      rw [v.2] at h
      simpa using h)
  exact this

/-- The dyadic majorant of the shell sums. -/
def majorant (k : ℕ) : ℝ :=
  M₀ * (if k = 0 then 1 else 0) + 2 * K * Real.log 2 * (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k)

theorem summable_majorant : Summable majorant := by
  unfold majorant
  apply Summable.add
  · exact (hasSum_ite_eq 0 (1 : ℝ)).summable.mul_left M₀
  · apply Summable.mul_left
    have h1 : Summable (fun k : ℕ => ((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := by
      have hr : ‖(1 / 2 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num
      have ha := summable_pow_mul_geometric_of_norm_lt_one 1 hr
      have hb := summable_pow_mul_geometric_of_norm_lt_one 0 hr
      have := ha.add hb
      refine this.congr ?_
      intro k
      simp only [pow_one, pow_zero, one_mul]
      ring
    exact h1

/-- **Every shell sum is at most its majorant.** -/
theorem fibre_tsum_le (k : ℕ) : ∑' v : Fibre k, term (v : Zero) ≤ majorant k := by
  apply Real.tsum_le_of_sum_le (fun v => term_nonneg _)
  intro s
  unfold majorant
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h1 := fibre_zero_sum_le s
    have h2 : 0 ≤ 2 * K * Real.log 2 * ((((0 : ℕ) : ℝ) + 1) * (1 / 2 : ℝ) ^ (0 : ℕ)) := by
      have := K_pos
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    rw [if_pos rfl, mul_one]
    linarith
  · have hk1 : 1 ≤ k := hk
    have h := fibre_sum_le hk1 s
    have hR : (3 : ℝ) ≤ 2 ^ (k + 1) := by
      have : (2 : ℝ) ^ 2 ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have hN := count_le hR
    have hlog : Real.log ((2 : ℝ) ^ (k + 1)) = ((k : ℝ) + 1) * Real.log 2 := by
      rw [Real.log_pow]
      push_cast
      ring
    rw [hlog] at hN
    have hne : k ≠ 0 := by omega
    rw [if_neg hne, mul_zero, zero_add]
    have h4 : ((4 : ℝ) ^ k)⁻¹ = (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k := by
      rw [← mul_pow, show (1 / 2 : ℝ) * (1 / 2) = (4 : ℝ)⁻¹ by norm_num, inv_pow]
    have h2k : (2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ k = 2 := by
      rw [pow_succ, mul_comm ((2 : ℝ) ^ k) 2, mul_assoc, ← mul_pow]
      norm_num
    have hK := K_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpow : 0 ≤ (1 / 2 : ℝ) ^ k := by positivity
    calc ∑ v ∈ s, term (v : Zero) ≤ ((4 : ℝ) ^ k)⁻¹ * N (2 ^ (k + 1)) := h
      _ ≤ ((4 : ℝ) ^ k)⁻¹ * (K * ((2 : ℝ) ^ (k + 1) * (((k : ℝ) + 1) * Real.log 2))) := by
          gcongr
      _ = 2 * K * Real.log 2 * (((k : ℝ) + 1) * (1 / 2 : ℝ) ^ k) := by
          rw [h4]
          have : (1 / 2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k * (K * ((2 : ℝ) ^ (k + 1) *
              (((k : ℝ) + 1) * Real.log 2))) =
              ((2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ k) * (K * Real.log 2 * (((k : ℝ) + 1) *
                (1 / 2 : ℝ) ^ k)) := by ring
          rw [this, h2k]
          ring

/-- Every shell is summable, its partial sums being bounded. -/
theorem summable_fibre (k : ℕ) : Summable (fun v : Fibre k => term (v : Zero)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact summable_of_sum_le (fun v => term_nonneg _) (fun s => fibre_zero_sum_le s)
  · exact summable_of_sum_le (fun v => term_nonneg _) (fun s => fibre_sum_le hk s)

/-- **FT1 (iii): the exponent of convergence.**  `Σ_ρ m_ρ / |ρ − ½|²` converges over the zeros
of `ξ`. -/
theorem summable_inverse_square : Summable term := by
  rw [← (Equiv.sigmaFiberEquiv shell).summable_iff]
  have hnn : ∀ x : (k : ℕ) × Fibre k, 0 ≤ (term ∘ (Equiv.sigmaFiberEquiv shell)) x :=
    fun x => term_nonneg _
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun k => ?_, ?_⟩
  · show Summable (fun v : Fibre k => term (v : Zero))
    exact summable_fibre k
  · show Summable (fun k : ℕ => ∑' v : Fibre k, term (v : Zero))
    exact Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun v => term_nonneg _))
      (fun k => fibre_tsum_le k) summable_majorant

end Soma.Holonics.RH.FosterCount

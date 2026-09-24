import Mathlib
import ElementaryHolonics.RH.FosterClassLandau

/-!
# FT4 (i): the Foster class — FT1 for every member

For a member `f` of the class: the global multiplicity `mult f u`, the count
`N f R ≤ K₁ + K₂ (½ + 2R)^σ` with `K₁, K₂` exhibited from the class's `A, B, σ` and the centre
value, and the exponent of convergence `Σ_ρ m_ρ |ρ − ½|^{−2} < ∞` by dyadic shells with the
geometric ratio `2^{σ−2} < 1`. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassCount

open Complex Metric Set Real
open scoped Classical
open Soma.Holonics.RH.FosterClassLandau

variable {f : ℂ → ℂ} {A B σ : ℝ}

/-! ## The global multiplicity -/

/-- The multiplicity of `f` at a point: the order, as an integer. -/
def mult (f : ℂ → ℂ) (u : ℂ) : ℤ := (meromorphicOrderAt f u).untop₀

theorem mult_eq_divisor [hf : FosterClass f A B σ] {c u : ℂ} {R : ℝ} (hu : u ∈ closedBall c R) :
    MeromorphicOn.divisor f (closedBall c R) u = mult f u :=
  MeromorphicOn.divisor_apply (hf.meromorphicOn _) hu

theorem mult_nonneg [hf : FosterClass f A B σ] (u : ℂ) : 0 ≤ mult f u := by
  rw [← mult_eq_divisor (f := f) (mem_closedBall_self (zero_le_one : (0 : ℝ) ≤ 1))]
  exact (hf.divisor_nonneg (closedBall u 1)) u

/-- **The centre is not a zero.** -/
theorem mult_half [hf : FosterClass f A B σ] : mult f (1 / 2 : ℂ) = 0 := by
  unfold mult
  have ha := hf.analyticAt (1 / 2 : ℂ)
  rw [ha.meromorphicOrderAt_eq, ha.analyticOrderAt_eq_zero.mpr hf.centre]
  simp

/-- The zeros of `f`, indexed by nonzero multiplicity. -/
abbrev Zero (f : ℂ → ℂ) := {u : ℂ // mult f u ≠ 0}

theorem Zero.ne_half [hf : FosterClass f A B σ] (u : Zero f) : (u : ℂ) ≠ 1 / 2 := by
  intro h
  apply u.2
  rw [h]
  exact mult_half (f := f) 

theorem Zero.dist_pos [hf : FosterClass f A B σ] (u : Zero f) : 0 < ‖(u : ℂ) - 1 / 2‖ :=
  norm_pos_iff.mpr (sub_ne_zero.mpr (Zero.ne_half u))

/-! ## The count with the global multiplicity -/

/-- The multiplicity-weighted count of the zeros in the centred closed disc of radius `R`. -/
def N (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) R then (mult f u : ℝ) else 0

theorem N_eq_finsum_divisor [hf : FosterClass f A B σ] (R : ℝ) :
    N f R = ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u : ℤ) : ℝ) := by
  have hfin := (MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R)).finiteSupport
    (isCompact_closedBall _ _)
  rw [show ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u : ℤ) : ℝ) =
      ∑ᶠ u, ((MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u : ℤ) : ℝ) from
      map_finsum (Int.castRingHom ℝ) hfin]
  unfold N
  apply finsum_congr
  intro u
  by_cases hu : u ∈ closedBall (1 / 2 : ℂ) R
  · rw [if_pos hu, mult_eq_divisor (f := f) hu]
  · rw [if_neg hu]
    have : MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R) u = 0 := by
      by_contra h
      exact hu ((MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R)).supportWithinDomain
        (Function.mem_support.mpr h))
    rw [this]
    simp

/-- The centre's logarithmic debt. -/
def L₀ (f : ℂ → ℂ) : ℝ := max 0 (-Real.log ‖f (1 / 2 : ℂ)‖)

theorem L₀_nonneg : 0 ≤ L₀ f := le_max_left _ _

theorem neg_log_le_L₀ : -Real.log ‖f (1 / 2 : ℂ)‖ ≤ L₀ f := le_max_right _ _

theorem log_jensenM_le [hf : FosterClass f A B σ] (r : ℝ) :
    Real.log (jensenM f A B σ r / ‖f (1 / 2 : ℂ)‖) ≤ L₀ f + budget f A B σ r := by
  have hx : 0 < ‖f (1 / 2 : ℂ)‖ := norm_pos_iff.mpr hf.centre
  have hj : 0 < jensenM f A B σ r := lt_of_lt_of_le one_pos (one_le_jensenM r)
  rw [Real.log_div hj.ne' hx.ne']
  have hX := budget_pos (f := f) (A := A) (B := B) (σ := σ) r
  have hlogj : Real.log (jensenM f A B σ r) ≤
      max 0 (Real.log ‖f (1 / 2 : ℂ)‖ + budget f A B σ r) := by
    unfold jensenM
    by_cases h : 1 ≤ ‖f (1 / 2 : ℂ)‖ * Real.exp (budget f A B σ r)
    · rw [max_eq_right h, Real.log_mul hx.ne' (Real.exp_pos _).ne', Real.log_exp]
      exact le_max_right _ _
    · push_neg at h
      rw [max_eq_left h.le, Real.log_one]
      exact le_max_left _ _
  have hL1 : 0 ≤ L₀ f := L₀_nonneg
  have hL2 : -Real.log ‖f (1 / 2 : ℂ)‖ ≤ L₀ f := neg_log_le_L₀
  have hmax : max 0 (Real.log ‖f (1 / 2 : ℂ)‖ + budget f A B σ r) ≤
      L₀ f + budget f A B σ r + Real.log ‖f (1 / 2 : ℂ)‖ :=
    max_le (by linarith) (by linarith)
  linarith

theorem budget_le [hf : FosterClass f A B σ] {r : ℝ} (hr : 0 ≤ r) :
    budget f A B σ r ≤ 1 + max 0 (Real.log A) + B * (1 / 2 + r) ^ σ + L₀ f := by
  unfold budget
  have h1 : 0 ≤ max 0 (Real.log A) := le_max_left _ _
  have h2 : Real.log A ≤ max 0 (Real.log A) := le_max_right _ _
  have h3 := neg_log_le_L₀ (f := f)
  have h4 : 0 ≤ L₀ f := L₀_nonneg
  have h5 : 0 ≤ B * (1 / 2 + r) ^ σ :=
    mul_nonneg hf.B_nonneg (Real.rpow_nonneg (by linarith) _)
  apply max_le
  · linarith
  · linarith

/-- The constants of the count. -/
def K₁ (f : ℂ → ℂ) (A : ℝ) : ℝ := (2 * L₀ f + 1 + max 0 (Real.log A)) / Real.log (3 / 2)

def K₂ (B : ℝ) : ℝ := B / Real.log (3 / 2)

theorem K₁_nonneg : 0 ≤ K₁ f A := by
  unfold K₁
  have := L₀_nonneg (f := f)
  have h : 0 ≤ max 0 (Real.log A) := le_max_left _ _
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  positivity

theorem K₂_nonneg [hf : FosterClass f A B σ] : 0 ≤ K₂ B := by
  unfold K₂
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  exact div_nonneg hf.B_nonneg hl.le

/-- **The count of the closed disc of radius `R`.** -/
theorem count_le [hf : FosterClass f A B σ] {R : ℝ} (hR : 0 < R) :
    N f R ≤ K₁ f A + K₂ B * (1 / 2 + 2 * R) ^ σ := by
  have h2R : 0 < 2 * R := by linarith
  have hhalf : 2 * R / 2 = R := by ring
  have h := finsum_divisor_le (f := f) h2R
  rw [hhalf, ← N_eq_finsum_divisor (f := f) R] at h
  have hJ := log_jensenM_le (f := f) (2 * R)
  have hb := budget_le (f := f) (r := 2 * R) (by linarith)
  have hl : 0 < Real.log (3 / 2) := Real.log_pos (by norm_num)
  unfold K₁ K₂
  rw [div_mul_eq_mul_div, ← add_div]
  exact h.trans (div_le_div_of_nonneg_right (by linarith) hl.le)

/-- The finite support of the counted population. -/
theorem support_finite [hf : FosterClass f A B σ] (w : ℂ → ℝ) (R : ℝ) :
    (Function.support (fun u => if u ∈ closedBall (1 / 2 : ℂ) R then (mult f u : ℝ) * w u
      else 0)).Finite := by
  classical
  apply ((MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) R)).finiteSupport
    (isCompact_closedBall _ _)).subset
  intro u hu
  rw [Function.mem_support] at hu ⊢
  by_cases hmem : u ∈ closedBall (1 / 2 : ℂ) R
  · rw [if_pos hmem] at hu
    rw [mult_eq_divisor (f := f) hmem]
    intro h0
    apply hu
    rw [h0]
    simp
  · rw [if_neg hmem] at hu
    exact absurd rfl hu

/-- **A finite family of zeros in the disc is dominated by the weighted count.** For a nonnegative
weight `w`, the sum of `m_ρ w(ρ)` over any finset of zeros inside the disc is at most the finsum
of the same weight over the disc. -/
theorem sum_le_weighted_finsum [hf : FosterClass f A B σ] {w : ℂ → ℝ} (hw : ∀ u, 0 ≤ w u)
    {R : ℝ} {ι : Type*}
    (φ : ι → Zero f) (hφ : Function.Injective φ) (s : Finset ι)
    (hs : ∀ i ∈ s, ((φ i : Zero f) : ℂ) ∈ closedBall (1 / 2 : ℂ) R) :
    ∑ i ∈ s, (mult f (φ i : ℂ) : ℝ) * w (φ i : ℂ) ≤
      ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) R then (mult f u : ℝ) * w u else 0 := by
  classical
  set g : ℂ → ℝ := fun u => if u ∈ closedBall (1 / 2 : ℂ) R then (mult f u : ℝ) * w u else 0
    with hg
  have hinj : Function.Injective (fun i => ((φ i : Zero f) : ℂ)) :=
    Subtype.val_injective.comp hφ
  set T : Finset ℂ := (support_finite (f := f) w R).toFinset ∪ s.image (fun i => ((φ i : Zero f) : ℂ))
    with hT
  have hsupp : Function.support g ⊆ ↑T := by
    intro u hu
    rw [hT, Finset.coe_union, Set.Finite.coe_toFinset]
    exact Or.inl hu
  rw [finsum_eq_sum_of_support_subset g hsupp]
  have himg : ∑ i ∈ s, (mult f (φ i : ℂ) : ℝ) * w (φ i : ℂ) =
      ∑ u ∈ s.image (fun i => ((φ i : Zero f) : ℂ)), g u := by
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
    · exact mul_nonneg (by exact_mod_cast mult_nonneg (f := f) u) (hw u)
    · exact le_rfl

/-! ## FT1 (iii): the exponent of convergence -/

/-- The inverse-square weight from the centre. -/
def invSq (u : ℂ) : ℝ := (‖u - 1 / 2‖ ^ 2)⁻¹

theorem invSq_nonneg (u : ℂ) : 0 ≤ invSq u := by
  unfold invSq
  positivity

/-- The dyadic shell of a zero: `k` with `2^k ≤ |ρ − ½| < 2^{k+1}`, and `0` below `2`. -/
def shell (u : Zero f) : ℕ := (Int.log 2 ‖(u : ℂ) - 1 / 2‖).toNat

theorem lt_two_pow_shell_succ (u : Zero f) : ‖(u : ℂ) - 1 / 2‖ < 2 ^ (shell u + 1) := by
  have h := Int.lt_zpow_succ_log_self (b := 2) (R := ℝ) (by norm_num) ‖(u : ℂ) - 1 / 2‖
  have hle : Int.log 2 ‖(u : ℂ) - 1 / 2‖ + 1 ≤ ((shell u + 1 : ℕ) : ℤ) := by
    unfold shell
    push_cast
    linarith [Int.self_le_toNat (Int.log 2 ‖(u : ℂ) - 1 / 2‖)]
  calc ‖(u : ℂ) - 1 / 2‖ < (2 : ℝ) ^ (Int.log 2 ‖(u : ℂ) - 1 / 2‖ + 1) := by exact_mod_cast h
    _ ≤ (2 : ℝ) ^ ((shell u + 1 : ℕ) : ℤ) := zpow_le_zpow_right₀ (by norm_num) hle
    _ = 2 ^ (shell u + 1) := by rw [zpow_natCast]

theorem two_pow_shell_le [hf : FosterClass f A B σ] {u : Zero f} (hk : 1 ≤ shell u) : (2 : ℝ) ^ shell u ≤ ‖(u : ℂ) - 1 / 2‖ := by
  have hpos := Zero.dist_pos u
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
theorem invSq_le_of_shell [hf : FosterClass f A B σ] {u : Zero f} (hk : 1 ≤ shell u) :
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
theorem mem_closedBall_of_shell (u : Zero f) :
    (u : ℂ) ∈ closedBall (1 / 2 : ℂ) (2 ^ (shell u + 1)) := by
  rw [mem_closedBall, Complex.dist_eq]
  exact (lt_two_pow_shell_succ u).le

/-- The weighted term of a zero. -/
def term (u : Zero f) : ℝ := (mult f (u : ℂ) : ℝ) * invSq (u : ℂ)

theorem term_nonneg [hf : FosterClass f A B σ] (u : Zero f) : 0 ≤ term u :=
  mul_nonneg (by exact_mod_cast mult_nonneg (f := f) _) (invSq_nonneg _)

/-- The fibre of a shell. -/
abbrev Fibre (f : ℂ → ℂ) (k : ℕ) := {u : Zero f // shell u = k}

/-- **The partial sums over shell `k ≥ 1` are at most `4^{−k} N(2^{k+1})`.** -/
theorem fibre_sum_le [hf : FosterClass f A B σ] {k : ℕ} (hk : 1 ≤ k) (s : Finset (Fibre f k)) :
    ∑ v ∈ s, term (v : Zero f) ≤ ((4 : ℝ) ^ k)⁻¹ * N f (2 ^ (k + 1)) := by
  classical
  have hstep : ∑ v ∈ s, term (v : Zero f) ≤
      ∑ v ∈ s, (mult f ((v : Zero f) : ℂ) : ℝ) * ((4 : ℝ) ^ k)⁻¹ := by
    apply Finset.sum_le_sum
    intro v _
    unfold term
    apply mul_le_mul_of_nonneg_left _ (by exact_mod_cast mult_nonneg (f := f) _)
    have := invSq_le_of_shell (u := (v : Zero f)) (by rw [v.2]; exact hk)
    rwa [v.2] at this
  refine hstep.trans ?_
  rw [← Finset.sum_mul, mul_comm (((4 : ℝ) ^ k)⁻¹) (N f _)]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have := sum_le_weighted_finsum (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one)
    (R := 2 ^ (k + 1)) (fun v : Fibre f k => (v : Zero f)) Subtype.val_injective s
    (fun v _ => by
      have := mem_closedBall_of_shell (v : Zero f)
      rwa [v.2] at this)
  simp only [mul_one] at this
  unfold N
  exact this

/-- The weighted finsum over the disc of radius two, bounding the inner shell. -/
def M₀ (f : ℂ → ℂ) : ℝ :=
  ∑ᶠ u, if u ∈ closedBall (1 / 2 : ℂ) 2 then (mult f u : ℝ) * invSq u else 0

/-- **The partial sums over the inner shell are at most `M₀`.** -/
theorem fibre_zero_sum_le [hf : FosterClass f A B σ] (s : Finset (Fibre f 0)) :
    ∑ v ∈ s, term (v : Zero f) ≤ M₀ f := by
  classical
  unfold M₀
  have := sum_le_weighted_finsum (w := invSq) invSq_nonneg (R := 2)
    (fun v : Fibre f 0 => (v : Zero f)) Subtype.val_injective s
    (fun v _ => by
      have h := mem_closedBall_of_shell (v : Zero f)
      rw [v.2] at h
      simpa using h)
  exact this


/-- The geometric ratio of the shells: `2^σ/4 < 1`. -/
def q (σ : ℝ) : ℝ := (2 : ℝ) ^ σ / 4

theorem q_nonneg (σ : ℝ) : 0 ≤ q σ := by
  unfold q
  positivity

theorem q_lt_one [hf : FosterClass f A B σ] : q σ < 1 := by
  unfold q
  rw [div_lt_one (by norm_num)]
  have : (2 : ℝ) ^ σ < (2 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hf.σ_lt_two
  rw [Real.rpow_two] at this
  linarith

/-- The dyadic majorant of the shell sums. -/
def majorant (f : ℂ → ℂ) (A B σ : ℝ) (k : ℕ) : ℝ :=
  M₀ f * (if k = 0 then 1 else 0) + K₁ f A * (1 / 4 : ℝ) ^ k + K₂ B * 8 ^ σ * q σ ^ k

theorem summable_majorant [hf : FosterClass f A B σ] : Summable (majorant f A B σ) := by
  unfold majorant
  apply Summable.add
  · apply Summable.add
    · exact (hasSum_ite_eq 0 (1 : ℝ)).summable.mul_left (M₀ f)
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  · exact (summable_geometric_of_lt_one (q_nonneg σ) (q_lt_one (f := f) )).mul_left _

theorem count_pow_le [hf : FosterClass f A B σ] (k : ℕ) :
    N f (2 ^ (k + 1)) ≤ K₁ f A + K₂ B * 8 ^ σ * ((2 : ℝ) ^ σ) ^ k := by
  have h := count_le (f := f) (R := 2 ^ (k + 1)) (by positivity)
  refine h.trans ?_
  have hle : (1 / 2 : ℝ) + 2 * 2 ^ (k + 1) ≤ 8 * 2 ^ k := by
    rw [pow_succ]
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  have hpow : ((1 / 2 : ℝ) + 2 * 2 ^ (k + 1)) ^ σ ≤ (8 * 2 ^ k) ^ σ :=
    Real.rpow_le_rpow (by positivity) hle hf.σ_pos.le
  have hsplit : ((8 : ℝ) * 2 ^ k) ^ σ = 8 ^ σ * ((2 : ℝ) ^ σ) ^ k := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      mul_comm (k : ℝ) σ, Real.rpow_mul_natCast (by norm_num)]
  rw [hsplit] at hpow
  have hK := K₂_nonneg (f := f) 
  nlinarith [mul_le_mul_of_nonneg_left hpow hK]

/-- **Every shell sum is at most its majorant.** -/
theorem fibre_tsum_le [hf : FosterClass f A B σ] (k : ℕ) :
    ∑' v : Fibre f k, term (v : Zero f) ≤ majorant f A B σ k := by
  apply Real.tsum_le_of_sum_le (fun v => term_nonneg _)
  intro s
  unfold majorant
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h1 := fibre_zero_sum_le s
    have h2 : 0 ≤ K₁ f A * (1 / 4 : ℝ) ^ (0 : ℕ) + K₂ B * 8 ^ σ * q σ ^ (0 : ℕ) := by
      have := K₁_nonneg (f := f) (A := A)
      have := K₂_nonneg (f := f) 
      have := q_nonneg σ
      positivity
    rw [if_pos rfl, mul_one]
    linarith
  · have hk1 : 1 ≤ k := hk
    have h := fibre_sum_le hk1 s
    have hN := count_pow_le (f := f) k
    have hne : k ≠ 0 := by omega
    rw [if_neg hne, mul_zero, zero_add]
    have h4 : ((4 : ℝ) ^ k)⁻¹ = (1 / 4 : ℝ) ^ k := by rw [one_div, inv_pow]
    have hq : ((4 : ℝ) ^ k)⁻¹ * ((2 : ℝ) ^ σ) ^ k = q σ ^ k := by
      unfold q
      rw [div_pow, div_eq_inv_mul]
    have hK := K₂_nonneg (f := f) 
    have h8 : 0 ≤ (8 : ℝ) ^ σ := by positivity
    calc ∑ v ∈ s, term (v : Zero f) ≤ ((4 : ℝ) ^ k)⁻¹ * N f (2 ^ (k + 1)) := h
      _ ≤ ((4 : ℝ) ^ k)⁻¹ * (K₁ f A + K₂ B * 8 ^ σ * ((2 : ℝ) ^ σ) ^ k) := by gcongr
      _ = K₁ f A * (1 / 4 : ℝ) ^ k + K₂ B * 8 ^ σ * q σ ^ k := by
          rw [← hq, ← h4]
          ring

/-- Every shell is summable, its partial sums being bounded. -/
theorem summable_fibre [hf : FosterClass f A B σ] (k : ℕ) :
    Summable (fun v : Fibre f k => term (v : Zero f)) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    exact summable_of_sum_le (fun v => term_nonneg _) (fun s => fibre_zero_sum_le s)
  · exact summable_of_sum_le (fun v => term_nonneg _) (fun s => fibre_sum_le hk s)

/-- **FT1 (iii) for the class: the exponent of convergence.** -/
theorem summable_inverse_square [hf : FosterClass f A B σ] : Summable (term (f := f)) := by
  rw [← (Equiv.sigmaFiberEquiv (shell (f := f))).summable_iff]
  have hnn : ∀ x : (k : ℕ) × Fibre f k,
      0 ≤ (term ∘ (Equiv.sigmaFiberEquiv (shell (f := f)))) x :=
    fun x => term_nonneg _
  rw [summable_sigma_of_nonneg hnn]
  refine ⟨fun k => ?_, ?_⟩
  · show Summable (fun v : Fibre f k => term (v : Zero f))
    exact summable_fibre (f := f) k
  · show Summable (fun k : ℕ => ∑' v : Fibre f k, term (v : Zero f))
    exact Summable.of_nonneg_of_le (fun k => tsum_nonneg (fun v => term_nonneg _))
      (fun k => fibre_tsum_le (f := f) k) (summable_majorant (f := f) )

end Soma.Holonics.RH.FosterClassCount

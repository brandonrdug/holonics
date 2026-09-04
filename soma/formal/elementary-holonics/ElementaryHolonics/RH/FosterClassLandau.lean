import Mathlib
import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.ZeroComb
import ElementaryHolonics.RH.LandauLemma
import ElementaryHolonics.RH.ZeroFactorizationExists
import ElementaryHolonics.RH.EntireDerivativeGrowth
import ElementaryHolonics.RH.FosterTanks
import ElementaryHolonics.RH.FosterCount

/-!
# FT4 (i): the Foster class — FT0 for every symmetric entire function of finite order below two

A member of the class is an entire `f` with `f(1 − s) = f(s)`, `f(½) ≠ 0`, and the envelope
`‖f w‖ ≤ A exp(B ‖w‖^σ)` with `0 < σ < 2`. This owner returns FT0 for every member: the symmetric
zero factorization on every disc centred at `½`, the budget `budget r` of `log ‖f‖` on the disc,
Jensen's count of the comb, and the paired finite Foster form with Landau's remainder
`16 (budget r + N log 2)/r`. The constants are the class's own `A, B, σ`, never existential.
`ξ` is a member; `heatE t ξ` is a member once FT4 (ii) returns its centre value from the kernel.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassLandau

open Complex Metric Finset
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.FosterTanks

/-- **The Foster class**: symmetric entire functions of finite order below two with a centre
value and an exhibited envelope. -/
class FosterClass (f : ℂ → ℂ) (A B σ : outParam ℝ) : Prop where
  diff : Differentiable ℂ f
  symm : ∀ s, f (1 - s) = f s
  centre : f (1 / 2 : ℂ) ≠ 0
  A_pos : 0 < A
  B_nonneg : 0 ≤ B
  σ_pos : 0 < σ
  σ_lt_two : σ < 2
  growth : HasGrowth f A B σ

variable {f : ℂ → ℂ} {A B σ : ℝ}

theorem FosterClass.analyticAt [hf : FosterClass f A B σ] (z : ℂ) : AnalyticAt ℂ f z :=
  hf.diff.analyticAt z

theorem FosterClass.meromorphicOn [hf : FosterClass f A B σ] (S : Set ℂ) : MeromorphicOn f S :=
  fun u _ => (hf.analyticAt u).meromorphicAt

theorem FosterClass.divisor_nonneg [hf : FosterClass f A B σ] (S : Set ℂ) :
    0 ≤ MeromorphicOn.divisor f S :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (fun u _ => hf.analyticAt u)

theorem FosterClass.meromorphicOrderAt_one_sub [hf : FosterClass f A B σ] (u : ℂ) :
    meromorphicOrderAt f (1 - u) = meromorphicOrderAt f u := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) u := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun s : ℂ ↦ 1 - s) u ≠ 0 := by
    have : deriv (fun s : ℂ ↦ 1 - s) u = -1 := by
      rw [deriv_const_sub, deriv_id'']
    rw [this]
    norm_num
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (f := f) hg hg'
  have hcomp : f ∘ (fun s : ℂ ↦ 1 - s) = f := funext hf.symm
  rw [hcomp] at h
  exact h.symm

/-! ## The symmetric factorization -/

structure SymmetricZeroFactorizationOf (f : ℂ → ℂ) (r : ℝ) extends
    ZeroFactorization f (1 / 2 : ℂ) r where
  refl_mem : ∀ ρ ∈ zeros, 1 - ρ ∈ zeros
  refl_mult : ∀ ρ ∈ zeros, mult (1 - ρ) = mult ρ
  /-- The comb is exactly the support of the divisor of the open disc inside the closed half disc. -/
  mem_zeros_iff : ∀ ρ, ρ ∈ zeros ↔
    (MeromorphicOn.divisor f (ball (1 / 2 : ℂ) r) ρ ≠ 0 ∧ ρ ∈ closedBall (1 / 2 : ℂ) (r / 2))
  /-- The multiplicities are the divisor's. -/
  mult_eq_div : ∀ ρ, (mult ρ : ℤ) = MeromorphicOn.divisor f (ball (1 / 2 : ℂ) r) ρ

theorem one_sub_mem_ball_half_iff {R : ℝ} (u : ℂ) :
    (1 - u) ∈ ball (1 / 2 : ℂ) R ↔ u ∈ ball (1 / 2 : ℂ) R := by
  simp only [Metric.mem_ball, Complex.dist_eq]
  have : (1 - u) - (1 / 2 : ℂ) = -(u - 1 / 2) := by ring
  rw [this, norm_neg]

/-- The divisor on an open disc centred at `½` is reflection symmetric. -/
theorem divisor_one_sub_ball [hf : FosterClass f A B σ] {R : ℝ} (u : ℂ) :
    MeromorphicOn.divisor f (ball (1 / 2 : ℂ) R) (1 - u) =
      MeromorphicOn.divisor f (ball (1 / 2 : ℂ) R) u := by
  by_cases hu : u ∈ ball (1 / 2 : ℂ) R
  · have hu' : (1 - u) ∈ ball (1 / 2 : ℂ) R := (one_sub_mem_ball_half_iff u).mpr hu
    rw [MeromorphicOn.divisor_apply (hf.meromorphicOn _) hu',
      MeromorphicOn.divisor_apply (hf.meromorphicOn _) hu,
      hf.meromorphicOrderAt_one_sub]
  · have hu' : (1 - u) ∉ ball (1 / 2 : ℂ) R :=
      fun h ↦ hu ((one_sub_mem_ball_half_iff u).mp h)
    rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def, if_neg (fun h ↦ hu' h.2),
      if_neg (fun h ↦ hu h.2)]

/-- **Existence of the symmetric factorization**, with its count equal to the divisor mass of
the closed half disc.  The construction is that of `ZeroFactorizationExists`, carried out at the
centre `½`, where the reflection preserves the disc and the divisor. -/
theorem exists_symmetricZeroFactorizationOf_count [hf' : FosterClass f A B σ] {r : ℝ} (hr : 0 < r) :
    ∃ Z : SymmetricZeroFactorizationOf f r,
      (Z.count : ℤ) = ∑ᶠ u, MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) (r / 2)) u := by
  classical
  have hξ : f (1 / 2 : ℂ) ≠ 0 := hf'.centre
  have hdf : Differentiable ℂ f := hf'.diff
  set z₀ : ℂ := 1 / 2 with hz₀
  set U : Set ℂ := ball z₀ r with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hmer : MeromorphicOn f U := fun u _ => (hdf.analyticAt u).meromorphicAt
  have hord : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ :=
    fun u => meromorphicOrderAt_ne_top hdf hξ u
  set D := MeromorphicOn.divisor f U with hDdef
  have hfinC : (Function.support (MeromorphicOn.divisor f (closedBall z₀ r))).Finite :=
    (MeromorphicOn.divisor f (closedBall z₀ r)).finiteSupport (isCompact_closedBall _ _)
  have hDsub : Function.support D ⊆
      Function.support (MeromorphicOn.divisor f (closedBall z₀ r)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain hu
    have huC : u ∈ closedBall z₀ r := ball_subset_closedBall huU
    rw [hDdef, MeromorphicOn.divisor_apply hmer huU] at hu
    rw [MeromorphicOn.divisor_apply (fun v _ => (hdf.analyticAt v).meromorphicAt) huC]
    exact hu
  have hfin : (Function.support D).Finite := hfinC.subset hDsub
  obtain ⟨g, hg, hg0, hcod⟩ := MeromorphicOn.extract_zeros_poles hmer hord hfin
  have han : AnalyticOnNhd ℂ f U := hdf.differentiableOn.analyticOnNhd hUo
  have hDnn : ∀ u, 0 ≤ D u := fun u => by
    first
      | exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
      | exact (AnalyticOnNhd.divisor_nonneg han) u
  set S : Finset ℂ := hfin.toFinset with hSdef
  have hφ : (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) = ∏ u ∈ S, (· - u) ^ D u := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    rw [Function.mem_mulSupport] at hu
    rw [hSdef, Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    rw [h0, zpow_zero]
  have hφeval : ∀ z, (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z = ∏ u ∈ S, (z - u) ^ (D u).toNat := by
    intro z
    rw [hφ, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro u _
    simp only [Pi.pow_apply]
    rw [← Int.toNat_of_nonneg (hDnn u), zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
  have hpt : ∀ z ∈ U, f z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
    intro z hz
    have hφan : AnalyticAt ℂ (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z :=
      Function.FactorizedRational.analyticAt (hDnn z)
    have hcont : ContinuousAt ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) z :=
      hφan.continuousAt.smul (hg z hz).continuousAt
    have := eq_of_codiscreteWithin hUo hcod hz (hdf.continuous.continuousAt) hcont
    rw [this, Pi.smul_apply', smul_eq_mul, hφeval]
  -- the reflection acts on the support and on the divisor
  have hDrefl : ∀ u, D (1 - u) = D u := fun u => by
    rw [hDdef, hUdef, hz₀]
    exact divisor_one_sub_ball u
  have hSrefl : ∀ u ∈ S, 1 - u ∈ S := by
    intro u hu
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support] at hu ⊢
    rw [hDrefl]
    exact hu
  refine ⟨{ zeros := S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2))
            mult := fun ρ => (D ρ).toNat
            unit := fun z => (∏ ρ ∈ S.filter (fun ρ => ρ ∉ closedBall z₀ (r / 2)),
              (z - ρ) ^ (D ρ).toNat) * g z
            zeros_mem := ?_
            mult_pos := ?_
            unit_diff := ?_
            unit_ne := ?_
            factor := ?_
            refl_mem := ?_
            refl_mult := ?_
            mem_zeros_iff := ?_
            mult_eq_div := ?_ }, ?_⟩
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2
  · intro ρ hρ
    have hsupp := (Finset.mem_filter.mp hρ).1
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support] at hsupp
    have := hDnn ρ
    omega
  · apply DifferentiableOn.mul
    · exact DifferentiableOn.fun_finsetProd (f := fun ρ z => (z - ρ) ^ (D ρ).toNat)
        (s := ball z₀ r) (fun ρ _ => by fun_prop)
    · exact hg.differentiableOn
  · intro z hz
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro ρ hρ
      apply pow_ne_zero
      have hout := (Finset.mem_filter.mp hρ).2
      intro h0
      apply hout
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact ball_subset_closedBall hz
    · exact hg0 ⟨z, ball_subset_ball (by linarith) hz⟩
  · intro z hz
    rw [hpt z hz, ← Finset.prod_filter_mul_prod_filter_not S (fun ρ => ρ ∈ closedBall z₀ (r / 2))]
    ring
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hSrefl ρ hρ.1, ?_⟩
    rw [hz₀]
    exact (one_sub_mem_closedBall_half_iff ρ).mpr (hz₀ ▸ hρ.2)
  · intro ρ _
    show (D (1 - ρ)).toNat = (D ρ).toNat
    rw [hDrefl]
  · intro ρ
    rw [Finset.mem_filter, hSdef, Set.Finite.mem_toFinset, Function.mem_support]
  · intro ρ
    show ((D ρ).toNat : ℤ) = D ρ
    exact Int.toNat_of_nonneg (hDnn ρ)
  · set D' := MeromorphicOn.divisor f (closedBall z₀ (r / 2)) with hD'def
    have hmer' : MeromorphicOn f (closedBall z₀ (r / 2)) :=
      fun u _ => (hdf.analyticAt u).meromorphicAt
    have hsub : closedBall z₀ (r / 2) ⊆ U := closedBall_subset_ball (by linarith)
    have hagree : ∀ u ∈ closedBall z₀ (r / 2), D' u = D u := by
      intro u hu
      rw [hD'def, hDdef, MeromorphicOn.divisor_apply hmer' hu,
        MeromorphicOn.divisor_apply hmer (hsub hu)]
    have hsupp : Function.support D' ⊆ ↑(S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2))) := by
      intro u hu
      rw [Function.mem_support] at hu
      have huC : u ∈ closedBall z₀ (r / 2) := D'.supportWithinDomain hu
      rw [Finset.mem_coe, Finset.mem_filter, hSdef, Set.Finite.mem_toFinset, Function.mem_support]
      refine ⟨?_, huC⟩
      rw [← hagree u huC]
      exact hu
    show ((∑ ρ ∈ S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2)), (D ρ).toNat : ℕ) : ℤ) =
      ∑ᶠ u, D' u
    rw [finsum_eq_sum_of_support_subset D' hsupp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hagree ρ (Finset.mem_filter.mp hρ).2, Int.toNat_of_nonneg (hDnn ρ)]

/-! ## The paired finite Foster form with Landau's remainder -/

/-- The zeros of a symmetric factorization are zeros of `f`. -/
theorem SymmetricZeroFactorizationOf.f_eq_zero {r : ℝ} (hr : 0 < r)
    (Z : SymmetricZeroFactorizationOf f r) {ρ : ℂ} (hρ : ρ ∈ Z.zeros) : f ρ = 0 := by
  have hmem : ρ ∈ ball (1 / 2 : ℂ) r := by
    have := Z.zeros_mem ρ hρ
    exact closedBall_subset_ball (by linarith) this
  rw [Z.factor ρ hmem]
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero hρ
  rw [sub_self]
  exact zero_pow (Z.mult_pos ρ hρ).ne'

/-! ## The budget and Jensen's count -/

/-- The budget of `log ‖f‖` on the disc of radius `r` about `½`, relative to the centre. -/
def budget (f : ℂ → ℂ) (A B σ r : ℝ) : ℝ :=
  max 1 (Real.log A + B * (1 / 2 + r) ^ σ - Real.log ‖f (1 / 2 : ℂ)‖)

theorem budget_pos (r : ℝ) : 0 < budget f A B σ r :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

/-- The growth bound on the disc, normalized at the centre. -/
theorem norm_le_of_growth [hf : FosterClass f A B σ] {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball (1 / 2 : ℂ) r) :
    ‖f z‖ ≤ ‖f (1 / 2 : ℂ)‖ * Real.exp (budget f A B σ r) := by
  have hpos₀ : 0 < ‖f (1 / 2 : ℂ)‖ := norm_pos_iff.mpr hf.centre
  have hnz : ‖z‖ ≤ 1 / 2 + r := by
    rw [mem_ball_iff_norm] at hz
    calc ‖z‖ = ‖(z - 1 / 2) + 1 / 2‖ := by ring_nf
      _ ≤ ‖z - 1 / 2‖ + ‖(1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ 1 / 2 + r := by rw [Soma.Holonics.RH.FosterCount.norm_half]; linarith
  have hσ : ‖z‖ ^ σ ≤ (1 / 2 + r) ^ σ := Real.rpow_le_rpow (norm_nonneg _) hnz hf.σ_pos.le
  have hG : ‖f z‖ ≤ A * Real.exp (B * (1 / 2 + r) ^ σ) := by
    calc ‖f z‖ ≤ A * Real.exp (B * ‖z‖ ^ σ) := hf.growth z
      _ ≤ A * Real.exp (B * (1 / 2 + r) ^ σ) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ hf.B_nonneg)) hf.A_pos.le
  have hM : Real.log A + B * (1 / 2 + r) ^ σ - Real.log ‖f (1 / 2 : ℂ)‖ ≤ budget f A B σ r :=
    le_max_right _ _
  calc ‖f z‖ ≤ A * Real.exp (B * (1 / 2 + r) ^ σ) := hG
    _ = Real.exp (Real.log A + B * (1 / 2 + r) ^ σ) := by
        rw [Real.exp_add, Real.exp_log hf.A_pos]
    _ ≤ Real.exp (Real.log ‖f (1 / 2 : ℂ)‖ + budget f A B σ r) := by
        apply Real.exp_le_exp.mpr
        linarith
    _ = ‖f (1 / 2 : ℂ)‖ * Real.exp (budget f A B σ r) := by
        rw [Real.exp_add, Real.exp_log hpos₀]

/-- Jensen's ceiling on the disc. -/
def jensenM (f : ℂ → ℂ) (A B σ r : ℝ) : ℝ :=
  max 1 (‖f (1 / 2 : ℂ)‖ * Real.exp (budget f A B σ r))

theorem one_le_jensenM (r : ℝ) : 1 ≤ jensenM f A B σ r := le_max_left _ _

/-- Jensen's count of the closed half disc. -/
theorem finsum_divisor_le [hf : FosterClass f A B σ] {r : ℝ} (hr : 0 < r) :
    ((∑ᶠ u, MeromorphicOn.divisor f (closedBall (1 / 2 : ℂ) (r / 2)) u : ℤ) : ℝ) ≤
      Real.log (jensenM f A B σ r / ‖f (1 / 2 : ℂ)‖) / Real.log (3 / 2) := by
  have hr2 : (0 : ℝ) < |r / 2| := by rw [abs_of_pos (by positivity)]; positivity
  have hlt : |r / 2| < |3 * r / 4| := by
    rw [abs_of_pos (by positivity), abs_of_pos (by positivity)]
    linarith
  have han : AnalyticOnNhd ℂ f (closedBall (1 / 2 : ℂ) |3 * r / 4|) := fun z _ => hf.analyticAt z
  have hbound : ∀ z ∈ sphere (1 / 2 : ℂ) |3 * r / 4|, ‖f z‖ ≤ jensenM f A B σ r := by
    intro z hz
    have hzball : z ∈ ball (1 / 2 : ℂ) r := by
      rw [mem_sphere_iff_norm, abs_of_pos (by positivity)] at hz
      rw [mem_ball_iff_norm, hz]
      linarith
    exact (norm_le_of_growth (f := f) hr hzball).trans (le_max_right _ _)
  have h := AnalyticOnNhd.sum_divisor_le hr2 hlt (one_le_jensenM r) han hf.centre hbound
  rw [abs_of_pos (by positivity : (0 : ℝ) < r / 2)] at h
  have hratio : (3 * r / 4) / (r / 2) = 3 / 2 := by
    field_simp
    ring
  rw [hratio] at h
  exact h

/-! ## The paired finite Foster form with Landau's remainder -/

/-- Landau's remainder bound at radius `r`. -/
def landau (f : ℂ → ℂ) (A B σ r : ℝ) : ℝ :=
  16 * (budget f A B σ r +
    Real.log (jensenM f A B σ r / ‖f (1 / 2 : ℂ)‖) / Real.log (3 / 2) * Real.log 2) / r

/-- **FT0 for the class: the paired finite Foster form with Landau's remainder.** -/
theorem exists_paired_foster_form [hf : FosterClass f A B σ] {r : ℝ} (hr : 0 < r) :
    ∃ Z : SymmetricZeroFactorizationOf f r,
      (Z.count : ℝ) ≤ Real.log (jensenM f A B σ r / ‖f (1 / 2 : ℂ)‖) / Real.log (3 / 2) ∧
      ∀ z ∈ closedBall (1 / 2 : ℂ) (r / 8), f z ≠ 0 →
        ‖logDeriv f z -
            ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) *
              ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))‖ ≤ landau f A B σ r := by
  obtain ⟨Z, hcount⟩ := exists_symmetricZeroFactorizationOf_count (f := f) hr
  have hN : (Z.count : ℝ) ≤
      Real.log (jensenM f A B σ r / ‖f (1 / 2 : ℂ)‖) / Real.log (3 / 2) := by
    have h := finsum_divisor_le (f := f) hr
    rw [← hcount] at h
    exact_mod_cast h
  refine ⟨Z, hN, fun z hz hfz => ?_⟩
  have hL := Z.toZeroFactorization.norm_logDeriv_sub_flux_le hr (budget_pos r) hf.centre
    (fun w hw => norm_le_of_growth (f := f) hr hw) hz hfz
  have hzρ : ∀ ρ ∈ Z.zeros, z ≠ ρ := by
    intro ρ hρ h
    apply hfz
    rw [h]
    exact Z.f_eq_zero hr hρ
  have hpair := flux_eq_tankSum Z.refl_mem Z.refl_mult hzρ
  rw [← hpair]
  refine hL.trans ?_
  unfold landau
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_le_mul_of_nonneg_right hN hlog2
  linarith

end Soma.Holonics.RH.FosterClassLandau

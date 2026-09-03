import Mathlib
import ElementaryHolonics.RH.RiemannXi
import ElementaryHolonics.RH.ZeroComb
import ElementaryHolonics.RH.LandauLemma
import ElementaryHolonics.RH.ZeroFactorizationExists
import ElementaryHolonics.RH.LandauXi
import ElementaryHolonics.RH.JensenCountsTheComb
import ElementaryHolonics.RH.RiemannXiGrowth
import ElementaryHolonics.RH.XiCentre

/-!
# FT0: the zeros are Foster tanks, and the finite Foster form carries Landau's remainder

Hadamard's product for `Ξ(w) = ξ(½ + w)`, paired by the functional equation, reads
`Ξ′/Ξ(w) = Σ_pairs 2w/(w² − ρ′²)` with `ρ′ = ρ − ½`.  Each term is the impedance of a parallel LC
tank with capacitance `½` and inductance `−2/ρ′²`; under RH the inductance is `2/γ²` and the tank
resonates at `(LC)^{−1/2} = γ`.  RH is Foster's reactance theorem for this one function: every
tank has positive inductance.

This owner returns the finite face of that statement, exactly:

* the tank algebra — the pair identity `1/(z − ρ) + 1/(z − (1 − ρ)) = 2(z − ½)/((z − ½)² − (ρ − ½)²)`,
  the parallel-LC identity, and **positivity iff on the seam**: the inductance is a positive real
  iff `ρ′` is purely imaginary and nonzero;
* a **symmetric zero factorization** of `ξ` on a disc centred at `½`: the construction of
  `ZeroFactorizationExists`, carried out at the seam's centre, whose zero population is closed
  under the reflection `s ↦ 1 − s` with matched multiplicities, by the reflection symmetry of the
  divisor (`ZeroComb`);
* the **paired flux identity**: on a reflection-closed comb the Coulomb flux equals the tank sum;
* **the paired finite Foster form with Landau's remainder**: on the `r/8` disc about `½`,
  `‖ξ′/ξ(z) − Σ_ρ m_ρ (z − ½)/((z − ½)² − (ρ − ½)²)‖ ≤ 16 (M + N log 2)/r`, with Jensen's count of
  `N`, from the standing Landau owners.

One hypothesis is carried explicitly and not discharged here: `riemannXi (1/2) ≠ 0`, the value at
the centre (`ξ(½) ≈ 0.4971`, positive).  The standing Landau owners normalize at a nonvanishing
centre, Mathlib carries no value of `ζ` at `½`, and the disc must be centred at `½` for the
reflection to preserve it.  Its discharge by an enclosure of the theta tail is a named item of
`FT1`; nothing below assumes anything about the zeros.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterTanks

open Complex Metric Finset
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.LandauLemma
open Soma.Holonics.RH.ZeroFactorizationExists
open Soma.Holonics.RH.LandauXi
open Soma.Holonics.RH.JensenCountsTheComb
open Soma.Holonics.RH.RiemannXiGrowth

/-! ## The tank algebra -/

/-- The capacitance of every tank: the seam's half. -/
def capacitance : ℂ := 1 / 2

/-- The inductance of the tank of the centred zero `ρ′ = ρ − ½`. -/
def inductance (ρ' : ℂ) : ℂ := -2 / ρ' ^ 2

/-- The impedance of the tank of `ρ′` at the centred point `w`. -/
def tank (ρ' w : ℂ) : ℂ := 2 * w / (w ^ 2 - ρ' ^ 2)

/-- **The pair identity.**  The two members of a reflection pair sum to one tank. -/
theorem pair_eq_tank {z ρ : ℂ} (h₁ : z ≠ ρ) (h₂ : z ≠ 1 - ρ) :
    1 / (z - ρ) + 1 / (z - (1 - ρ)) = tank (ρ - 1 / 2) (z - 1 / 2) := by
  unfold tank
  have h₁' : z - ρ ≠ 0 := sub_ne_zero.mpr h₁
  have h₂' : z - (1 - ρ) ≠ 0 := sub_ne_zero.mpr h₂
  have hden : (z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2 = (z - ρ) * (z - (1 - ρ)) := by ring
  rw [hden]
  field_simp
  ring

/-- **The parallel-LC identity.**  The tank is the impedance `wL/(w²LC + 1)` of a parallel LC
circuit with the seam's capacitance and the zero's inductance. -/
theorem tank_eq_parallel_LC {ρ' w : ℂ} (hρ : ρ' ≠ 0) :
    tank ρ' w = w * inductance ρ' / (w ^ 2 * inductance ρ' * capacitance + 1) := by
  unfold tank inductance capacitance
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hsplit : w ^ 2 * (-2 / ρ' ^ 2) * (1 / 2) + 1 = (ρ' ^ 2 - w ^ 2) / ρ' ^ 2 := by
    field_simp
    all_goals ring
  rw [hsplit]
  by_cases hden : w ^ 2 - ρ' ^ 2 = 0
  · have hB : ρ' ^ 2 - w ^ 2 = 0 := by linear_combination -hden
    rw [hden, hB, div_zero, zero_div, div_zero]
  · have hB : ρ' ^ 2 - w ^ 2 ≠ 0 := by
      intro h
      apply hden
      linear_combination -h
    have hq : (ρ' ^ 2 - w ^ 2) / ρ' ^ 2 ≠ 0 := div_ne_zero hB h2
    rw [div_eq_div_iff hden hq]
    field_simp
    ring

/-- A complex number squares to a negative real iff it is purely imaginary and nonzero. -/
theorem sq_eq_neg_real_iff (w : ℂ) :
    (∃ c : ℝ, c < 0 ∧ w ^ 2 = (c : ℂ)) ↔ (w.re = 0 ∧ w ≠ 0) := by
  constructor
  · rintro ⟨c, hc, hw⟩
    have hre : (w ^ 2).re = c := by rw [hw]; simp
    have him : (w ^ 2).im = 0 := by rw [hw]; simp
    rw [sq, Complex.mul_re] at hre
    rw [sq, Complex.mul_im] at him
    have him' : 2 * w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.mp him' with h | h
    · have : w.re = 0 := by linarith
      refine ⟨this, ?_⟩
      intro h0
      rw [h0] at hre
      simp at hre
      linarith
    · exfalso
      rw [h] at hre
      nlinarith [sq_nonneg w.re]
  · rintro ⟨hre, hne⟩
    refine ⟨-(w.im ^ 2), ?_, ?_⟩
    · have : w.im ≠ 0 := by
        intro h
        apply hne
        exact Complex.ext hre h
      have := sq_pos_of_ne_zero this
      linarith
    · apply Complex.ext
      · simp [sq, Complex.mul_re, hre]
      · simp [sq, Complex.mul_im, hre]

/-- **Positivity iff on the seam.**  The inductance of the tank of `ρ′` is a positive real iff
`ρ′` is purely imaginary and nonzero, i.e. iff the zero `ρ = ½ + ρ′` lies on the critical line and
is not the centre. -/
theorem inductance_pos_real_iff (ρ' : ℂ) :
    (∃ L : ℝ, 0 < L ∧ inductance ρ' = (L : ℂ)) ↔ (ρ'.re = 0 ∧ ρ' ≠ 0) := by
  rw [← sq_eq_neg_real_iff]
  unfold inductance
  constructor
  · rintro ⟨L, hL, h⟩
    refine ⟨-2 / L, by
      have h2L : 0 < 2 / L := by positivity
      rw [neg_div]
      exact neg_neg_of_pos h2L, ?_⟩
    have hρ : ρ' ^ 2 ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      have : (L : ℂ) = 0 := h.symm
      have : L = 0 := by exact_mod_cast this
      linarith
    have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    have hρ0 : ρ' ≠ 0 := by
      intro h0
      apply hρ
      rw [h0]
      ring
    push_cast
    rw [eq_div_iff hL', ← h]
    field_simp
  · rintro ⟨c, hc, hw⟩
    refine ⟨-2 / c, by
      have hnc : 0 < -c := by linarith
      have h2c : 0 < 2 / -c := by positivity
      rw [div_neg] at h2c
      rw [neg_div]
      exact h2c, ?_⟩
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne
    rw [hw]
    push_cast
    ring

/-- **The resonance of a seam tank is the height.**  For a zero `½ + iγ`, the inductance is
`2/γ²` and `1/√(LC) = γ`. -/
theorem seam_tank_resonance {γ : ℝ} (hγ : 0 < γ) :
    inductance (I * γ) = ((2 / γ ^ 2 : ℝ) : ℂ) ∧
      1 / Real.sqrt ((2 / γ ^ 2) * (1 / 2)) = γ := by
  constructor
  · unfold inductance
    have : (I * (γ : ℂ)) ^ 2 = -((γ : ℂ) ^ 2) := by
      rw [mul_pow, I_sq]
      ring
    rw [this]
    push_cast
    have hγ' : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
    field_simp
  · have h : (2 / γ ^ 2) * (1 / 2) = (1 / γ) ^ 2 := by
      field_simp
    rw [h, Real.sqrt_sq (by positivity)]
    field_simp

/-! ## The paired flux on a reflection-closed comb -/

/-- **The paired flux identity.**  On a finite comb closed under `ρ ↦ 1 − ρ` with matched
multiplicities, the Coulomb flux is the tank sum. -/
theorem flux_eq_tankSum {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ ∈ Z, 1 - ρ ∈ Z) (hm : ∀ ρ ∈ Z, m (1 - ρ) = m ρ)
    {z : ℂ} (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ Z, (m ρ : ℂ) * ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2)) := by
  -- the reflected sum equals the sum
  have hrefl : ∑ ρ ∈ Z, (m ρ : ℂ) / (z - (1 - ρ)) = ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) := by
    refine Finset.sum_nbij' (fun ρ => 1 - ρ) (fun ρ => 1 - ρ) ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      exact hZ ρ hρ
    · intro ρ hρ
      exact hZ ρ hρ
    · intro ρ _
      ring
    · intro ρ _
      ring
    · intro ρ hρ
      rw [hm ρ hρ]
  -- average the two
  have hhalf : ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ Z, (m ρ : ℂ) * ((1 / (z - ρ) + 1 / (z - (1 - ρ))) / 2) := by
    have h := congrArg (fun s => (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) + s) / 2) hrefl
    rw [← Finset.sum_add_distrib] at h
    rw [Finset.sum_div] at h
    calc ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)
        = (∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) + ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)) / 2 := by ring
      _ = ∑ ρ ∈ Z, ((m ρ : ℂ) / (z - ρ) + (m ρ : ℂ) / (z - (1 - ρ))) / 2 := h.symm
      _ = _ := by
          apply Finset.sum_congr rfl
          intro ρ _
          ring
  rw [hhalf]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have h₁ : z ≠ ρ := hz ρ hρ
  have h₂ : z ≠ 1 - ρ := hz (1 - ρ) (hZ ρ hρ)
  have := pair_eq_tank h₁ h₂
  unfold tank at this
  rw [this]
  ring

/-! ## The symmetric zero factorization at the seam's centre -/

/-- A zero factorization of `ξ` on a disc centred at `½` whose comb is closed under the reflection
`ρ ↦ 1 − ρ` with matched multiplicities. -/
structure SymmetricZeroFactorization (r : ℝ) extends
    ZeroFactorization riemannXi (1 / 2 : ℂ) r where
  refl_mem : ∀ ρ ∈ zeros, 1 - ρ ∈ zeros
  refl_mult : ∀ ρ ∈ zeros, mult (1 - ρ) = mult ρ

theorem one_sub_mem_ball_half_iff {R : ℝ} (u : ℂ) :
    (1 - u) ∈ ball (1 / 2 : ℂ) R ↔ u ∈ ball (1 / 2 : ℂ) R := by
  simp only [Metric.mem_ball, Complex.dist_eq]
  have : (1 - u) - (1 / 2 : ℂ) = -(u - 1 / 2) := by ring
  rw [this, norm_neg]

/-- The xi divisor on an open disc centred at `½` is reflection symmetric. -/
theorem divisor_riemannXi_one_sub_ball {R : ℝ} (u : ℂ) :
    MeromorphicOn.divisor riemannXi (ball (1 / 2 : ℂ) R) (1 - u) =
      MeromorphicOn.divisor riemannXi (ball (1 / 2 : ℂ) R) u := by
  by_cases hu : u ∈ ball (1 / 2 : ℂ) R
  · have hu' : (1 - u) ∈ ball (1 / 2 : ℂ) R := (one_sub_mem_ball_half_iff u).mpr hu
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu',
      MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu,
      meromorphicOrderAt_riemannXi_one_sub]
  · have hu' : (1 - u) ∉ ball (1 / 2 : ℂ) R :=
      fun h ↦ hu ((one_sub_mem_ball_half_iff u).mp h)
    rw [MeromorphicOn.divisor_def, MeromorphicOn.divisor_def, if_neg (fun h ↦ hu' h.2),
      if_neg (fun h ↦ hu h.2)]

/-- **Existence of the symmetric factorization**, with its count equal to the divisor mass of
the closed half disc.  The construction is that of `ZeroFactorizationExists`, carried out at the
centre `½`, where the reflection preserves the disc and the divisor. -/
theorem exists_symmetricZeroFactorization_count {r : ℝ} (hr : 0 < r)
    (hξ : riemannXi (1 / 2 : ℂ) ≠ 0) :
    ∃ Z : SymmetricZeroFactorization r,
      (Z.count : ℤ) = ∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) (r / 2)) u := by
  classical
  have hf : Differentiable ℂ riemannXi := differentiable_riemannXi
  set z₀ : ℂ := 1 / 2 with hz₀
  set U : Set ℂ := ball z₀ r with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hmer : MeromorphicOn riemannXi U := fun u _ => (hf.analyticAt u).meromorphicAt
  have hord : ∀ u : U, meromorphicOrderAt riemannXi u ≠ ⊤ :=
    fun u => meromorphicOrderAt_ne_top hf hξ u
  set D := MeromorphicOn.divisor riemannXi U with hDdef
  have hfinC : (Function.support (MeromorphicOn.divisor riemannXi (closedBall z₀ r))).Finite :=
    (MeromorphicOn.divisor riemannXi (closedBall z₀ r)).finiteSupport (isCompact_closedBall _ _)
  have hDsub : Function.support D ⊆
      Function.support (MeromorphicOn.divisor riemannXi (closedBall z₀ r)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have huU : u ∈ U := (MeromorphicOn.divisor riemannXi U).supportWithinDomain hu
    have huC : u ∈ closedBall z₀ r := ball_subset_closedBall huU
    rw [hDdef, MeromorphicOn.divisor_apply hmer huU] at hu
    rw [MeromorphicOn.divisor_apply (fun v _ => (hf.analyticAt v).meromorphicAt) huC]
    exact hu
  have hfin : (Function.support D).Finite := hfinC.subset hDsub
  obtain ⟨g, hg, hg0, hcod⟩ := MeromorphicOn.extract_zeros_poles hmer hord hfin
  have han : AnalyticOnNhd ℂ riemannXi U := hf.differentiableOn.analyticOnNhd hUo
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
  have hpt : ∀ z ∈ U, riemannXi z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
    intro z hz
    have hφan : AnalyticAt ℂ (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z :=
      Function.FactorizedRational.analyticAt (hDnn z)
    have hcont : ContinuousAt ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) z :=
      hφan.continuousAt.smul (hg z hz).continuousAt
    have := eq_of_codiscreteWithin hUo hcod hz (hf.continuous.continuousAt) hcont
    rw [this, Pi.smul_apply', smul_eq_mul, hφeval]
  -- the reflection acts on the support and on the divisor
  have hDrefl : ∀ u, D (1 - u) = D u := fun u => by
    rw [hDdef, hUdef, hz₀]
    exact divisor_riemannXi_one_sub_ball u
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
            refl_mult := ?_ }, ?_⟩
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
  · set D' := MeromorphicOn.divisor riemannXi (closedBall z₀ (r / 2)) with hD'def
    have hmer' : MeromorphicOn riemannXi (closedBall z₀ (r / 2)) :=
      fun u _ => (hf.analyticAt u).meromorphicAt
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

/-- The zeros of a symmetric factorization are zeros of `ξ`. -/
theorem SymmetricZeroFactorization.riemannXi_eq_zero {r : ℝ} (hr : 0 < r)
    (Z : SymmetricZeroFactorization r) {ρ : ℂ} (hρ : ρ ∈ Z.zeros) : riemannXi ρ = 0 := by
  have hmem : ρ ∈ ball (1 / 2 : ℂ) r := by
    have := Z.zeros_mem ρ hρ
    exact closedBall_subset_ball (by linarith) this
  rw [Z.factor ρ hmem]
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero hρ
  rw [sub_self]
  exact zero_pow (Z.mult_pos ρ hρ).ne'

/-- **FT0: the paired finite Foster form with Landau's remainder.**  On a disc centred at `½`,
the log-derivative of `ξ` is the sum of the tanks of its zeros in the half disc, one tank per
reflection pair counted from both members, plus Landau's remainder, with Jensen's count of the
comb.  The hypothesis `hξ` is the value at the centre and is carried, not assumed about any zero. -/
theorem exists_paired_foster_form {r : ℝ} (hr : 0 < r) (hξ : riemannXi (1 / 2 : ℂ) ≠ 0) :
    ∃ (C : ℝ) (Z : SymmetricZeroFactorization r), 0 < C ∧
      (Z.count : ℝ) ≤ Real.log (jensenCeiling C (1 / 2) r / ‖riemannXi (1 / 2)‖) /
        Real.log (3 / 2) ∧
      ∀ z ∈ closedBall (1 / 2 : ℂ) (r / 8), riemannXi z ≠ 0 →
        ‖logDeriv riemannXi z -
            ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) *
              ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))‖ ≤
          16 * (xiBudget C (1 / 2) r +
            Real.log (jensenCeiling C (1 / 2) r / ‖riemannXi (1 / 2)‖) / Real.log (3 / 2) *
              Real.log 2) / r := by
  obtain ⟨C, hC, hgrowth⟩ := pointwiseAbscissaGrowthOfRiemannXiHolds
  obtain ⟨Z, hcount⟩ := exists_symmetricZeroFactorization_count hr hξ
  have hN : (Z.count : ℝ) ≤
      Real.log (jensenCeiling C (1 / 2) r / ‖riemannXi (1 / 2)‖) / Real.log (3 / 2) := by
    have h := finsum_divisor_le hC hgrowth hr hξ
    rw [← hcount] at h
    exact_mod_cast h
  refine ⟨C, Z, hC, hN, fun z hz hfz => ?_⟩
  have hL := Z.toZeroFactorization.norm_logDeriv_sub_flux_le hr (xiBudget_pos C (1 / 2) r) hξ
    (fun w hw => norm_riemannXi_le_of_growth hC hgrowth hr hξ hw) hz hfz
  have hzρ : ∀ ρ ∈ Z.zeros, z ≠ ρ := by
    intro ρ hρ h
    apply hfz
    rw [h]
    exact Z.riemannXi_eq_zero hr hρ
  have hpair := flux_eq_tankSum Z.refl_mem Z.refl_mult hzρ
  rw [← hpair]
  refine hL.trans ?_
  apply div_le_div_of_nonneg_right _ hr.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have := mul_le_mul_of_nonneg_right hN hlog2
  linarith

/-! ## FT1 (i): the carried hypothesis discharged -/

/-- **The symmetric factorization exists unconditionally**, the centre value being positive by
`XiCentre.riemannXi_one_half_ne_zero`. -/
theorem exists_symmetricZeroFactorization_count' {r : ℝ} (hr : 0 < r) :
    ∃ Z : SymmetricZeroFactorization r,
      (Z.count : ℤ) = ∑ᶠ u, MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) (r / 2)) u :=
  exists_symmetricZeroFactorization_count hr XiCentre.riemannXi_one_half_ne_zero

/-- **FT0 unconditionally: the paired finite Foster form with Landau's remainder.** -/
theorem exists_paired_foster_form' {r : ℝ} (hr : 0 < r) :
    ∃ (C : ℝ) (Z : SymmetricZeroFactorization r), 0 < C ∧
      (Z.count : ℝ) ≤ Real.log (jensenCeiling C (1 / 2) r / ‖riemannXi (1 / 2)‖) /
        Real.log (3 / 2) ∧
      ∀ z ∈ closedBall (1 / 2 : ℂ) (r / 8), riemannXi z ≠ 0 →
        ‖logDeriv riemannXi z -
            ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) *
              ((z - 1 / 2) / ((z - 1 / 2) ^ 2 - (ρ - 1 / 2) ^ 2))‖ ≤
          16 * (xiBudget C (1 / 2) r +
            Real.log (jensenCeiling C (1 / 2) r / ‖riemannXi (1 / 2)‖) / Real.log (3 / 2) *
              Real.log 2) / r :=
  exists_paired_foster_form hr XiCentre.riemannXi_one_half_ne_zero

end Soma.Holonics.RH.FosterTanks

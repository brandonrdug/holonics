import Mathlib
import HolonicsResearch.Zeta.RectangleCountStable
import HolonicsResearch.Zeta.XiStrip
import HolonicsResearch.Zeta.XiConjugation
import HolonicsResearch.Zeta.TrivialZeros
import HolonicsResearch.Zeta.WeightedArgumentPrinciple

/-!
# Carry and ticks: two receivers of one Aeon

The argument lift of `ξ` is an Aeon clock. Two receivers read it up to a height `T`:

- the **rectangle carry** `N(T)`: the multiplicity-weighted count of the zeros in the rectangle
  `[−1, 2] × [0, T]`, which the rectangle argument principle returns as the winding
  `(1/2πi) ∮ ξ′/ξ` when the top edge meets no zero (`carry_eq_argumentPrinciple`);
- the **section ticks** on the seam `Re s = ½`: each seam zero ticks with its order
  (`orderTicks`), or, if the receiver reads only sign changes of the real seam function, with the
  parity of its order (`parityTicks`).

`N(T)` splits exactly as order ticks plus the off-seam count, and the sign-change defect
`N(T) − parityTicks(T)` is the off-seam count plus the multiplicity defect
`Σ_seam (ord − ord mod 2)` (`defect_eq_offSeamCount_addMultiplicityDefect`). Hence:

- `RH ⟺ ∀ admissible T, N(T) = orderTicks(T)` (`riemannHypothesis_iff_carry_eq_orderTicks`);
- `RH ∧ simplicity ⟺ ∀ admissible T, N(T) = parityTicks(T)`
  (`riemannHypothesis_and_simple_iff_carry_eq_parityTicks`): a sign-change count needs
  simplicity besides RH.

The parity tick is the sign-change receiver itself: `ξ` is real on the seam
(`riemannXi_seamPoint_im`), and the real seam function `y ↦ ξ(½ + iy)` changes sign at a seam
zero exactly when its order is odd (`signChangeAt_iff_odd`), so each seam zero contributes to
`parityTicks` exactly when the seam function changes sign there
(`carryDivisor_emod_two_eq_signChange`).

[proved-derived; formal-checked] Every theorem is discharged with no `sorryAx`.
[open] No tube or neck owner bounds the carry–tick defect or proves it zero; the
Riemann–von Mangoldt `S(T)` is unbounded, so no fixed neck correction can.
-/

noncomputable section

namespace Holonics.Zeta.CarryTick

open Complex Set ComplexConjugate
open Holonics.Zeta.RiemannXi
open Holonics.Zeta.RectangleCauchy
open Holonics.Zeta.XiStrip

/-! ## The divisor of `ξ` on any set -/

theorem analyticAt_riemannXi (u : ℂ) : AnalyticAt ℂ riemannXi u :=
  analyticOn_riemannXi univ u (mem_univ u)

/-- The divisor of `ξ` on a set is nonzero exactly at its zeros in the set. -/
theorem divisor_ne_zero_iff (U : Set ℂ) (u : ℂ) :
    MeromorphicOn.divisor riemannXi U u ≠ 0 ↔ u ∈ U ∧ riemannXi u = 0 := by
  constructor
  · intro h
    refine ⟨(MeromorphicOn.divisor riemannXi U).supportWithinDomain (Function.mem_support.mpr h),
      ?_⟩
    by_contra hne
    apply h
    have hmem : u ∈ U :=
      (MeromorphicOn.divisor riemannXi U).supportWithinDomain (Function.mem_support.mpr h)
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem,
      (analyticAt_riemannXi u).meromorphicOrderAt_eq,
      ((analyticAt_riemannXi u).analyticOrderAt_eq_zero).2 hne]
    simp
  · rintro ⟨hmem, hzero⟩
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem]
    have han := analyticAt_riemannXi u
    have hne : analyticOrderAt riemannXi u ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han, hzero⟩
    have htop : meromorphicOrderAt riemannXi u ≠ ⊤ :=
      Holonics.Zeta.WeightedArgumentPrinciple.meromorphicOrderAt_riemannXi_ne_top u
    rw [han.meromorphicOrderAt_eq] at htop ⊢
    cases hn : analyticOrderAt riemannXi u with
    | top => exact absurd (by rw [hn]; rfl) htop
    | coe n =>
      rw [hn] at hne
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne rfl
      simp [hn0]

theorem divisor_nonneg (U : Set ℂ) (u : ℂ) : 0 ≤ MeromorphicOn.divisor riemannXi U u :=
  MeromorphicOn.AnalyticOnNhd.divisor_nonneg (analyticOn_riemannXi U) u

/-- On the set, the divisor value is `1` exactly when the analytic order is `1`. -/
theorem divisor_eq_one_iff {U : Set ℂ} {u : ℂ} (hu : u ∈ U) :
    MeromorphicOn.divisor riemannXi U u = 1 ↔ analyticOrderAt riemannXi u = 1 := by
  rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu,
    (analyticAt_riemannXi u).meromorphicOrderAt_eq]
  have htop : meromorphicOrderAt riemannXi u ≠ ⊤ :=
    Holonics.Zeta.WeightedArgumentPrinciple.meromorphicOrderAt_riemannXi_ne_top u
  rw [(analyticAt_riemannXi u).meromorphicOrderAt_eq] at htop
  cases hn : analyticOrderAt riemannXi u with
  | top => rw [hn] at htop; exact absurd rfl htop
  | coe n =>
    simp only [ENat.map_natCast]
    rw [WithTop.untop₀_coe]
    constructor
    · intro h
      have : (n : ℤ) = 1 := h
      rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl]
      exact congrArg _ (by exact_mod_cast this)
    · intro h
      have : n = 1 := by exact_mod_cast h
      rw [this]
      rfl

/-! ## The carry rectangle and its receivers -/

/-- The top corner of the carry rectangle `[−1, 2] × [0, T]`. -/
def carryTop (T : ℝ) : ℂ := 2 + T * I

/-- The closed carry rectangle. -/
abbrev carryRect (T : ℝ) : Set ℂ := closedRect (-1) (carryTop T)

/-- The divisor of `ξ` on the carry rectangle. -/
abbrev carryDivisor (T : ℝ) := MeromorphicOn.divisor riemannXi (carryRect T)

theorem isCompact_carryRect (T : ℝ) : IsCompact (carryRect T) :=
  isCompact_uIcc.reProdIm isCompact_uIcc

/-- The finite support of the carry divisor: the zeros of `ξ` in the rectangle. -/
def carrySupport (T : ℝ) : Finset ℂ := by
  classical
  exact ((carryDivisor T).finiteSupport (isCompact_carryRect T)).toFinset

theorem mem_carrySupport {T : ℝ} {u : ℂ} :
    u ∈ carrySupport T ↔ u ∈ carryRect T ∧ riemannXi u = 0 := by
  classical
  unfold carrySupport
  rw [Finite.mem_toFinset, Function.mem_support, divisor_ne_zero_iff]

/-- **The rectangle carry** `N(T)`: the multiplicity-weighted zero count. -/
def carry (T : ℝ) : ℤ := ∑ u ∈ carrySupport T, carryDivisor T u

/-- **Order ticks**: each seam zero ticks with its order. -/
def orderTicks (T : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (carrySupport T).filter (fun u => u.re = 1 / 2), carryDivisor T u

/-- **The off-seam count**, with multiplicity. -/
def offSeamCount (T : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (carrySupport T).filter (fun u => ¬ u.re = 1 / 2), carryDivisor T u

/-- **Parity ticks**: a sign-change receiver ticks once at a seam zero of odd order and not at
all at one of even order. -/
def parityTicks (T : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (carrySupport T).filter (fun u => u.re = 1 / 2), carryDivisor T u % 2

/-- **The multiplicity defect** of the parity receiver: `Σ_seam (ord − ord mod 2)`. -/
def multiplicityDefect (T : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (carrySupport T).filter (fun u => u.re = 1 / 2),
    (carryDivisor T u - carryDivisor T u % 2)

/-- **The carry is the order ticks plus the off-seam count.** -/
theorem carry_eq_orderTicks_add_offSeamCount (T : ℝ) :
    carry T = orderTicks T + offSeamCount T := by
  classical
  unfold carry orderTicks offSeamCount
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **The carry–tick defect of the sign-change receiver** [proved-derived; formal-checked]:
`N(T) − parityTicks(T) = offSeamCount(T) + multiplicityDefect(T)`. -/
theorem defect_eq_offSeamCount_addMultiplicityDefect (T : ℝ) :
    carry T - parityTicks T = offSeamCount T + multiplicityDefect T := by
  classical
  rw [carry_eq_orderTicks_add_offSeamCount]
  unfold orderTicks parityTicks multiplicityDefect
  rw [Finset.sum_sub_distrib]
  ring

theorem offSeamCount_nonneg (T : ℝ) : 0 ≤ offSeamCount T := by
  classical
  unfold offSeamCount
  exact Finset.sum_nonneg fun u _ => divisor_nonneg _ u

theorem multiplicityDefect_nonneg (T : ℝ) : 0 ≤ multiplicityDefect T := by
  classical
  unfold multiplicityDefect
  refine Finset.sum_nonneg fun u _ => ?_
  have h0 : 0 ≤ carryDivisor T u := divisor_nonneg (carryRect T) u
  have : carryDivisor T u % 2 ≤ carryDivisor T u := by omega
  linarith

/-- **The off-seam count vanishes iff every zero in the rectangle is on the seam.** -/
theorem offSeamCount_eq_zero_iff (T : ℝ) :
    offSeamCount T = 0 ↔ ∀ u ∈ carryRect T, riemannXi u = 0 → u.re = 1 / 2 := by
  classical
  unfold offSeamCount
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => divisor_nonneg _ u)]
  constructor
  · intro h u hu hz
    by_contra hre
    have hmem : u ∈ (carrySupport T).filter (fun u => ¬ u.re = 1 / 2) :=
      Finset.mem_filter.mpr ⟨mem_carrySupport.mpr ⟨hu, hz⟩, hre⟩
    exact (divisor_ne_zero_iff _ u).mpr ⟨hu, hz⟩ (h u hmem)
  · intro h u hu
    rw [Finset.mem_filter, mem_carrySupport] at hu
    exact absurd (h u hu.1.1 hu.1.2) hu.2

/-- **The multiplicity defect vanishes iff every seam zero in the rectangle is simple.** -/
theorem multiplicityDefect_eq_zero_iff (T : ℝ) :
    multiplicityDefect T = 0 ↔
      ∀ u ∈ carryRect T, riemannXi u = 0 → u.re = 1 / 2 → analyticOrderAt riemannXi u = 1 := by
  classical
  unfold multiplicityDefect
  have hnn : ∀ u ∈ (carrySupport T).filter (fun u => u.re = 1 / 2),
      0 ≤ carryDivisor T u - carryDivisor T u % 2 := by
    intro u _
    have h0 : 0 ≤ carryDivisor T u := divisor_nonneg (carryRect T) u
    have : carryDivisor T u % 2 ≤ carryDivisor T u := by omega
    linarith
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h u hu hz hre
    have hmem : u ∈ (carrySupport T).filter (fun u => u.re = 1 / 2) :=
      Finset.mem_filter.mpr ⟨mem_carrySupport.mpr ⟨hu, hz⟩, hre⟩
    have hk := h u hmem
    have hpos : carryDivisor T u ≠ 0 := (divisor_ne_zero_iff _ u).mpr ⟨hu, hz⟩
    have h0 : 0 ≤ carryDivisor T u := divisor_nonneg (carryRect T) u
    have h1 : carryDivisor T u = 1 := by omega
    exact (divisor_eq_one_iff hu).mp h1
  · intro h u hu
    rw [Finset.mem_filter, mem_carrySupport] at hu
    have h1 := (divisor_eq_one_iff hu.1.1).mpr (h u hu.1.1 hu.1.2 hu.2)
    show carryDivisor T u - carryDivisor T u % 2 = 0
    rw [h1]
    rfl

/-! ## The parity tick is a sign change of the seam function -/

/-- The seam point at ordinate `y`. -/
def seamPoint (y : ℝ) : ℂ := 1 / 2 + y * I

/-- **`ξ` is real on the seam**: conjugation and the reflection `s ↦ 1 − s` agree there. -/
theorem riemannXi_seamPoint_im (y : ℝ) : (riemannXi (seamPoint y)).im = 0 := by
  have hc : conj (seamPoint y) = 1 - seamPoint y := by
    unfold seamPoint
    apply Complex.ext <;> simp
    norm_num
  have h : conj (riemannXi (seamPoint y)) = riemannXi (seamPoint y) := by
    rw [← Holonics.Zeta.XiConjugation.riemannXi_conj, hc, riemannXi_one_sub]
  exact Complex.conj_eq_iff_im.mp h

/-- The real seam function `y ↦ ξ(½ + iy)` (Hardy's `Z` up to its unimodular phase and the
positive archimedean factor). -/
def seamXi (y : ℝ) : ℝ := (riemannXi (seamPoint y)).re

/-- **A sign change of a real function at `γ`**: opposite signs on the two sides, near `γ`. -/
def SignChangeAt (f : ℝ → ℝ) (γ : ℝ) : Prop :=
  ∃ ε > 0, ∀ y₁ ∈ Ioo (γ - ε) γ, ∀ y₂ ∈ Ioo γ (γ + ε), f y₁ * f y₂ < 0

/-- Near a seam zero of order `k`, the seam function is `(y − γ)^k` times a real function of
constant nonzero sign. -/
theorem seamXi_local_form {γ : ℝ} {k : ℕ} (hk : analyticOrderAt riemannXi (seamPoint γ) = k) :
    ∃ q : ℝ → ℝ, ∃ ε > 0, ∃ c : ℝ, c ≠ 0 ∧ ∀ y, dist y γ < ε →
      seamXi y = (y - γ) ^ k * q y ∧ 0 < c * q y := by
  obtain ⟨g, hg, hg0, hfac⟩ := (analyticAt_riemannXi _).analyticOrderAt_eq_natCast.mp hk
  set Q : ℝ → ℂ := fun y => I ^ k * g (seamPoint y) with hQ
  have hφ : Continuous seamPoint := by unfold seamPoint; fun_prop
  have hQc : ContinuousAt Q γ :=
    continuousAt_const.mul (hg.continuousAt.comp hφ.continuousAt)
  have hfac' : ∀ᶠ y in nhds γ, riemannXi (seamPoint y) = ((y - γ : ℝ) : ℂ) ^ k * Q y := by
    have := hφ.continuousAt.tendsto.eventually hfac
    filter_upwards [this] with y hy
    rw [hy, smul_eq_mul, hQ]
    have : seamPoint y - seamPoint γ = I * ((y - γ : ℝ) : ℂ) := by
      unfold seamPoint; push_cast; ring
    rw [this, mul_pow]
    ring
  -- Q is real off `γ`, hence at `γ`
  have hQim : (Q γ).im = 0 := by
    have hev : ∀ᶠ y in nhdsWithin γ {γ}ᶜ, (Q y).im = 0 := by
      filter_upwards [nhdsWithin_le_nhds hfac', self_mem_nhdsWithin] with y hy hne
      have hne' : ((y - γ : ℝ) : ℂ) ^ k ≠ 0 := by
        apply pow_ne_zero
        exact_mod_cast sub_ne_zero.mpr hne
      have hreal := riemannXi_seamPoint_im y
      rw [hy] at hreal
      have hr : (((y - γ : ℝ) : ℂ) ^ k).im = 0 := by
        rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
      have hre : (((y - γ : ℝ) : ℂ) ^ k).re ≠ 0 := by
        intro h0
        apply hne'
        exact Complex.ext h0 hr
      rw [Complex.mul_im, hr, zero_mul, add_zero] at hreal
      exact (mul_eq_zero.mp hreal).resolve_left hre
    have hlim : Filter.Tendsto (fun y => (Q y).im) (nhdsWithin γ {γ}ᶜ) (nhds (Q γ).im) :=
      (Complex.continuous_im.continuousAt.tendsto.comp hQc.tendsto).mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  have hQ0 : Q γ ≠ 0 := by
    rw [hQ]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) hg0
  set c := (Q γ).re with hc
  have hc0 : c ≠ 0 := by
    intro h
    exact hQ0 (Complex.ext h hQim)
  have hsign : ∀ᶠ y in nhds γ, 0 < c * (Q y).re := by
    have hcont : ContinuousAt (fun y => c * (Q y).re) γ :=
      continuousAt_const.mul (Complex.continuous_re.continuousAt.comp hQc)
    have hpos : 0 < c * (Q γ).re := by rw [← hc]; exact mul_self_pos.mpr hc0
    exact hcont.eventually (lt_mem_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hfac'.and hsign)
  refine ⟨fun y => (Q y).re, ε, hε, c, hc0, fun y hy => ⟨?_, (hball hy).2⟩⟩
  have h := (hball hy).1
  unfold seamXi
  rw [h, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

/-- **The parity tick is the sign change** [proved-derived; formal-checked]: the real seam
function changes sign at a seam zero exactly when its order is odd. -/
theorem signChangeAt_iff_odd {γ : ℝ} {k : ℕ}
    (hk : analyticOrderAt riemannXi (seamPoint γ) = k) : SignChangeAt seamXi γ ↔ Odd k := by
  obtain ⟨q, ε, hε, c, hc0, hloc⟩ := seamXi_local_form hk
  have hprod : ∀ y₁ ∈ Ioo (γ - ε) γ, ∀ y₂ ∈ Ioo γ (γ + ε),
      seamXi y₁ * seamXi y₂ = ((y₁ - γ) * (y₂ - γ)) ^ k * (q y₁ * q y₂) ∧ 0 < q y₁ * q y₂ := by
    intro y₁ h₁ y₂ h₂
    have hd₁ : dist y₁ γ < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [h₁.1, h₁.2]
    have hd₂ : dist y₂ γ < ε := by
      rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [h₂.1, h₂.2]
    obtain ⟨e₁, p₁⟩ := hloc y₁ hd₁
    obtain ⟨e₂, p₂⟩ := hloc y₂ hd₂
    refine ⟨by rw [e₁, e₂, mul_pow]; ring, ?_⟩
    have : 0 < (c * q y₁) * (c * q y₂) := mul_pos p₁ p₂
    have hcc : 0 < c * c := mul_self_pos.mpr hc0
    nlinarith
  have hneg : ∀ y₁ ∈ Ioo (γ - ε) γ, ∀ y₂ ∈ Ioo γ (γ + ε), (y₁ - γ) * (y₂ - γ) < 0 := by
    intro y₁ h₁ y₂ h₂
    exact mul_neg_of_neg_of_pos (by linarith [h₁.2]) (by linarith [h₂.1])
  constructor
  · intro ⟨ε', hε', hch⟩
    by_contra hodd
    have heven : Even k := Nat.not_odd_iff_even.mp hodd
    set δ := min ε ε' / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hδε : δ < ε := by rw [hδ]; linarith [min_le_left ε ε']
    have hδε' : δ < ε' := by rw [hδ]; linarith [min_le_right ε ε']
    have m₁ : γ - δ ∈ Ioo (γ - ε) γ := ⟨by linarith, by linarith⟩
    have m₂ : γ + δ ∈ Ioo γ (γ + ε) := ⟨by linarith, by linarith⟩
    have m₁' : γ - δ ∈ Ioo (γ - ε') γ := ⟨by linarith, by linarith⟩
    have m₂' : γ + δ ∈ Ioo γ (γ + ε') := ⟨by linarith, by linarith⟩
    obtain ⟨he, hp⟩ := hprod _ m₁ _ m₂
    have hpow : 0 < ((γ - δ - γ) * (γ + δ - γ)) ^ k :=
      heven.pow_pos (ne_of_lt (hneg _ m₁ _ m₂))
    have := hch _ m₁' _ m₂'
    rw [he] at this
    nlinarith [mul_pos hpow hp]
  · intro hodd
    refine ⟨ε, hε, fun y₁ h₁ y₂ h₂ => ?_⟩
    obtain ⟨he, hp⟩ := hprod y₁ h₁ y₂ h₂
    rw [he]
    exact mul_neg_of_neg_of_pos (hodd.pow_neg (hneg y₁ h₁ y₂ h₂)) hp

open scoped Classical in
/-- **The parity ticks count the sign changes** [proved-derived; formal-checked]: each seam zero
in the rectangle contributes `1` to `parityTicks` exactly when the seam function changes sign
there. -/
theorem carryDivisor_emod_two_eq_signChange {T : ℝ} {u : ℂ} (hu : u ∈ carryRect T)
    (hre : u.re = 1 / 2) :
    carryDivisor T u % 2 = if SignChangeAt seamXi u.im then 1 else 0 := by
  have hpt : u = seamPoint u.im := by
    unfold seamPoint
    apply Complex.ext <;> simp [hre]
  have htop : meromorphicOrderAt riemannXi u ≠ ⊤ :=
    Holonics.Zeta.WeightedArgumentPrinciple.meromorphicOrderAt_riemannXi_ne_top u
  rw [(analyticAt_riemannXi u).meromorphicOrderAt_eq] at htop
  unfold carryDivisor
  rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hu,
    (analyticAt_riemannXi u).meromorphicOrderAt_eq]
  cases hn : analyticOrderAt riemannXi u with
  | top => rw [hn] at htop; exact absurd rfl htop
  | coe k =>
    have hk : analyticOrderAt riemannXi (seamPoint u.im) = k := by rw [← hpt]; exact hn
    simp only [ENat.map_natCast]
    rw [WithTop.untop₀_coe]
    by_cases hodd : Odd k
    · rw [if_pos ((signChangeAt_iff_odd hk).mpr hodd)]
      obtain ⟨j, rfl⟩ := hodd
      push_cast
      omega
    · rw [if_neg (fun h => hodd ((signChangeAt_iff_odd hk).mp h))]
      obtain ⟨j, rfl⟩ := Nat.not_odd_iff_even.mp hodd
      push_cast
      omega

/-! ## The argument principle reads the carry -/

/-- **An admissible height**: positive, with no zero of `ξ` on the top edge. -/
def AdmissibleHeight (T : ℝ) : Prop :=
  0 < T ∧ ∀ x : ℝ, -1 ≤ x → x ≤ 2 → riemannXi (x + T * I) ≠ 0

theorem mem_carryRect_iff {T : ℝ} (hT : 0 ≤ T) {u : ℂ} :
    u ∈ carryRect T ↔ (-1 ≤ u.re ∧ u.re ≤ 2) ∧ (0 ≤ u.im ∧ u.im ≤ T) := by
  unfold carryRect closedRect carryTop
  rw [mem_reProdIm]
  have h1 : ((-1 : ℂ)).re = -1 := by simp
  have h2 : ((2 : ℂ) + (T : ℂ) * I).re = 2 := by simp
  have h3 : ((-1 : ℂ)).im = 0 := by simp
  have h4 : ((2 : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [h1, h2, h3, h4, uIcc_of_le (by norm_num), uIcc_of_le hT]
  simp [mem_Icc]

/-- On an admissible height, `ξ` has no zero on the boundary of the carry rectangle: the
vertical edges lie outside the strip, the bottom edge is real, and the top edge is admissible. -/
theorem boundary_ne_zero {T : ℝ} (hT : AdmissibleHeight T) :
    ∀ ζ ∈ boundaryRect (-1) (carryTop T), riemannXi ζ ≠ 0 := by
  intro ζ hζ hz
  obtain ⟨hcl, hop⟩ := hζ
  have hT0 := hT.1.le
  rw [mem_carryRect_iff hT0] at hcl
  have hstrip := re_mem_Ioo_of_riemannXi_eq_zero hz
  have him := im_ne_zero_of_riemannXi_eq_zero hz
  apply hop
  unfold openRect carryTop
  rw [mem_reProdIm]
  simp only [neg_re, one_re, add_re, re_ofNat, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_im, one_im, neg_zero, add_im, im_ofNat, mul_im,
    zero_add]
  refine ⟨⟨by rw [min_eq_left (by norm_num)]; linarith, by rw [max_eq_right (by norm_num)]; linarith⟩,
    ⟨by rw [min_eq_left hT0]; exact lt_of_le_of_ne hcl.2.1 (Ne.symm him), ?_⟩⟩
  rw [max_eq_right hT0]
  refine lt_of_le_of_ne hcl.2.2 ?_
  intro heq
  apply hT.2 ζ.re (by linarith) (by linarith)
  rw [← heq, re_add_im]
  exact hz

/-- **The argument principle reads the carry** [proved-derived; formal-checked]: on an
admissible height, `∮ ξ′/ξ` around the carry rectangle is `2πi N(T)`. -/
theorem carry_eq_argumentPrinciple {T : ℝ} (hT : AdmissibleHeight T) :
    rectIntegral (logDeriv riemannXi) (-1) (carryTop T) = 2 * Real.pi * I * carry T := by
  classical
  have hzw : (-1 : ℂ).re < (carryTop T).re ∧ (-1 : ℂ).im < (carryTop T).im := by
    unfold carryTop
    simp [hT.1]
    norm_num
  obtain ⟨n, hn, hdiv⟩ := Holonics.Zeta.RectangleCountStable.exists_count differentiable_riemannXi
    hzw (boundary_ne_zero hT)
  rw [hn]
  congr 1
  rw [← hdiv]
  -- the open and closed divisors agree pointwise
  have hpt : ∀ u, (MeromorphicOn.divisor riemannXi (openRect (-1) (carryTop T)) u : ℂ) =
      (carryDivisor T u : ℂ) := by
    intro u
    by_cases ho : u ∈ openRect (-1) (carryTop T)
    · have hc : u ∈ carryRect T := openRect_subset_closedRect _ _ ho
      rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) ho,
        MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hc]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ ho]
      by_cases hc : u ∈ carryRect T
      · have hz : riemannXi u ≠ 0 := boundary_ne_zero hT u ⟨hc, ho⟩
        have : carryDivisor T u = 0 := by
          by_contra h
          exact hz ((divisor_ne_zero_iff _ u).mp h).2
        rw [this]
      · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hc]
  rw [finsum_congr hpt, finsum_eq_sum_of_support_subset (s := carrySupport T)]
  · unfold carry
    push_cast
    rfl
  · intro u hu
    rw [Function.mem_support] at hu
    rw [Finset.mem_coe]
    unfold carrySupport
    rw [Finite.mem_toFinset, Function.mem_support]
    exact_mod_cast hu

/-- **Admissible heights exist above every height**: the zeros of `ξ` in a compact rectangle are
finitely many, so their ordinates miss all but finitely many heights. -/
theorem exists_admissibleHeight_gt (T₀ : ℝ) : ∃ T, T₀ < T ∧ AdmissibleHeight T := by
  classical
  set T₁ : ℝ := max T₀ 0 + 1 with hT₁
  have hT₁pos : 0 < T₁ := by positivity
  have hT₁0 : 0 ≤ T₁ + 1 := by linarith
  set B : Finset ℝ := (carrySupport (T₁ + 1)).image Complex.im with hB
  have hinf : (Ioo T₁ (T₁ + 1)).Infinite := Ioo_infinite (by linarith)
  obtain ⟨T, hTmem, hTB⟩ := (hinf.sdiff B.finite_toSet).nonempty
  refine ⟨T, by
    have := hTmem.1
    have : T₀ ≤ max T₀ 0 := le_max_left _ _
    linarith, ?_, ?_⟩
  · linarith [hTmem.1]
  · intro x hx1 hx2 hz
    apply hTB
    rw [Finset.mem_coe, hB, Finset.mem_image]
    refine ⟨x + T * I, mem_carrySupport.mpr ⟨?_, hz⟩, by simp⟩
    rw [mem_carryRect_iff hT₁0]
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add]
    exact ⟨⟨hx1, hx2⟩, ⟨by linarith [hTmem.1], hTmem.2.le⟩⟩

/-- An upper zero of `ξ` lies in every carry rectangle above its height. -/
theorem mem_carryRect_of_zero {ρ : ℂ} (hρ : riemannXi ρ = 0) {T : ℝ} (hpos : 0 < ρ.im)
    (hT : ρ.im < T) : ρ ∈ carryRect T := by
  have hstrip := re_mem_Ioo_of_riemannXi_eq_zero hρ
  rw [mem_carryRect_iff (by linarith)]
  exact ⟨⟨by linarith, by linarith⟩, ⟨hpos.le, hT.le⟩⟩

/-- Every zero of `ξ` has an upper zero with the same real part: itself or its conjugate. -/
theorem exists_upper_zero {ρ : ℂ} (hρ : riemannXi ρ = 0) :
    ∃ ρ' : ℂ, riemannXi ρ' = 0 ∧ 0 < ρ'.im ∧ ρ'.re = ρ.re := by
  have him := im_ne_zero_of_riemannXi_eq_zero hρ
  rcases lt_or_gt_of_ne him with hneg | hpos
  · refine ⟨conj ρ, ?_, by simp; linarith, by simp⟩
    rw [Holonics.Zeta.XiConjugation.riemannXi_conj, hρ, map_zero]
  · exact ⟨ρ, hρ, hpos, rfl⟩

/-! ## The two receivers and the Riemann hypothesis -/

/-- **RH is the equality of the carry with the order ticks** [proved-derived; formal-checked]:
`RH ⟺ ∀ admissible T, N(T) = Σ_(seam zeros ≤ T) order`. -/
theorem riemannHypothesis_iff_carry_eq_orderTicks :
    RiemannHypothesis ↔ ∀ T, AdmissibleHeight T → carry T = orderTicks T := by
  rw [Holonics.Zeta.TrivialZeros.riemannHypothesis_iff_xi]
  constructor
  · intro hRH T _
    rw [carry_eq_orderTicks_add_offSeamCount, (offSeamCount_eq_zero_iff T).mpr
      (fun u _ hz => hRH u hz), add_zero]
  · intro h ρ hρ
    obtain ⟨ρ', hρ', hpos, hre⟩ := exists_upper_zero hρ
    obtain ⟨T, hT, hadm⟩ := exists_admissibleHeight_gt ρ'.im
    have hoff : offSeamCount T = 0 := by
      have := carry_eq_orderTicks_add_offSeamCount T
      rw [h T hadm] at this
      linarith
    rw [← hre]
    exact (offSeamCount_eq_zero_iff T).mp hoff ρ' (mem_carryRect_of_zero hρ' hpos hT) hρ'

/-- **A sign-change receiver needs simplicity besides RH** [proved-derived; formal-checked]:
`N(T) = parityTicks(T)` for every admissible `T` iff RH holds and every upper zero is simple. -/
theorem riemannHypothesis_and_simple_iff_carry_eq_parityTicks :
    (RiemannHypothesis ∧ ∀ ρ, riemannXi ρ = 0 → 0 < ρ.im → analyticOrderAt riemannXi ρ = 1) ↔
      ∀ T, AdmissibleHeight T → carry T = parityTicks T := by
  constructor
  · rintro ⟨hRH, hsimple⟩ T hT
    rw [Holonics.Zeta.TrivialZeros.riemannHypothesis_iff_xi] at hRH
    have h1 : offSeamCount T = 0 := (offSeamCount_eq_zero_iff T).mpr (fun u _ hz => hRH u hz)
    have h2 : multiplicityDefect T = 0 := by
      rw [multiplicityDefect_eq_zero_iff]
      intro u hu hz _
      apply hsimple u hz
      have him := im_ne_zero_of_riemannXi_eq_zero hz
      rw [mem_carryRect_iff hT.1.le] at hu
      exact lt_of_le_of_ne hu.2.1 (Ne.symm him)
    have := defect_eq_offSeamCount_addMultiplicityDefect T
    rw [h1, h2] at this
    linarith
  · intro h
    have hboth : ∀ T, AdmissibleHeight T → offSeamCount T = 0 ∧ multiplicityDefect T = 0 := by
      intro T hT
      have := defect_eq_offSeamCount_addMultiplicityDefect T
      rw [h T hT, sub_self] at this
      have h1 := offSeamCount_nonneg T
      have h2 := multiplicityDefect_nonneg T
      constructor <;> linarith
    refine ⟨?_, ?_⟩
    · rw [riemannHypothesis_iff_carry_eq_orderTicks]
      intro T hT
      rw [carry_eq_orderTicks_add_offSeamCount, (hboth T hT).1, add_zero]
    · intro ρ hρ hpos
      obtain ⟨T, hT, hadm⟩ := exists_admissibleHeight_gt ρ.im
      have hmem := mem_carryRect_of_zero hρ hpos hT
      have hre : ρ.re = 1 / 2 := by
        exact (offSeamCount_eq_zero_iff T).mp (hboth T hadm).1 ρ hmem hρ
      exact (multiplicityDefect_eq_zero_iff T).mp (hboth T hadm).2 ρ hmem hρ hre

end Holonics.Zeta.CarryTick

#print axioms Holonics.Zeta.CarryTick.defect_eq_offSeamCount_addMultiplicityDefect
#print axioms Holonics.Zeta.CarryTick.signChangeAt_iff_odd
#print axioms Holonics.Zeta.CarryTick.carryDivisor_emod_two_eq_signChange
#print axioms Holonics.Zeta.CarryTick.carry_eq_argumentPrinciple
#print axioms Holonics.Zeta.CarryTick.riemannHypothesis_iff_carry_eq_orderTicks
#print axioms Holonics.Zeta.CarryTick.riemannHypothesis_and_simple_iff_carry_eq_parityTicks

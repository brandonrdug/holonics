import ElementaryHolonics.RH.XiConjugation
import ElementaryHolonics.RH.WeightedArgumentPrinciple

/-!
# Four-orbit counting: the off-line zeros of `ξ` in a centred disc come in multiples of four

A finite set of points closed under the reflection `s ↦ 1 − s` and under conjugation, none on the
critical line and none on the real axis, splits into the left and right halves exchanged by the
reflection and, within a half, into the upper and lower parts exchanged by conjugation; so its
cardinality is a multiple of four.  The zeros of `ξ` off the line and off the real axis in any
disc centred at `½` form such a set.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroOrbitCount

open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiConjugation
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.WeilPositivity (riemannXi_eq_zero_of_divisor_ne_zero)
open Soma.Holonics.RH.WeightedArgumentPrinciple (meromorphicOrderAt_riemannXi_ne_top)
open Complex Metric
open scoped ComplexConjugate

/-- **Four-orbit counting.** -/
theorem card_mod_four_eq_zero (S : Finset ℂ) (hσ : ∀ s ∈ S, 1 - s ∈ S) (hτ : ∀ s ∈ S, conj s ∈ S)
    (hre : ∀ s ∈ S, s.re ≠ 1 / 2) (him : ∀ s ∈ S, s.im ≠ 0) : S.card % 4 = 0 := by
  classical
  set L := S.filter (fun s => s.re < 1 / 2) with hL
  set R := S.filter (fun s => ¬ s.re < 1 / 2) with hR
  have hcard : L.card + R.card = S.card := Finset.card_filter_add_card_filter_not _
  have hLR : R = L.image (fun s => 1 - s) := by
    ext s
    simp only [hR, hL, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hs, hnot⟩
      have h' : 1 / 2 < s.re := lt_of_le_of_ne (not_lt.mp hnot) (Ne.symm (hre s hs))
      refine ⟨1 - s, ⟨hσ s hs, ?_⟩, by ring⟩
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    · rintro ⟨t, ⟨ht, hlt⟩, rfl⟩
      refine ⟨hσ t ht, ?_⟩
      simp only [Complex.sub_re, Complex.one_re, not_lt]
      linarith
  have hinj : Function.Injective (fun s : ℂ => 1 - s) := fun a b h => by
    simpa using h
  have hRcard : R.card = L.card := by
    rw [hLR, Finset.card_image_of_injective _ hinj]
  set U := L.filter (fun s => 0 < s.im) with hU
  set D := L.filter (fun s => ¬ 0 < s.im) with hD
  have hcard2 : U.card + D.card = L.card := Finset.card_filter_add_card_filter_not _
  have hUD : D = U.image (fun s => conj s) := by
    ext s
    simp only [hD, hU, hL, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨hs, hlt⟩, hnot⟩
      have h' : s.im < 0 := lt_of_le_of_ne (not_lt.mp hnot) (him s hs)
      refine ⟨conj s, ⟨⟨hτ s hs, by simpa using hlt⟩, ?_⟩, Complex.conj_conj s⟩
      simp only [Complex.conj_im]
      linarith
    · rintro ⟨t, ⟨⟨ht, hlt⟩, hpos⟩, rfl⟩
      refine ⟨⟨hτ t ht, by simpa using hlt⟩, ?_⟩
      simp only [Complex.conj_im, not_lt]
      linarith
  have hinjc : Function.Injective (fun s : ℂ => conj s) := (starRingEnd ℂ).injective
  have hDcard : D.card = U.card := by
    rw [hUD, Finset.card_image_of_injective _ hinjc]
  omega

/-- Inside a centred disc the divisor of `ξ` is nonzero exactly at the zeros of `ξ`. -/
theorem divisor_ne_zero_iff (R : ℝ) (u : ℂ) :
    MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|) u ≠ 0 ↔
      u ∈ closedBall (1 / 2 : ℂ) |R| ∧ riemannXi u = 0 := by
  constructor
  · intro h
    exact ⟨(MeromorphicOn.divisor riemannXi _).supportWithinDomain (Function.mem_support.mpr h),
      riemannXi_eq_zero_of_divisor_ne_zero h⟩
  · rintro ⟨hmem, hzero⟩
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem]
    have han : AnalyticAt ℂ riemannXi u := analyticOn_riemannXi Set.univ u (Set.mem_univ u)
    have hne : analyticOrderAt riemannXi u ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han, hzero⟩
    have htop : meromorphicOrderAt riemannXi u ≠ ⊤ := meromorphicOrderAt_riemannXi_ne_top u
    rw [han.meromorphicOrderAt_eq] at htop ⊢
    cases hn : analyticOrderAt riemannXi u with
    | top => exact absurd (by rw [hn]; rfl) htop
    | coe n =>
      rw [hn] at hne
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne rfl
      simp [hn0]

/-- The zeros of `ξ` off the line and off the real axis in the centred disc of radius `|R|`. -/
def offLineZeros (R : ℝ) : Finset ℂ := by
  classical
  exact ((MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|)).finiteSupport
    (isCompact_closedBall _ _)).toFinset.filter (fun u => u.re ≠ 1 / 2 ∧ u.im ≠ 0)

theorem mem_offLineZeros {R : ℝ} {u : ℂ} :
    u ∈ offLineZeros R ↔
      (u ∈ closedBall (1 / 2 : ℂ) |R| ∧ riemannXi u = 0) ∧ u.re ≠ 1 / 2 ∧ u.im ≠ 0 := by
  classical
  unfold offLineZeros
  rw [Finset.mem_filter, Set.Finite.mem_toFinset, Function.mem_support, divisor_ne_zero_iff]

theorem conj_mem_closedBall_half_iff {R : ℝ} (u : ℂ) :
    conj u ∈ closedBall (1 / 2 : ℂ) R ↔ u ∈ closedBall (1 / 2 : ℂ) R := by
  simp only [Metric.mem_closedBall, Complex.dist_eq]
  have h : conj u - (1 / 2 : ℂ) = conj (u - 1 / 2) := by
    rw [map_sub, map_div₀, map_one, map_ofNat]
  rw [h, Complex.norm_conj]

/-- **The off-line zeros of `ξ` in a centred disc come in multiples of four.** -/
theorem card_offLineZeros_mod_four (R : ℝ) : (offLineZeros R).card % 4 = 0 := by
  apply card_mod_four_eq_zero
  · intro s hs
    rw [mem_offLineZeros] at hs ⊢
    obtain ⟨⟨hmem, hz⟩, hre, him⟩ := hs
    refine ⟨⟨(one_sub_mem_closedBall_half_iff s).mpr hmem, (zeroOrbit hz).1⟩, ?_, ?_⟩
    · simp only [Complex.sub_re, Complex.one_re]
      intro h
      apply hre
      linarith
    · simp only [Complex.sub_im, Complex.one_im]
      intro h
      apply him
      linarith
  · intro s hs
    rw [mem_offLineZeros] at hs ⊢
    obtain ⟨⟨hmem, hz⟩, hre, him⟩ := hs
    exact ⟨⟨(conj_mem_closedBall_half_iff s).mpr hmem, (zeroOrbit hz).2.1⟩, by simpa using hre,
      by simpa using him⟩
  · intro s hs
    exact (mem_offLineZeros.mp hs).2.1
  · intro s hs
    exact (mem_offLineZeros.mp hs).2.2

end Soma.Holonics.RH.ZeroOrbitCount

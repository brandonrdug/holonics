import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardBoundaryEvaluation
import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardCarrierBridges

/-!
# Closing the specialized Huard return

This file joins the source's proved oriented conservation theorem to the
three exact finite evaluations owned by the carrier-bridge and boundary
modules.  The source population remains addressed until those evaluations;
the final algebra only clears the common factor three.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardEvaluation

open Finset
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardSpecialization
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardBoundaryEvaluation
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardCarrierBridges

/-- Exchanging the factor and cofactor pairs preserves the complete positive
quadruple population. -/
theorem huardFullSwap_mem {n : ℕ}
    {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ huardPositiveQuadruples n) :
    huardFullSwap q ∈ huardPositiveQuadruples n := by
  rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
  rw [mem_huardPositiveQuadruples] at hq ⊢
  change 1 ≤ x ∧ x ≤ n ∧ 1 ≤ y ∧ y ≤ n ∧
    1 ≤ a ∧ a ≤ n ∧ 1 ≤ b ∧ b ≤ n ∧ x * a + y * b = n
  rcases hq with ⟨ha1, han, hb1, hbn, hx1, hxn, hy1, hyn, hsum⟩
  exact ⟨hx1, hxn, hy1, hyn, ha1, han, hb1, hbn, by
    simpa [mul_comm, add_comm] using hsum⟩

@[simp] theorem huardFullSwap_involutive
    (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    huardFullSwap (huardFullSwap q) = q := by
  rcases q with ⟨ab, xy⟩
  rfl

/-- Every integer current may therefore be reindexed through the complete
factor/cofactor exchange without losing an occurrence. -/
theorem sum_huardFullSwap (n : ℕ)
    (H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ) :
    (∑ q ∈ huardPositiveQuadruples n, H q) =
      ∑ q ∈ huardPositiveQuadruples n, H (huardFullSwap q) := by
  apply Finset.sum_bij (fun q _hq => huardFullSwap q)
  · intro q hq
    exact huardFullSwap_mem hq
  · intro q₁ _hq₁ q₂ _hq₂ heq
    have := congrArg huardFullSwap heq
    simpa using this
  · intro q hq
    exact ⟨huardFullSwap q, huardFullSwap_mem hq, by simp⟩
  · intro q _hq
    simp

/-- The original six Huard faces and the three `g=f-f∘swap` faces agree
after summing over the complete addressed population.  The equality is not
pointwise: the second and sixth faces use factor/cofactor exchange, the fifth
uses simultaneous reversal, and the fourth uses both. -/
theorem sum_huardOrientedCurrent_specialized_eq_sixTerm (k n : ℕ) :
    (∑ q ∈ huardPositiveQuadruples n,
        huardOrientedCurrent (specializedG k) q) =
      ∑ q ∈ huardPositiveQuadruples n, specializedSixTerm k q := by
  let t₂ : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    specializedF k (q.1.1 : ℤ) (-(q.1.2 : ℤ))
      (q.2.1 : ℤ) (q.2.2 : ℤ)
  let t₄ : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    specializedF k (q.1.1 : ℤ) ((q.1.1 : ℤ) + (q.1.2 : ℤ))
      ((q.2.2 : ℤ) - (q.2.1 : ℤ)) (q.2.2 : ℤ)
  let t₅ : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    specializedF k ((q.1.2 : ℤ) - (q.1.1 : ℤ)) (q.1.2 : ℤ)
      (q.2.1 : ℤ) ((q.2.1 : ℤ) + (q.2.2 : ℤ))
  let t₆ : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    specializedF k ((q.1.1 : ℤ) + (q.1.2 : ℤ)) (q.1.2 : ℤ)
      (q.2.1 : ℤ) ((q.2.1 : ℤ) - (q.2.2 : ℤ))
  have h₂ := sum_huardFullSwap n t₂
  have h₄full := sum_huardFullSwap n t₄
  have h₄turn := sum_quadSwap n (fun q => t₄ (huardFullSwap q))
  have h₅ := sum_quadSwap n t₅
  have h₆ := sum_huardFullSwap n t₆
  simp only [t₂, t₄, t₅, t₆, huardFullSwap, quadSwap, add_comm] at h₂ h₄full h₄turn h₅ h₆
  simp only [huardOrientedCurrent, specializedG, specializedSixTerm,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linear_combination h₂ + h₄full + h₄turn - h₅ + h₆

/-! ## The complete specialized evaluation -/

/-- The exact finite source return, the three carrier rebases, and the
boundary divisor-row evaluation together prove the specialized Huard
six-term identity at every positive scale and positive address. -/
theorem specializedSixTermEvaluation_proved
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    SpecializedSixTermEvaluation k n := by
  have horiented := specializedOrientedReturn_expanded
    huardOffDiagonalCancellation_proved (k := k) hn
  have hsix := sum_huardOrientedCurrent_specialized_eq_sixTerm k n
  have hcarriers := specializedSixTerm_sum_eq_qCarriers k n
  have hboundary := three_mul_sum_specializedBoundaryExpansion hk hn
  have hsource :
      2 * qMinusCarrier k n + 2 * qPlusCarrier k n -
          8 * qScaleCarrier k n =
        ∑ dt ∈ huardBoundaryPairs n,
          specializedBoundaryExpansion k n dt := by
    calc
      _ = ∑ q ∈ huardPositiveQuadruples n, specializedSixTerm k q :=
        hcarriers.symm
      _ = ∑ q ∈ huardPositiveQuadruples n,
          huardOrientedCurrent (specializedG k) q := hsix.symm
      _ = _ := horiented
  rw [qMinusCarrier_eq_huardMinusCurrent,
    qPlusCarrier_eq_huardPlusCurrent,
    qScaleCarrier_eq_scaledDivisorConvolution k n hk] at hsource
  by_cases hkn : k ∣ n
  · rw [if_pos hkn] at hboundary
    simp only [SpecializedSixTermEvaluation, if_pos hkn]
    linarith
  · rw [if_neg hkn] at hboundary
    simp only [SpecializedSixTermEvaluation, if_neg hkn]
    linarith

/-- The remaining source proposition is now inhabited without an admitted
arithmetic hypothesis. -/
theorem huardLemmaOneCleared_proved : HuardLemmaOneCleared :=
  huardLemmaOneCleared_of_specializedSixTermEvaluation
    (fun _k _n hk hn => specializedSixTermEvaluation_proved hk hn)

#print axioms sum_huardOrientedCurrent_specialized_eq_sixTerm
#print axioms specializedSixTermEvaluation_proved
#print axioms huardLemmaOneCleared_proved

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardEvaluation

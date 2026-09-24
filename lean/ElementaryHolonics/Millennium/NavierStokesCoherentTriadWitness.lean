import ElementaryHolonics.Millennium.NavierStokesFourierTriads
import ElementaryHolonics.Millennium.NavierStokesH3LerayBilinear

/-!
# A concrete noncollinear coherent Fourier triad

This owner is a coefficient-level witness for the quadratic source.  The two input frequencies
are `e₀` and `e₁`, with divergence-free amplitudes `(0,1,1)` and `(1,0,1)`.  Their exchanged
advective feeds at `e₀ + e₁` have the same nonzero third component.  The exact existing Leray
projection removes the parallel `(1,1,0)` part and leaves a nonzero third component.

The result is deliberately finite and algebraic.  It does not construct a physical solution,
prove a coherence-defect bound, or infer a blowup conclusion.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesCoherentTriadWitness

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity

def p : SpatialFrequency := ![1, 0, 0]

def q : SpatialFrequency := ![0, 1, 0]

def k : SpatialFrequency := p + q

def vp : ComplexVector := ![0, 1, 1]

def vq : ComplexVector := ![1, 0, 1]

def firstFeed : ComplexVector := complexAdvectiveInteraction p q vp vq

def secondFeed : ComplexVector := complexAdvectiveInteraction q p vq vp

def feedSum : ComplexVector := firstFeed + secondFeed

def projectedFeedSum : ComplexVector := lerayProjectMode k feedSum

/-! ## The complete finite real coefficient population -/

def finiteSupport : Finset SpatialFrequency := {p, q, -p, -q}

def coefficientPopulation : SpatialFrequency → ComplexVector := fun frequency ↦
  if frequency = p then vp
  else if frequency = q then vq
  else if frequency = -p then vp
  else if frequency = -q then vq
  else 0

def completeAdvectiveSourceAt : ComplexVector :=
  ∑' parent : SpatialFrequency,
    complexAdvectiveInteraction parent (k - parent)
      (coefficientPopulation parent) (coefficientPopulation (k - parent))

def completeProjectedSourceAt : ComplexVector :=
  lerayProjectMode k completeAdvectiveSourceAt

def pdeProjectedNonlinearSourceAt : ComplexVector := -completeProjectedSourceAt

def completeDiagonalFeedSquareAt : ℝ :=
  ∑' parent : SpatialFrequency,
    ‖(complexAdvectiveInteraction parent (k - parent)
      (coefficientPopulation parent) (coefficientPopulation (k - parent))) 2‖ ^ 2

theorem p_eq : p = ![1, 0, 0] := rfl

theorem q_eq : q = ![0, 1, 0] := rfl

theorem k_eq : k = ![1, 1, 0] := by
  ext i
  fin_cases i <;> simp [k, p, q]

theorem input_frequencies_noncollinear :
    complexCross (complexFrequencyVector p) (complexFrequencyVector q) ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : ComplexVector => z 2) h
  simp [complexCross, complexFrequencyVector, p, q, crossProduct] at hcoord

theorem p_ne_zero : p ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : SpatialFrequency => z 0) h
  simp [p] at hcoord

theorem q_ne_zero : q ≠ 0 := by
  intro h
  have hcoord := congrArg (fun z : SpatialFrequency => z 1) h
  simp [q] at hcoord

theorem finiteSupport_pairwise_distinct :
    p ≠ q ∧ p ≠ -p ∧ p ≠ -q ∧ q ≠ -p ∧ q ≠ -q ∧ -p ≠ -q := by
  simp [p, q]

theorem coefficientPopulation_apply_p : coefficientPopulation p = vp := by
  simp [coefficientPopulation, p]

theorem coefficientPopulation_apply_q : coefficientPopulation q = vq := by
  simp [coefficientPopulation, p, q]

theorem coefficientPopulation_apply_neg_p : coefficientPopulation (-p) = vp := by
  simp [coefficientPopulation, p, q]

theorem coefficientPopulation_apply_neg_q : coefficientPopulation (-q) = vq := by
  simp [coefficientPopulation, p, q]

theorem coefficientPopulation_zero_of_not_mem {parent : SpatialFrequency}
    (hparent : parent ∉ finiteSupport) : coefficientPopulation parent = 0 := by
  simp only [coefficientPopulation]
  split <;> rename_i h
  · exact False.elim (hparent (by simp [finiteSupport, h]))
  split <;> rename_i h
  · exact False.elim (hparent (by simp [finiteSupport, h]))
  split <;> rename_i h
  · exact False.elim (hparent (by simp [finiteSupport, h]))
  split <;> rename_i h
  · exact False.elim (hparent (by simp [finiteSupport, h]))
  rfl

theorem completeSource_term_zero_outside_support (parent : SpatialFrequency)
    (hparent : parent ∉ finiteSupport) :
    complexAdvectiveInteraction parent (k - parent)
      (coefficientPopulation parent) (coefficientPopulation (k - parent)) = 0 := by
  rw [coefficientPopulation_zero_of_not_mem hparent]
  simp [complexAdvectiveInteraction, complexDot, dotProduct]

theorem coefficientPopulation_k_eq_zero : coefficientPopulation k = 0 := by
  apply coefficientPopulation_zero_of_not_mem
  simp [finiteSupport, k, p, q]

theorem coefficientPopulation_divergence_free :
    ∀ frequency, complexDot (complexFrequencyVector frequency)
      (coefficientPopulation frequency) = 0 := by
  intro frequency
  by_cases hpF : frequency = p
  · subst frequency
    rw [coefficientPopulation_apply_p]
    simp [p, vp, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]
  by_cases hqF : frequency = q
  · subst frequency
    rw [coefficientPopulation_apply_q]
    simp [q, vq, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]
  by_cases hnpF : frequency = -p
  · subst frequency
    rw [coefficientPopulation_apply_neg_p]
    simp [p, vp, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]
  by_cases hnqF : frequency = -q
  · subst frequency
    rw [coefficientPopulation_apply_neg_q]
    simp [q, vq, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]
  rw [coefficientPopulation_zero_of_not_mem (by
    simp only [finiteSupport, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpF, hqF, hnpF, hnqF⟩)]
  simp [complexDot, dotProduct]

theorem coefficientPopulation_conjugate_symmetric (frequency : SpatialFrequency) :
    coefficientPopulation (-frequency) =
      fun component ↦ (starRingEnd ℂ) (coefficientPopulation frequency component) := by
  by_cases hpF : frequency = p
  · subst frequency
    rw [coefficientPopulation_apply_neg_p, coefficientPopulation_apply_p]
    ext component
    fin_cases component <;> simp [vp]
  by_cases hqF : frequency = q
  · subst frequency
    rw [coefficientPopulation_apply_neg_q, coefficientPopulation_apply_q]
    ext component
    fin_cases component <;> simp [vq]
  by_cases hnpF : frequency = -p
  · subst frequency
    rw [show -(-p) = p by simp, coefficientPopulation_apply_p,
      coefficientPopulation_apply_neg_p]
    ext component
    fin_cases component <;> simp [vp]
  by_cases hnqF : frequency = -q
  · subst frequency
    rw [show -(-q) = q by simp, coefficientPopulation_apply_q,
      coefficientPopulation_apply_neg_q]
    ext component
    fin_cases component <;> simp [vq]
  have hfrequency : frequency ∉ finiteSupport := by
    simp only [finiteSupport, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpF, hqF, hnpF, hnqF⟩
  have hnegp : -frequency ≠ p := by
    intro h
    apply hnpF
    have := congrArg Neg.neg h
    simpa using this
  have hnegq : -frequency ≠ q := by
    intro h
    apply hnqF
    have := congrArg Neg.neg h
    simpa using this
  have hnegnp : -frequency ≠ -p := by
    intro h
    apply hpF
    exact neg_injective h
  have hnegnq : -frequency ≠ -q := by
    intro h
    apply hqF
    exact neg_injective h
  have hnegfrequency : -frequency ∉ finiteSupport := by
    simp only [finiteSupport, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hnegp, hnegq, hnegnp, hnegnq⟩
  rw [coefficientPopulation_zero_of_not_mem hnegfrequency,
    coefficientPopulation_zero_of_not_mem hfrequency]
  ext component
  simp

theorem completeAdvectiveSourceAt_eq_feedSum :
    completeAdvectiveSourceAt = feedSum := by
  have hkp : k - p = q := by
    ext i
    fin_cases i <;> simp [k, p, q]
  have hkq : k - q = p := by
    ext i
    fin_cases i <;> simp [k, p, q]
  have htransportp : coefficientPopulation (k - -p) = 0 := by
    apply coefficientPopulation_zero_of_not_mem
    simp [finiteSupport, k, p, q]
  have htransportq : coefficientPopulation (k - -q) = 0 := by
    apply coefficientPopulation_zero_of_not_mem
    simp [finiteSupport, k, p, q]
  unfold completeAdvectiveSourceAt
  rw [tsum_eq_sum (s := finiteSupport)]
  · rw [show finiteSupport = {p, q, -p, -q} by rfl]
    rw [Finset.sum_insert (by simp [p, q]), Finset.sum_insert (by simp [p, q]),
      Finset.sum_insert (by simp [p, q]), Finset.sum_singleton]
    rw [coefficientPopulation_apply_p, hkp, coefficientPopulation_apply_q,
      coefficientPopulation_apply_neg_p, htransportp, coefficientPopulation_apply_neg_q,
      htransportq, hkq, coefficientPopulation_apply_p]
    simp [complexAdvectiveInteraction, feedSum, firstFeed, secondFeed, complexDot, dotProduct,
      complexFrequencyVector, Fin.sum_univ_succ]
  · intro parent hparent
    exact completeSource_term_zero_outside_support parent hparent

theorem completeProjectedSourceAt_eq_projectedFeedSum :
    completeProjectedSourceAt = projectedFeedSum := by
  unfold completeProjectedSourceAt projectedFeedSum
  rw [completeAdvectiveSourceAt_eq_feedSum]

theorem vp_divergence_free :
    complexDot (complexFrequencyVector p) vp = 0 := by
  simp [p, vp, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]

theorem vq_divergence_free :
    complexDot (complexFrequencyVector q) vq = 0 := by
  simp [q, vq, complexDot, dotProduct, complexFrequencyVector, Fin.sum_univ_succ]

theorem firstFeed_component_two : firstFeed 2 = 2 * (Real.pi : ℂ) * Complex.I := by
  simp [firstFeed, complexAdvectiveInteraction, q, vp, vq, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

theorem secondFeed_component_two : secondFeed 2 = 2 * (Real.pi : ℂ) * Complex.I := by
  simp [secondFeed, complexAdvectiveInteraction, p, vp, vq, complexDot, dotProduct,
    complexFrequencyVector, Fin.sum_univ_succ]

theorem feed_component_two_eq : firstFeed 2 = secondFeed 2 := by
  rw [firstFeed_component_two, secondFeed_component_two]

theorem feed_component_two_ne_zero : firstFeed 2 ≠ 0 := by
  rw [firstFeed_component_two]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem projectedFeedSum_eq_third_axis : projectedFeedSum =
    ![0, 0, 4 * (Real.pi : ℂ) * Complex.I] := by
  rw [projectedFeedSum, feedSum, firstFeed, secondFeed, k_eq]
  ext i
  fin_cases i <;>
    simp [lerayProjectMode, complexAdvectiveInteraction, p, q, vp, vq,
      complexDot, dotProduct, complexFrequencyVector, frequencySquared, Fin.sum_univ_succ] <;>
    ring

theorem pdeProjectedNonlinearSourceAt_eq_neg_third_axis :
    pdeProjectedNonlinearSourceAt = ![0, 0, -(4 * (Real.pi : ℂ) * Complex.I)] := by
  rw [pdeProjectedNonlinearSourceAt, completeProjectedSourceAt_eq_projectedFeedSum,
    projectedFeedSum_eq_third_axis]
  ext i
  fin_cases i <;> simp

theorem completeDiagonalFeedSquareAt_eq_first_second :
    completeDiagonalFeedSquareAt = ‖firstFeed 2‖ ^ 2 + ‖secondFeed 2‖ ^ 2 := by
  have hkp : k - p = q := by
    ext i
    fin_cases i <;> simp [k, p, q]
  have hkq : k - q = p := by
    ext i
    fin_cases i <;> simp [k, p, q]
  have htransportp : coefficientPopulation (k - -p) = 0 := by
    apply coefficientPopulation_zero_of_not_mem
    simp [finiteSupport, k, p, q]
  have htransportq : coefficientPopulation (k - -q) = 0 := by
    apply coefficientPopulation_zero_of_not_mem
    simp [finiteSupport, k, p, q]
  unfold completeDiagonalFeedSquareAt
  rw [tsum_eq_sum (s := finiteSupport)]
  · rw [show finiteSupport = {p, q, -p, -q} by rfl]
    rw [Finset.sum_insert (by simp [p, q]), Finset.sum_insert (by simp [p, q]),
      Finset.sum_insert (by simp [p, q]), Finset.sum_singleton]
    rw [coefficientPopulation_apply_p, hkp, coefficientPopulation_apply_q,
      coefficientPopulation_apply_neg_p, htransportp, coefficientPopulation_apply_neg_q,
      htransportq, hkq, coefficientPopulation_apply_p]
    simp [complexAdvectiveInteraction, firstFeed, secondFeed]
  · intro parent hparent
    have hzero := completeSource_term_zero_outside_support parent hparent
    rw [show (complexAdvectiveInteraction parent (k - parent)
        (coefficientPopulation parent) (coefficientPopulation (k - parent))) 2 = 0 by
      exact congrArg (fun z : ComplexVector ↦ z 2) hzero]
    simp

theorem completeAdvectiveSourceAt_component_two_norm_sq_eq_twice_diagonal :
    ‖completeAdvectiveSourceAt 2‖ ^ 2 = 2 * completeDiagonalFeedSquareAt := by
  rw [completeAdvectiveSourceAt_eq_feedSum, completeDiagonalFeedSquareAt_eq_first_second,
    feedSum]
  simp only [Pi.add_apply]
  rw [firstFeed_component_two, secondFeed_component_two]
  have hnorm : ‖(Real.pi : ℂ) * Complex.I * 4‖ = 4 * Real.pi := by
    rw [norm_mul, norm_mul]
    simp [abs_of_pos Real.pi_pos]
    ring
  have hnorm2 : ‖2 * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul]
    simp [abs_of_pos Real.pi_pos]
  have hsum : 2 * (Real.pi : ℂ) * Complex.I + 2 * (Real.pi : ℂ) * Complex.I =
      (Real.pi : ℂ) * Complex.I * 4 := by ring
  rw [hsum, hnorm, hnorm2]
  ring

theorem complete_coefficient_inequality_iff (κ : ℝ) :
    ‖completeAdvectiveSourceAt 2‖ ^ 2 ≤
        (1 + κ) * completeDiagonalFeedSquareAt ↔ 1 ≤ κ := by
  have hdiagonal : 0 < completeDiagonalFeedSquareAt := by
    rw [completeDiagonalFeedSquareAt_eq_first_second, firstFeed_component_two,
      secondFeed_component_two]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
      Complex.norm_I, mul_one]
    rw [abs_of_pos Real.pi_pos]
    positivity
  rw [completeAdvectiveSourceAt_component_two_norm_sq_eq_twice_diagonal]
  constructor <;> intro h
  · nlinarith
  · nlinarith

theorem projectedFeedSum_component_two_ne_zero : projectedFeedSum 2 ≠ 0 := by
  rw [projectedFeedSum_eq_third_axis]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

theorem projectedFeedSum_divergence_free :
    complexDot (complexFrequencyVector k) projectedFeedSum = 0 := by
  exact complexDot_lerayProjectMode_eq_zero k feedSum

theorem projectedFeedSum_norm_sq_eq_twice_diagonal_feed_norm_sq :
    ‖projectedFeedSum‖ ^ 2 =
      2 * (‖firstFeed 2‖ ^ 2 + ‖secondFeed 2‖ ^ 2) := by
  rw [projectedFeedSum_eq_third_axis, firstFeed_component_two, secondFeed_component_two]
  rw [Pi.norm_def]
  rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
  rw [Finset.sup_insert, Finset.sup_insert, Finset.sup_singleton]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  simp only [nnnorm_zero, zero_max]
  change ‖4 * (Real.pi : ℂ) * Complex.I‖ ^ 2 = _
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
    Complex.norm_I, mul_one]
  rw [abs_of_pos Real.pi_pos]
  ring

theorem output_frequency_eq_sum : k = p + q := rfl

theorem output_frequency_differs_from_p : k ≠ p := by
  intro h
  have hcoord := congrArg (fun z : SpatialFrequency => z 1) h
  simp [k, p, q] at hcoord

theorem output_frequency_differs_from_q : k ≠ q := by
  intro h
  have hcoord := congrArg (fun z : SpatialFrequency => z 0) h
  simp [k, p, q] at hcoord

theorem generic_zero_vector_ne_projectedFeedSum :
    (0 : ComplexVector) ≠ projectedFeedSum := by
  intro h
  have hcoord := congrArg (fun z : ComplexVector => z 2) h
  exact (projectedFeedSum_component_two_ne_zero hcoord.symm)

theorem complete_coefficient_receiver_zero_input_nonzero_source :
    coefficientPopulation k = 0 ∧ pdeProjectedNonlinearSourceAt ≠ 0 := by
  constructor
  · exact coefficientPopulation_k_eq_zero
  · rw [pdeProjectedNonlinearSourceAt_eq_neg_third_axis]
    intro h
    have hcoord := congrArg (fun z : ComplexVector => z 2) h
    simp at hcoord

#print axioms vp_divergence_free
#print axioms vq_divergence_free
#print axioms projectedFeedSum_eq_third_axis
#print axioms projectedFeedSum_norm_sq_eq_twice_diagonal_feed_norm_sq
#print axioms coefficientPopulation_conjugate_symmetric
#print axioms completeAdvectiveSourceAt_eq_feedSum
#print axioms completeProjectedSourceAt_eq_projectedFeedSum
#print axioms pdeProjectedNonlinearSourceAt_eq_neg_third_axis
#print axioms coefficientPopulation_k_eq_zero
#print axioms coefficientPopulation_divergence_free
#print axioms completeDiagonalFeedSquareAt_eq_first_second
#print axioms completeAdvectiveSourceAt_component_two_norm_sq_eq_twice_diagonal
#print axioms complete_coefficient_inequality_iff
#print axioms generic_zero_vector_ne_projectedFeedSum
#print axioms complete_coefficient_receiver_zero_input_nonzero_source

end Soma.Holonics.Millennium.NavierStokesCoherentTriadWitness

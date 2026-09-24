import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource

/-!
# The divisibility-indicator specialization of the Huard source

This file supplies the exact polynomial/indicator carrier used in the
Huard--Ou--Spearman--Williams passage.  The indicator is an integer-valued
divisibility face, so no floor division or numerical approximation enters the
specialization.  The source theorem is instantiated with its oriented
difference.  The resulting equality is the largest source-faithful return
before the six finite affine reindexing sums are evaluated into the named
divisor and congruence currents.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardSpecialization

open Finset
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource

/-! ## Exact integer carrier -/

/-- The exact divisibility face at modulus `k`. -/
def divisibilityIndicator (k : ℕ) (x : ℤ) : ℤ :=
  if (k : ℤ) ∣ x then 1 else 0

/-- The source polynomial `f(a,b,x,y)=(2a²-b²)F_k(x)`. -/
def specializedF (k : ℕ) (a b x _y : ℤ) : ℤ :=
  (2 * a ^ 2 - b ^ 2) * divisibilityIndicator k x

/-- The oriented difference `g=f-f∘swap` used by the finite source theorem. -/
def specializedG (k : ℕ) (a b x y : ℤ) : ℤ :=
  specializedF k a b x y - specializedF k x y a b

theorem divisibilityIndicator_neg (k : ℕ) (x : ℤ) :
    divisibilityIndicator k (-x) = divisibilityIndicator k x := by
  simp [divisibilityIndicator]

/-- The specialized difference obeys the source's sign-flip law. -/
theorem specializedG_flip (k : ℕ) :
    ∀ a b x y : ℤ,
      specializedG k a (-b) x y = specializedG k (-a) b x y := by
  intro a b x y
  simp [specializedG, specializedF, divisibilityIndicator, dvd_neg]

/-- Every oriented difference is antisymmetric under exchanging the two pairs. -/
theorem specializedG_antisymmetric (k : ℕ) :
    ∀ a b x y : ℤ,
      specializedG k a b x y = -specializedG k x y a b := by
  intro a b x y
  simp [specializedG]

/-! ## Exact source return -/

/-- The divisibility-indicator specialization of the finite Huard theorem.

This is an exact equality of the retained positive-quadruple carrier and its
divisor-boundary return.  It is the source-faithful bridge needed before the
finite affine maps are evaluated into `scaledDivisorConvolution` and the two
Huard congruence currents.
-/
theorem specializedOrientedReturn
    (hoff : HuardOffDiagonalCancellation)
    {k n : ℕ} (hn : 0 < n) :
    (∑ q ∈ huardPositiveQuadruples n,
        huardOrientedCurrent (specializedG k) q) =
      ∑ dt ∈ huardBoundaryPairs n,
        huardBoundaryCurrent (specializedG k) n dt := by
  exact huardOrientedTheoremOne_of_offDiagonal hoff
    (specializedG k) (specializedG_flip k) (specializedG_antisymmetric k) hn

/-! ## Boundary-face evaluation -/

/-- The six polynomial/indicator faces at a boundary point `(d,t)`, written
with all chart coordinates exposed.  The subtraction in the third face is
integer subtraction: the boundary chart retains the oriented difference even
when its natural-number representatives are ordered. -/
def specializedBoundaryExpansion (k n : ℕ) (dt : ℕ × ℕ) : ℤ :=
  ((2 * ((n / dt.1 : ℕ) : ℤ) ^ 2) * divisibilityIndicator k (dt.1 : ℤ) -
      (2 * (dt.1 : ℤ) ^ 2 - (dt.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((n / dt.1 : ℕ) : ℤ)) +
    (-((n / dt.1 : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (dt.2 : ℤ) -
      (2 * (dt.2 : ℤ) ^ 2 - (dt.1 : ℤ) ^ 2) *
        divisibilityIndicator k 0) +
    (((n / dt.1 : ℕ) : ℤ) ^ 2 *
        divisibilityIndicator k ((dt.1 : ℤ) - (dt.2 : ℤ)) -
      (2 * ((dt.1 : ℤ) - (dt.2 : ℤ)) ^ 2 - (dt.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((n / dt.1 : ℕ) : ℤ))

theorem huardBoundaryCurrent_specialized_eq
    (k n : ℕ) (dt : ℕ × ℕ) :
    huardBoundaryCurrent (specializedG k) n dt =
      specializedBoundaryExpansion k n dt := by
  simp only [huardBoundaryCurrent, specializedBoundaryExpansion,
    specializedG, specializedF]
  ring

/-- The exact specialized source return with the boundary receiver expanded
into its three oriented faces. -/
theorem specializedOrientedReturn_expanded
    (hoff : HuardOffDiagonalCancellation)
    {k n : ℕ} (hn : 0 < n) :
    (∑ q ∈ huardPositiveQuadruples n,
        huardOrientedCurrent (specializedG k) q) =
      ∑ dt ∈ huardBoundaryPairs n,
        specializedBoundaryExpansion k n dt := by
  rw [specializedOrientedReturn hoff hn]
  apply Finset.sum_congr rfl
  intro dt hdt
  rw [huardBoundaryCurrent_specialized_eq]

/-! ## The six source faces before their receiver reindexing -/

/-- The six-term current appearing on the left of Huard--Ou--Spearman--
Williams Theorem 1, evaluated at a positive quadruple. -/
def specializedSixTerm (k : ℕ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  specializedF k (q.1.1 : ℤ) (q.1.2 : ℤ) (q.2.1 : ℤ) (-(q.2.2 : ℤ)) -
    specializedF k (q.1.1 : ℤ) (-(q.1.2 : ℤ)) (q.2.1 : ℤ) (q.2.2 : ℤ) +
    specializedF k (q.1.1 : ℤ) ((q.1.1 : ℤ) - (q.1.2 : ℤ))
      ((q.2.1 : ℤ) + (q.2.2 : ℤ)) (q.2.2 : ℤ) -
    specializedF k (q.1.1 : ℤ) ((q.1.1 : ℤ) + (q.1.2 : ℤ))
      ((q.2.2 : ℤ) - (q.2.1 : ℤ)) (q.2.2 : ℤ) +
    specializedF k ((q.1.2 : ℤ) - (q.1.1 : ℤ)) (q.1.2 : ℤ)
      (q.2.1 : ℤ) ((q.2.1 : ℤ) + (q.2.2 : ℤ)) -
    specializedF k ((q.1.1 : ℤ) + (q.1.2 : ℤ)) (q.1.2 : ℤ)
      (q.2.1 : ℤ) ((q.2.1 : ℤ) - (q.2.2 : ℤ))

/-- The polynomial face of the six-term current has only three surviving
transport directions: the two congruence differences and the scale face. -/
def specializedTransportFace (k : ℕ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
  (((q.1.1 : ℤ) ^ 2 + 2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) -
        (q.1.2 : ℤ) ^ 2) *
      divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) +
    (-(q.1.1 : ℤ) ^ 2 + 2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) +
        (q.1.2 : ℤ) ^ 2) *
      divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ)) -
    8 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k (q.2.1 : ℤ)

theorem specializedSixTerm_eq_transport_faces
    (k : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    specializedSixTerm k q = specializedTransportFace k q := by
  simp only [specializedSixTerm, specializedF, divisibilityIndicator_neg]
  simp only [specializedTransportFace]
  ring

/-- The exact finite carrier equality obtained before evaluating its two
congruence currents.  It is the source's long calculation with every
summand exposed, and is useful as the reindexing boundary for the next deed. -/
theorem specializedSixTerm_sum_eq_transport_faces
    (k n : ℕ) :
    (∑ q ∈ huardPositiveQuadruples n, specializedSixTerm k q) =
      ∑ q ∈ huardPositiveQuadruples n, specializedTransportFace k q := by
  apply Finset.sum_congr rfl
  intro q hq
  exact specializedSixTerm_eq_transport_faces k q

/-- The three q-carriers exposed by the specialized source.  These retain
the full factor/cofactor occurrence, unlike their later divisor-current
receiver shadows. -/
def qMinusCarrier (k n : ℕ) : ℤ :=
  ∑ q ∈ huardPositiveQuadruples n,
    (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))

def qPlusCarrier (k n : ℕ) : ℤ :=
  ∑ q ∈ huardPositiveQuadruples n,
    (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))

def qScaleCarrier (k n : ℕ) : ℤ :=
  ∑ q ∈ huardPositiveQuadruples n,
    (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k (q.2.1 : ℤ)

def specializedTransportDecomposed (k : ℕ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : ℤ :=
    ((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ)) +
      2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
        divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ)) -
      ((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ)) +
      2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
        divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ)) -
      8 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
        divisibilityIndicator k (q.2.1 : ℤ)

theorem specializedTransportFace_eq_decomposed
    (k : ℕ) (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    specializedTransportFace k q = specializedTransportDecomposed k q := by
  simp only [specializedTransportFace, specializedTransportDecomposed]
  ring

def quadSwap (q : (ℕ × ℕ) × (ℕ × ℕ)) : (ℕ × ℕ) × (ℕ × ℕ) :=
  ((q.1.2, q.1.1), (q.2.2, q.2.1))

theorem quadSwap_mem (n : ℕ) {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ huardPositiveQuadruples n) :
    quadSwap q ∈ huardPositiveQuadruples n := by
  rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
  rw [huardPositiveQuadruples, Finset.mem_filter] at hq
  rcases hq with ⟨hbox, heq⟩
  change a * x + b * y = n at heq
  rw [huardPositiveQuadruples, Finset.mem_filter]
  have hbox' :
      (a, b) ∈ (Finset.Icc 1 n).product (Finset.Icc 1 n) ∧
        (x, y) ∈ (Finset.Icc 1 n).product (Finset.Icc 1 n) := by
    exact Finset.mem_product.mp hbox
  have hab' := Finset.mem_product.mp hbox'.1
  have hxy' := Finset.mem_product.mp hbox'.2
  change ((b, a), (y, x)) ∈
      ((Finset.Icc 1 n).product (Finset.Icc 1 n)).product
        ((Finset.Icc 1 n).product (Finset.Icc 1 n)) ∧
      b * y + a * x = n
  constructor
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
          ⟨hab'.2, hab'.1⟩,
        Finset.mem_product.mpr
          ⟨hxy'.2, hxy'.1⟩⟩
  · omega

theorem quadSwap_involutive (q : (ℕ × ℕ) × (ℕ × ℕ)) :
    quadSwap (quadSwap q) = q := by
  rcases q with ⟨⟨a, b⟩, ⟨x, y⟩⟩
  rfl

theorem sum_quadSwap (n : ℕ) (H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ) :
    (∑ q ∈ huardPositiveQuadruples n, H q) =
      ∑ q ∈ huardPositiveQuadruples n, H (quadSwap q) := by
  apply Finset.sum_bij (fun q _hq => quadSwap q)
  · intro q hq
    exact quadSwap_mem n hq
  · intro q₁ hq₁ q₂ hq₂ heq
    have := congrArg quadSwap heq
    simpa [quadSwap] using this
  · intro q hq
    exact ⟨quadSwap q, quadSwap_mem n hq, quadSwap_involutive q⟩
  · intro q hq
    simpa [quadSwap_involutive q]

theorem qOddMinus_sum_zero (k n : ℕ) :
    (∑ q ∈ huardPositiveQuadruples n,
      ((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) = 0 := by
  let H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    ((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
      divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))
  have hs := sum_quadSwap n H
  have hneg : (∑ q ∈ huardPositiveQuadruples n, H (quadSwap q)) =
      -∑ q ∈ huardPositiveQuadruples n, H q := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    simp [H, quadSwap, add_comm]
    ring
  linarith

theorem qOddPlus_sum_zero (k n : ℕ) :
    (∑ q ∈ huardPositiveQuadruples n,
      -((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
        divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))) = 0 := by
  let H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    -((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
      divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))
  have hs := sum_quadSwap n H
  have hneg : (∑ q ∈ huardPositiveQuadruples n, H (quadSwap q)) =
      -∑ q ∈ huardPositiveQuadruples n, H q := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    have hi := divisibilityIndicator_neg k
      ((q.2.1 : ℤ) - (q.2.2 : ℤ))
    rw [show -((q.2.1 : ℤ) - (q.2.2 : ℤ)) =
        (q.2.2 : ℤ) - (q.2.1 : ℤ) by ring] at hi
    have hi' : divisibilityIndicator k (-(q.2.1 : ℤ) + (q.2.2 : ℤ)) =
        divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ)) := by
      congr 1
      ring
    have hi'' : divisibilityIndicator k ((q.2.1 : ℤ) - (q.2.2 : ℤ)) =
        divisibilityIndicator k (-(q.2.1 : ℤ) + (q.2.2 : ℤ)) :=
      hi.symm.trans hi'.symm
    simp [H, quadSwap]
    rw [hi'']
    ring
  linarith

theorem specializedSixTerm_sum_eq_qCarriers (k n : ℕ) :
    (∑ q ∈ huardPositiveQuadruples n, specializedSixTerm k q) =
      2 * qMinusCarrier k n + 2 * qPlusCarrier k n -
        8 * qScaleCarrier k n := by
  rw [specializedSixTerm_sum_eq_transport_faces]
  rw [show (∑ q ∈ huardPositiveQuadruples n, specializedTransportFace k q) =
      ∑ q ∈ huardPositiveQuadruples n, specializedTransportDecomposed k q by
    apply Finset.sum_congr rfl
    intro q hq
    exact specializedTransportFace_eq_decomposed k q]
  have hminus := qOddMinus_sum_zero k n
  have hplus := qOddPlus_sum_zero k n
  have hminus2 :
      (∑ q ∈ huardPositiveQuadruples n,
        2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
          divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) =
        2 * qMinusCarrier k n := by
    unfold qMinusCarrier
    calc
      _ = ∑ q ∈ huardPositiveQuadruples n,
          2 * ((q.1.1 : ℤ) * (q.1.2 : ℤ) *
            divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hplus2 :
      (∑ q ∈ huardPositiveQuadruples n,
        2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
          divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))) =
        2 * qPlusCarrier k n := by
    unfold qPlusCarrier
    calc
      _ = ∑ q ∈ huardPositiveQuadruples n,
          2 * ((q.1.1 : ℤ) * (q.1.2 : ℤ) *
            divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hscale8 :
      (∑ q ∈ huardPositiveQuadruples n,
        8 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
          divisibilityIndicator k (q.2.1 : ℤ)) =
        8 * qScaleCarrier k n := by
    unfold qScaleCarrier
    calc
      _ = ∑ q ∈ huardPositiveQuadruples n,
          8 * ((q.1.1 : ℤ) * (q.1.2 : ℤ) *
            divisibilityIndicator k (q.2.1 : ℤ)) := by
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hlinear :
      (∑ q ∈ huardPositiveQuadruples n, specializedTransportDecomposed k q) =
        (∑ q ∈ huardPositiveQuadruples n,
          ((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
            divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) +
          (∑ q ∈ huardPositiveQuadruples n,
            2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
              divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))) +
        (∑ q ∈ huardPositiveQuadruples n,
          -((q.1.1 : ℤ) ^ 2 - (q.1.2 : ℤ) ^ 2) *
            divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))) +
          (∑ q ∈ huardPositiveQuadruples n,
            2 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
              divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))) -
        (∑ q ∈ huardPositiveQuadruples n,
          8 * (q.1.1 : ℤ) * (q.1.2 : ℤ) *
            divisibilityIndicator k (q.2.1 : ℤ)) := by
    simp only [specializedTransportDecomposed, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_mul,
      neg_mul]
    ring
  rw [hlinear, hminus, hplus, hminus2, hplus2, hscale8]
  ring

/-! ## The exact residual to the named arithmetic currents -/

/-- The remaining source-side evaluation obligation.  It records precisely
the finite equality still needed to turn the specialized oriented return into
the cleared Huard lemma; it introduces no proposition as an axiom. -/
def SpecializedSixTermEvaluation (k n : ℕ) : Prop :=
  24 * scaledDivisorConvolution k n =
    -cubicDivisorCurrent n + ordinaryDivisorCurrent n +
      (if k ∣ n then
        6 * cubicDivisorCurrent (n / k) -
          6 * (n : ℤ) * ordinaryDivisorCurrent (n / k)
      else 0) +
      6 * huardMinusCurrent k n + 6 * huardPlusCurrent k n

/-- The source specialization has exactly the target shape: closing its six
finite affine reindexing evaluation is the remaining `HuardLemmaOneCleared`
edge. -/
theorem huardLemmaOneCleared_of_specializedSixTermEvaluation
    (heval : ∀ k n : ℕ, 0 < k → 0 < n → SpecializedSixTermEvaluation k n) :
    HuardLemmaOneCleared := by
  intro k n hk hn
  simpa [SpecializedSixTermEvaluation] using heval k n hk hn

#print axioms divisibilityIndicator_neg
#print axioms specializedG_flip
#print axioms specializedG_antisymmetric
#print axioms specializedOrientedReturn
#print axioms huardLemmaOneCleared_of_specializedSixTermEvaluation

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardSpecialization

import Mathlib.Tactic
import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Transport.ReceiverPotential

/-!
# A finite joint-receiver witness

This file formalizes the exact finite counterexample recorded in
`research/experiments/alpha_passive_junction/bit_marginal_receipt.json`.  Three equally weighted
source occurrences carry the packets `011`, `101`, and `110`.  Every single-bit marginal has value
`2/3`, so componentwise majority produces `111`, while that complete packet is absent from the
actual joint source range.  A second two-bit parity pair records the same marginal face with two
different joint supports.

The source occurrence remains an explicit parameter throughout.  A marginal is a declared scalar
receiver of the complete packet; the joint face is `Set.range` of the full packet map.  This is an
exact receiver-chart witness, not a learner, decoder, language diagnosis, or claim about a general
probabilistic model.
-/

noncomputable section

namespace Soma.Holonics.Computation.JointReceiverWitness

/-! ## Three sources and the absent componentwise-majority packet -/

abbrev Source : Type := Fin 3
abbrev BitTuple : Type := Fin 3 → Bool

/-- The three source occurrences and their complete Boolean packets: `011`, `101`, `110`. -/
def packets : Source → BitTuple :=
  ![![false, true, true], ![true, false, true], ![true, true, false]]

/-- The joint face is the set of full packets. Source multiplicity remains in `packets` and its
preimage fibres; taking the range is an explicit set-valued receiver quotient. -/
def jointFace : Set BitTuple := Set.range packets

/-- The scalar value used by the rational marginal receiver. -/
def bitValue : Bool → ℚ
  | false => 0
  | true => 1

/-- Equal source weights for the finite receiver chart. -/
def sourceWeight (_ : Source) : ℚ := 1 / 3

/-- The marginal receiver at one packet coordinate, retaining no cross-coordinate conjunction. -/
def marginal (axis : Fin 3) : ℚ :=
  ∑ source : Source, sourceWeight source * bitValue (packets source axis)

/-- The componentwise true packet proposed by strict marginal majority. -/
def componentwiseTrue : BitTuple := fun _ ↦ true

theorem packets_source_zero : packets 0 = ![false, true, true] := by
  rfl

theorem packets_source_one : packets 1 = ![true, false, true] := by
  rfl

theorem packets_source_two : packets 2 = ![true, true, false] := by
  rfl

/-- Every coordinate has exact marginal `2/3` under the three equal source weights. -/
theorem marginal_eq_two_thirds (axis : Fin 3) : marginal axis = (2 / 3 : ℚ) := by
  fin_cases axis <;>
    norm_num [marginal, sourceWeight, bitValue, packets, Fin.sum_univ_succ]

/-- The componentwise-true packet is absent from the actual joint packet range. -/
theorem componentwiseTrue_not_mem_jointFace : componentwiseTrue ∉ jointFace := by
  intro h
  rcases h with ⟨source, hsource⟩
  fin_cases source
  · have hbit := congrFun hsource (0 : Fin 3)
    norm_num [componentwiseTrue, packets] at hbit
  · have hbit := congrFun hsource (1 : Fin 3)
    norm_num [componentwiseTrue, packets] at hbit
  · have hbit := congrFun hsource (2 : Fin 3)
    change false = true at hbit
    contradiction

/-- Strict marginal majorities hold simultaneously while the proposed whole packet is absent. -/
theorem strictMarginalMajority_is_absent :
    (∀ axis, (1 / 2 : ℚ) < marginal axis) ∧ componentwiseTrue ∉ jointFace := by
  constructor
  · intro axis
    rw [marginal_eq_two_thirds]
    norm_num
  · exact componentwiseTrue_not_mem_jointFace

/-- The complete source ensemble has one entering observation in this comparison. -/
def ensembleObservation : Set.range (fun _ : Source ↦ ()) := ⟨(), ⟨0, rfl⟩⟩

/-- The joint face is exactly the shared compatible-potential image of the source ensemble. -/
theorem jointFace_is_potential :
    Soma.Holonics.Transport.ReceiverPotential.outcomes (fun _ : Source ↦ ())
      ensembleObservation packets = jointFace := by
  ext packet
  constructor
  · rintro ⟨source, hsource⟩
    exact ⟨source.1, hsource⟩
  · rintro ⟨source, hsource⟩
    exact ⟨⟨source, rfl⟩, hsource⟩

/-! ## Two parity supports with the same scalar marginals -/

abbrev PairTuple : Type := Fin 2 → Bool
abbrev PairSource : Type := Fin 2

/-- Even two-bit parity support: `00`, `11`. -/
def evenParity : PairSource → PairTuple := ![![false, false], ![true, true]]

/-- Odd two-bit parity support: `01`, `10`. -/
def oddParity : PairSource → PairTuple := ![![false, true], ![true, false]]

/-- The actual joint support of a two-bit source family. -/
def pairJointFace (family : PairSource → PairTuple) : Set PairTuple := Set.range family

/-- The equal-weight two-bit marginal receiver. -/
def pairMarginal (family : PairSource → PairTuple) (axis : Fin 2) : ℚ :=
  ∑ source : PairSource, (1 / 2 : ℚ) * bitValue (family source axis)

theorem evenParity_marginal_eq_one_half (axis : Fin 2) :
    pairMarginal evenParity axis = (1 / 2 : ℚ) := by
  fin_cases axis <;>
    norm_num [pairMarginal, evenParity, bitValue, Fin.sum_univ_succ]

theorem oddParity_marginal_eq_one_half (axis : Fin 2) :
    pairMarginal oddParity axis = (1 / 2 : ℚ) := by
  fin_cases axis <;>
    norm_num [pairMarginal, oddParity, bitValue, Fin.sum_univ_succ]

/-- The even and odd parity supports have exactly the same marginal face. -/
theorem parity_marginals_agree (axis : Fin 2) :
    pairMarginal evenParity axis = pairMarginal oddParity axis := by
  rw [evenParity_marginal_eq_one_half, oddParity_marginal_eq_one_half]

/-- The two parity source families have different full joint supports. -/
theorem parity_jointFaces_differ : pairJointFace evenParity ≠ pairJointFace oddParity := by
  intro h
  have heven : (![false, false] : PairTuple) ∈ pairJointFace evenParity := by
    refine ⟨0, ?_⟩
    rfl
  rw [h] at heven
  rcases heven with ⟨source, hsource⟩
  fin_cases source <;>
    simp [oddParity] at hsource

/-! ## Source-fibre exposure -/

/-- Every source occurrence is retained behind the full joint face as a range witness. -/
theorem source_mem_jointFace (source : Source) : packets source ∈ jointFace :=
  ⟨source, rfl⟩

end Soma.Holonics.Computation.JointReceiverWitness

section Audit

open Soma.Holonics.Computation.JointReceiverWitness

#print axioms marginal_eq_two_thirds
#print axioms strictMarginalMajority_is_absent
#print axioms jointFace_is_potential
#print axioms componentwiseTrue_not_mem_jointFace
#print axioms parity_marginals_agree
#print axioms parity_jointFaces_differ
#print axioms source_mem_jointFace

end Audit

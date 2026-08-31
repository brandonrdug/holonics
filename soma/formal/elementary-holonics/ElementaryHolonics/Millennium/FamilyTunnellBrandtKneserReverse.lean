import ElementaryHolonics.Millennium.FamilyTunnellBrandtDistinctNeighbors
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex

/-!
# The ordinary two-class Kneser reverse fiber

For each fixed source class, a normalized isotropic direction produces one
actual rational neighbor.  The retained fractional generator makes this map
injective.  This file packages the resulting outgoing population and its
reverse incidence fiber without assigning a destination class: the latter is
the still-open Jones--Pall classification edge.

The exact common-index and determinant receipts are returned alongside the
population.  In particular, both relative indices are `p`, the actual full
Gram determinant is `512`, and the exact covolume-square pullback formula is
retained rather than collapsed to its scalar consequence.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtKneserReverse

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborDiscriminant
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
open Soma.Holonics.Millennium.FamilyTunnellBrandtDistinctNeighbors

variable {p : ℕ} [Fact p.Prime]

/-! ## First source class -/

def firstNeighborPopulation (hp2 : p ≠ 2) :
    Finset (AddSubgroup RatTriple) := by
  classical
  exact Finset.univ.image (fun d : FirstBrandtDirection (p := p) =>
    integralNeighbor (p := p) 32 d)

def firstNeighborIncidence (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) (N : AddSubgroup RatTriple) : Prop :=
  N = integralNeighbor (p := p) 32 d

theorem firstNeighborPopulation_card (hp2 : p ≠ 2) :
    (firstNeighborPopulation (p := p) hp2).card = p + 1 := by
  classical
  rw [firstNeighborPopulation, Finset.card_image_iff.mpr]
  · exact firstBrandtDirection_card (p := p) hp2
  · intro d hd e he hde
    exact (integralNeighbor_eq_iff_projectiveDirection_eq
      (p := p) hp2 32 d e).mp hde

theorem firstNeighborIncidence_reverse_unique (hp2 : p ≠ 2)
    {N : AddSubgroup RatTriple}
    {d e : FirstBrandtDirection (p := p)}
    (hd : firstNeighborIncidence (p := p) hp2 d N)
    (he : firstNeighborIncidence (p := p) hp2 e N) :
    d = e := by
  apply (integralNeighbor_eq_iff_projectiveDirection_eq
    (p := p) hp2 32 d e).mp
  exact (show integralNeighbor (p := p) 32 d = N from hd.symm).trans he

theorem firstNeighborPopulation_mem_iff (hp2 : p ≠ 2)
    (N : AddSubgroup RatTriple) :
    N ∈ firstNeighborPopulation (p := p) hp2 ↔
      ∃ d : FirstBrandtDirection (p := p),
        firstNeighborIncidence (p := p) hp2 d N := by
  classical
  constructor
  · intro hN
    rw [firstNeighborPopulation, Finset.mem_image] at hN
    rcases hN with ⟨d, hd, rfl⟩
    exact ⟨d, rfl⟩
  · rintro ⟨d, hd⟩
    rw [firstNeighborPopulation, Finset.mem_image]
    exact ⟨d, Finset.mem_univ _, hd.symm⟩

theorem firstNeighbor_exact_gate_receipt (hp2 : p ≠ 2)
    (d : FirstBrandtDirection (p := p)) :
    ambientNeighborPolarCore (p := p) hp2 (.inl d) =
        sourcePolarCore (p := p) hp2 (.inl d) ∧
      (sourcePolarCore (p := p) hp2 (.inl d)).relIndex sourceIntegralLattice = p ∧
      (sourcePolarCore (p := p) hp2 (.inl d)).relIndex
        (occurrenceNeighborSubgroup hp2 (.inl d)) = p ∧
      (occurrenceQuotientFullGram hp2 (.inl d)
        (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
          hp2 (.inl d))).det = 512 ∧
      ((((occurrenceQuotientFullGram hp2 (.inl d)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (.inl d))).det : ℤ) : ℚ)) =
        512 * (occurrenceBasisCoordinateMatrix (p := p) hp2 (.inl d)).det ^ 2 := by
  have hcore := ambientNeighborPolarCore_eq_sourcePolarCore (p := p) hp2 (.inl d)
  exact ⟨hcore,
    sourcePolarCore_relIndex_sourceIntegralLattice (p := p) hp2 (.inl d),
    by rw [← hcore]; exact ambientNeighborPolarCore_relIndex_neighbor (p := p) hp2 (.inl d),
    FamilyTunnellBrandtNeighborCommonIndex.occurrenceFullGram_det_eq_512
      (p := p) hp2 (.inl d),
    occurrenceFullGram_det_eq_source_det_mul_covolume_sq (p := p) hp2 (.inl d)⟩

/-! ## Second source class -/

def secondNeighborPopulation (hp2 : p ≠ 2) :
    Finset (AddSubgroup RatTriple) := by
  classical
  exact Finset.univ.image (fun d : SecondBrandtDirection (p := p) =>
    brandtSecondIntegralNeighbor (p := p) hp2 d)

def secondNeighborIncidence (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) (N : AddSubgroup RatTriple) : Prop :=
  N = brandtSecondIntegralNeighbor (p := p) hp2 d

theorem secondNeighborPopulation_card (hp2 : p ≠ 2) :
    (secondNeighborPopulation (p := p) hp2).card = p + 1 := by
  classical
  rw [secondNeighborPopulation, Finset.card_image_iff.mpr]
  · exact secondBrandtDirection_card (p := p) hp2
  · intro d hd e he hde
    exact (brandtSecondIntegralNeighbor_eq_iff_projectiveDirection_eq
      (p := p) hp2 d e).mp hde

theorem secondNeighborIncidence_reverse_unique (hp2 : p ≠ 2)
    {N : AddSubgroup RatTriple}
    {d e : SecondBrandtDirection (p := p)}
    (hd : secondNeighborIncidence (p := p) hp2 d N)
    (he : secondNeighborIncidence (p := p) hp2 e N) :
    d = e := by
  apply (brandtSecondIntegralNeighbor_eq_iff_projectiveDirection_eq
    (p := p) hp2 d e).mp
  exact (show brandtSecondIntegralNeighbor (p := p) hp2 d = N from hd.symm).trans he

theorem secondNeighborPopulation_mem_iff (hp2 : p ≠ 2)
    (N : AddSubgroup RatTriple) :
    N ∈ secondNeighborPopulation (p := p) hp2 ↔
      ∃ d : SecondBrandtDirection (p := p),
        secondNeighborIncidence (p := p) hp2 d N := by
  classical
  constructor
  · intro hN
    rw [secondNeighborPopulation, Finset.mem_image] at hN
    rcases hN with ⟨d, hd, rfl⟩
    exact ⟨d, rfl⟩
  · rintro ⟨d, hd⟩
    rw [secondNeighborPopulation, Finset.mem_image]
    exact ⟨d, Finset.mem_univ _, hd.symm⟩

theorem secondNeighbor_exact_gate_receipt (hp2 : p ≠ 2)
    (d : SecondBrandtDirection (p := p)) :
    ambientNeighborPolarCore (p := p) hp2 (.inr d) =
        sourcePolarCore (p := p) hp2 (.inr d) ∧
      (sourcePolarCore (p := p) hp2 (.inr d)).relIndex sourceIntegralLattice = p ∧
      (sourcePolarCore (p := p) hp2 (.inr d)).relIndex
        (occurrenceNeighborSubgroup hp2 (.inr d)) = p ∧
      (occurrenceQuotientFullGram hp2 (.inr d)
        (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
          hp2 (.inr d))).det = 512 ∧
      ((((occurrenceQuotientFullGram hp2 (.inr d)
          (FamilyTunnellBrandtNeighborDiscriminant.occurrenceQuotientRankThreeBasis
            hp2 (.inr d))).det : ℤ) : ℚ)) =
        512 * (occurrenceBasisCoordinateMatrix (p := p) hp2 (.inr d)).det ^ 2 := by
  have hcore := ambientNeighborPolarCore_eq_sourcePolarCore (p := p) hp2 (.inr d)
  exact ⟨hcore,
    sourcePolarCore_relIndex_sourceIntegralLattice (p := p) hp2 (.inr d),
    by rw [← hcore]; exact ambientNeighborPolarCore_relIndex_neighbor (p := p) hp2 (.inr d),
    FamilyTunnellBrandtNeighborCommonIndex.occurrenceFullGram_det_eq_512
      (p := p) hp2 (.inr d),
    occurrenceFullGram_det_eq_source_det_mul_covolume_sq (p := p) hp2 (.inr d)⟩

#print axioms firstNeighborPopulation_card
#print axioms firstNeighborIncidence_reverse_unique
#print axioms firstNeighborPopulation_mem_iff
#print axioms firstNeighbor_exact_gate_receipt
#print axioms secondNeighborPopulation_card
#print axioms secondNeighborIncidence_reverse_unique
#print axioms secondNeighborPopulation_mem_iff
#print axioms secondNeighbor_exact_gate_receipt

end Soma.Holonics.Millennium.FamilyTunnellBrandtKneserReverse

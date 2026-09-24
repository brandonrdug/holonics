import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
import ElementaryHolonics.Millennium.FamilyTunnellBrandtModFourReceiver
import ElementaryHolonics.Millennium.FamilyTunnellBrandtLocalizeAtPrime
import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicCarrierImage

/-!
# The unconditional Jones--Pall input carried by an actual Brandt neighbor

The actual odd-prime neighbor now carries all of the source-independent
arithmetic needed before a genus classification: an integral positive-definite
rank-three quadratic receiver and full-polar determinant `512`.  Its complete
mod-four representation profile is the source profile, so it cannot be the
third determinant-`64` class `x^2 + y^2 + 64z^2`.

This file makes that last statement at the level required by destination
classification: there is no equivalence from the actual quotient carrier to
`IntTriple` which transports its quadratic receiver to the third form.  No
destination label or genus classifier is assumed.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtJonesPallReduction

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationClassification
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationReduction
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborGram
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtModFourReceiver
open Soma.Holonics.Millennium.FamilyTunnellBrandtLocalizeAtPrime
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicCarrierImage

variable {p : ℕ} [Fact p.Prime]

/-- The exact cyclic quotient carrying the actual returned neighbor. -/
abbrev OccurrenceCarrier (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :=
  NeighborCoordinates ⧸ AddSubgroup.zmultiples
    (occurrenceRelationGenerator hp2 occurrence)

/-- The exhibited third determinant-`64` class is not an integral destination
of any actual odd-prime Brandt neighbor.  The obstruction is the represented
residue `3 mod 4`, transported from the source through the actual neighbor
passage. -/
theorem occurrence_not_brandtThird_receiver_equivalent (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ¬ ∃ e : OccurrenceCarrier hp2 occurrence ≃ IntTriple,
      ∀ x : OccurrenceCarrier hp2 occurrence,
        occurrenceQuotientQuadratic hp2 occurrence x =
          (brandtThirdQuadratic (e x) : ℚ) := by
  rintro ⟨e, he⟩
  rcases (occurrenceNeighbor_represents_three_and_third_cannot hp2 occurrence).1 with
    ⟨y, N, hyQ, hyMod⟩
  let x : OccurrenceCarrier hp2 occurrence :=
    (occurrenceQuotientEquivNeighbor hp2 occurrence).symm y
  have hxQ : occurrenceQuotientQuadratic hp2 occurrence x = (N : ℚ) := by
    simpa [x, occurrenceQuotientQuadratic] using hyQ
  have hN : N = brandtThirdQuadratic (e x) := by
    exact_mod_cast hxQ.symm.trans (he x)
  have hthird := brandtThird_cannot_represent_three_mod_four (e x)
  apply hthird
  rw [← hN]
  simpa using hyMod

/-- The complete source-specific local passage used by the Jones--Pall
classifier.  Away from the defining prime the source and neighbor agree after
inverting `p`; at the defining prime the explicit polar-form isometry maps the
completed source carrier onto the completed actual-neighbor carrier. -/
theorem occurrence_jonesPall_local_genus_passage (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (∀ x : RatTriple,
      primePowerSaturation (p := p) sourceIntegralLattice x ↔
        primePowerSaturation (p := p)
          (occurrenceNeighborSubgroup hp2 occurrence) x) ∧
    (∀ x y : PadicFieldTriple (p := p),
      occurrencePadicFieldPolar occurrence
        (occurrenceDefiningPrimeIsometry hp2 occurrence x)
        (occurrenceDefiningPrimeIsometry hp2 occurrence y) =
          occurrencePadicFieldPolar occurrence x y) ∧
    completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) =
      completedOccurrenceNeighborLattice hp2 occurrence ∧
    (∀ r : ℤ, SourceRepresentsModSixteen occurrence r ↔
      NeighborRepresentsModSixteen hp2 occurrence r) := by
  exact ⟨primePowerSaturation_source_iff_neighbor hp2 occurrence,
    occurrenceDefiningPrimeIsometry_preserves_form hp2 occurrence,
    definingPrimeIsometry_completedSource_eq_completedNeighbor hp2 occurrence,
    source_neighbor_mod_sixteen_profile_equivalence hp2 occurrence⟩

/-- The exact source-specific reduction packet available to the next
Jones--Pall step.  It simultaneously retains determinant, integrality,
positive definiteness, and the first excluded global class. -/
theorem occurrence_jonesPall_input_packet (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceQuotientFullGram hp2 occurrence
      (occurrenceQuotientRankThreeBasis hp2 occurrence)).det = 512 ∧
    (∀ x : OccurrenceCarrier hp2 occurrence,
      ∃ N : ℤ, occurrenceQuotientQuadratic hp2 occurrence x = (N : ℚ)) ∧
    (∀ x : OccurrenceCarrier hp2 occurrence,
      0 ≤ occurrenceQuotientQuadratic hp2 occurrence x) ∧
    (∀ x : OccurrenceCarrier hp2 occurrence,
      occurrenceQuotientQuadratic hp2 occurrence x = 0 ↔ x = 0) ∧
    ¬ ∃ e : OccurrenceCarrier hp2 occurrence ≃ IntTriple,
      ∀ x : OccurrenceCarrier hp2 occurrence,
        occurrenceQuotientQuadratic hp2 occurrence x =
          (brandtThirdQuadratic (e x) : ℚ) := by
  exact ⟨occurrenceFullGram_det_eq_512 hp2 occurrence,
    occurrenceQuotientQuadratic_is_integer hp2 occurrence,
    occurrenceQuotientQuadratic_nonnegative hp2 occurrence,
    occurrenceQuotientQuadratic_eq_zero_iff hp2 occurrence,
    occurrence_not_brandtThird_receiver_equivalent hp2 occurrence⟩

#print axioms occurrence_not_brandtThird_receiver_equivalent
#print axioms occurrence_jonesPall_local_genus_passage
#print axioms occurrence_jonesPall_input_packet

end Soma.Holonics.Millennium.FamilyTunnellBrandtJonesPallReduction

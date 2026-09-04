import ElementaryHolonics.Millennium.FamilyTunnellBrandtLocalReflection
import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift

/-!
# The source-specific hyperbolic pair at the defining Brandt prime

The exact isotropic lift is promoted from `ℤ_p^3` to `ℚ_p^3`.  Its retained
integral polar witness still pairs by a `p`-adic unit.  Normalizing that
partner and applying the generic isotropic correction produces a hyperbolic
pair `(e,f)`.  Reciprocal scaling then gives the actual ambient isometry

`e ↦ p⁻¹e`, `f ↦ p f`,

while fixing the orthogonal remainder.  The remaining lattice gate is only
to identify the completed source and occurrence lattices with the two spans
selected by this already-constructed isometry.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift
open Soma.Holonics.Millennium.FamilyTunnellBrandtLocalReflection

variable {p : ℕ} [Fact p.Prime]

abbrev PadicFieldTriple := ℚ_[p] × ℚ_[p] × ℚ_[p]

def padicTripleToField (v : PadicTriple (p := p)) : PadicFieldTriple (p := p) :=
  ((v.1 : ℚ_[p]), (v.2.1 : ℚ_[p]), (v.2.2 : ℚ_[p]))

def occurrencePadicFieldQuadratic
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : PadicFieldTriple (p := p)) : ℚ_[p] :=
  match occurrence with
  | .inl _ => 2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2
  | .inr _ =>
      2 * v.1 ^ 2 + 4 * v.2.1 ^ 2 + 4 * v.2.1 * v.2.2 + 9 * v.2.2 ^ 2

/-- The source full-polar form over the completed fraction field. -/
def occurrencePadicFieldPolar
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    LinearMap.BilinForm ℚ_[p] (PadicFieldTriple (p := p)) :=
  LinearMap.mk₂ ℚ_[p]
    (fun u v => match occurrence with
      | .inl _ => 4 * u.1 * v.1 + 2 * u.2.1 * v.2.1 + 64 * u.2.2 * v.2.2
      | .inr _ =>
          4 * u.1 * v.1 + 8 * u.2.1 * v.2.1 +
            4 * (u.2.1 * v.2.2 + u.2.2 * v.2.1) + 18 * u.2.2 * v.2.2)
    (by intros; cases occurrence <;> simp <;> ring)
    (by intros; cases occurrence <;> simp [smul_eq_mul] <;> ring)
    (by intros; cases occurrence <;> simp <;> ring)
    (by intros; cases occurrence <;> simp [smul_eq_mul] <;> ring)

@[simp]
theorem occurrencePadicFieldPolar_apply
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicFieldTriple (p := p)) :
    occurrencePadicFieldPolar occurrence u v =
      match occurrence with
      | .inl _ => 4 * u.1 * v.1 + 2 * u.2.1 * v.2.1 + 64 * u.2.2 * v.2.2
      | .inr _ =>
          4 * u.1 * v.1 + 8 * u.2.1 * v.2.1 +
            4 * (u.2.1 * v.2.2 + u.2.2 * v.2.1) +
              18 * u.2.2 * v.2.2 := rfl

theorem occurrencePadicFieldPolar_symmetric
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicFieldTriple (p := p)) :
    occurrencePadicFieldPolar occurrence u v =
      occurrencePadicFieldPolar occurrence v u := by
  cases occurrence <;> simp <;> ring

theorem occurrencePadicFieldPolar_self
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : PadicFieldTriple (p := p)) :
    occurrencePadicFieldPolar occurrence v v =
      2 * occurrencePadicFieldQuadratic occurrence v := by
  cases occurrence <;>
    simp [occurrencePadicFieldQuadratic] <;> ring

theorem occurrencePadicFieldQuadratic_cast
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : PadicTriple (p := p)) :
    occurrencePadicFieldQuadratic occurrence (padicTripleToField v) =
      (occurrencePadicQuadratic occurrence v : ℚ_[p]) := by
  cases occurrence <;>
    norm_num [occurrencePadicFieldQuadratic, occurrencePadicQuadratic,
      padicTripleToField] <;> norm_cast

theorem occurrencePadicFieldPolar_cast
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicTriple (p := p)) :
    occurrencePadicFieldPolar occurrence
        (padicTripleToField u) (padicTripleToField v) =
      (occurrencePadicPolar occurrence u v : ℚ_[p]) := by
  cases occurrence <;>
    norm_num [occurrencePadicFieldPolar, occurrencePadicPolar,
      padicTripleToField] <;> norm_cast

def occurrencePadicIsotropicVector (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) :=
  padicTripleToField (occurrenceExactIsotropicLift hp2 occurrence)

def occurrencePadicWitnessVector (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) :=
  padicTripleToField
    (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence))

theorem occurrencePadicIsotropicVector_isotropic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrencePadicIsotropicVector hp2 occurrence)
      (occurrencePadicIsotropicVector hp2 occurrence) = 0 := by
  rw [occurrencePadicFieldPolar_self, occurrencePadicIsotropicVector,
    occurrencePadicFieldQuadratic_cast,
    occurrenceExactIsotropicLift_quadratic_eq_zero]
  norm_num

/-- The corrected isotropic line still pairs with its original partner by a
unit of `ℤ_p`; the correction term lies strictly inside the maximal ideal. -/
theorem occurrenceExactLift_polar_witness_norm_eq_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ‖occurrencePadicPolar occurrence
      (occurrenceExactIsotropicLift hp2 occurrence)
      (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence))‖ = 1 := by
  let b := occurrenceUnitPolarCoefficient hp2 occurrence
  let c := occurrenceIntegralQuadratic occurrence
    (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let delta : ℤ_[p] := (s * (2 * (c : ℤ_[p]))) * (p : ℤ_[p])
  have hb : ‖(b : ℤ_[p])‖ = 1 :=
    norm_intCast_eq_one_of_not_dvd b
      (prime_not_dvd_occurrenceUnitPolarCoefficient hp2 occurrence)
  have hpNorm : ‖(p : ℤ_[p])‖ < 1 :=
    PadicInt.norm_natCast_lt_one_iff.mpr dvd_rfl
  have hdelta : ‖delta‖ < 1 := by
    exact PadicInt.norm_lt_one_mul hpNorm
  have hne : ‖(b : ℤ_[p])‖ ≠ ‖delta‖ := by
    rw [hb]
    exact (ne_of_lt hdelta).symm
  have hsum : ‖(b : ℤ_[p]) + delta‖ = 1 := by
    rw [PadicInt.norm_add_eq_max_of_ne hne, hb]
    exact max_eq_left (le_of_lt hdelta)
  rw [occurrenceExactIsotropicLift]
  have hformula :
      occurrencePadicPolar occurrence
        (intTripleToPadic (occurrenceDirectionLift hp2 occurrence) +
          ((p : ℤ_[p]) * s) •
            intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence))
        (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)) =
          (b : ℤ_[p]) + delta := by
    rw [occurrencePadicPolar_add_left,
      occurrencePadicPolar_smul_left,
      occurrencePadicPolar_intCast,
      occurrencePadicPolar_self,
      occurrencePadicQuadratic_intCast]
    simp only [occurrenceUnitPolarCoefficient, b, c, delta, s]
    ring
  rw [hformula]
  exact hsum

theorem occurrencePadicPairing_ne_zero (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrencePadicIsotropicVector hp2 occurrence)
      (occurrencePadicWitnessVector hp2 occurrence) ≠ 0 := by
  rw [occurrencePadicIsotropicVector, occurrencePadicWitnessVector,
    occurrencePadicFieldPolar_cast]
  intro hzero
  have hzeroInt : occurrencePadicPolar occurrence
      (occurrenceExactIsotropicLift hp2 occurrence)
      (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)) = 0 := by
    exact Subtype.coe_injective hzero
  have hnorm := occurrenceExactLift_polar_witness_norm_eq_one hp2 occurrence
  rw [hzeroInt, norm_zero] at hnorm
  norm_num at hnorm

/-- Normalize the retained partner to polar pairing one. -/
def occurrenceNormalizedPartner (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) :=
  (occurrencePadicFieldPolar occurrence
    (occurrencePadicIsotropicVector hp2 occurrence)
    (occurrencePadicWitnessVector hp2 occurrence))⁻¹ •
      occurrencePadicWitnessVector hp2 occurrence

theorem occurrenceNormalizedPartner_pairing (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrencePadicIsotropicVector hp2 occurrence)
      (occurrenceNormalizedPartner hp2 occurrence) = 1 := by
  rw [occurrenceNormalizedPartner, map_smul]
  simp only [smul_eq_mul]
  exact inv_mul_cancel₀ (occurrencePadicPairing_ne_zero hp2 occurrence)

/-- The corrected partner is isotropic while retaining pairing one. -/
def occurrenceIsotropicPartner (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) :=
  correctedIsotropicPartner (occurrencePadicFieldPolar occurrence)
    (occurrencePadicIsotropicVector hp2 occurrence)
    (occurrenceNormalizedPartner hp2 occurrence)

theorem occurrenceIsotropicPartner_pairing (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrencePadicIsotropicVector hp2 occurrence)
      (occurrenceIsotropicPartner hp2 occurrence) = 1 := by
  exact correctedIsotropicPartner_pairing
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceNormalizedPartner_pairing hp2 occurrence)

theorem occurrenceIsotropicPartner_isotropic (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrenceIsotropicPartner hp2 occurrence)
      (occurrenceIsotropicPartner hp2 occurrence) = 0 := by
  exact correctedIsotropicPartner_isotropic
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence)
    (by norm_num)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceNormalizedPartner_pairing hp2 occurrence)

/-- The actual defining-prime ambient isometry. -/
def occurrenceDefiningPrimeIsometry (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) ≃ₗ[ℚ_[p]] PadicFieldTriple (p := p) :=
  hyperbolicScaleEquiv
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence)
    (occurrencePadicIsotropicVector hp2 occurrence)
    (occurrenceIsotropicPartner hp2 occurrence)
    (p : ℚ_[p])
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_pairing hp2 occurrence)

theorem occurrenceDefiningPrimeIsometry_preserves_form (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x y : PadicFieldTriple (p := p)) :
    occurrencePadicFieldPolar occurrence
      (occurrenceDefiningPrimeIsometry hp2 occurrence x)
      (occurrenceDefiningPrimeIsometry hp2 occurrence y) =
        occurrencePadicFieldPolar occurrence x y := by
  exact hyperbolicScaleEquiv_preserves_form
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_pairing hp2 occurrence) x y

theorem occurrenceDefiningPrimeIsometry_isotropic_direction (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceDefiningPrimeIsometry hp2 occurrence
      (occurrencePadicIsotropicVector hp2 occurrence) =
        ((p : ℚ_[p])⁻¹) • occurrencePadicIsotropicVector hp2 occurrence := by
  exact hyperbolicScaleEquiv_e
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_pairing hp2 occurrence)

theorem occurrenceDefiningPrimeIsometry_partner (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceDefiningPrimeIsometry hp2 occurrence
      (occurrenceIsotropicPartner hp2 occurrence) =
        (p : ℚ_[p]) • occurrenceIsotropicPartner hp2 occurrence := by
  exact hyperbolicScaleEquiv_f
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence)
    (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    (occurrencePadicIsotropicVector_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_isotropic hp2 occurrence)
    (occurrenceIsotropicPartner_pairing hp2 occurrence)

#print axioms occurrenceExactLift_polar_witness_norm_eq_one
#print axioms occurrencePadicPairing_ne_zero
#print axioms occurrenceIsotropicPartner_isotropic
#print axioms occurrenceDefiningPrimeIsometry_preserves_form
#print axioms occurrenceDefiningPrimeIsometry_isotropic_direction
#print axioms occurrenceDefiningPrimeIsometry_partner

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair

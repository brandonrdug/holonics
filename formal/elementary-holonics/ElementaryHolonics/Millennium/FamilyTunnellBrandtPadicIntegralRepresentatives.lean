import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair

/-!
# Integral representatives of the source-specific hyperbolic partner

The norm-one polar pairing is a unit of `ℤ_p`, by `PadicInt.isUnit_iff`.
Consequently the normalized partner has an integral `ℤ_p^3` representative.
For `p ≠ 2`, the scalar two is also a unit, so the isotropic correction of
that partner remains integral.  The field-level cast identities are exact.
This owner does not assert a lattice-genus or local-isometry conclusion.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIntegralRepresentatives

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel
open Soma.Holonics.Millennium.FamilyTunnellBrandtLocalReflection

variable {p : ℕ} [Fact p.Prime]

private theorem two_not_dvd (hp2 : p ≠ 2) : ¬(p : ℤ) ∣ 2 := by
  intro h
  have hNat : p ∣ (2 : ℕ) := by simpa [Int.natCast_dvd] using h
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hNat
  have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
  exact hp2 (Nat.le_antisymm hle hge)

private theorem two_isUnit (hp2 : p ≠ 2) : IsUnit (2 : ℤ_[p]) := by
  apply PadicInt.isUnit_iff.mpr
  exact norm_intCast_eq_one_of_not_dvd (p := p) 2 (two_not_dvd (p := p) hp2)

private theorem padicInt_inv_cast_of_isUnit {z : ℤ_[p]} (hz : IsUnit z) :
    ((z.inv : ℤ_[p]) : ℚ_[p]) = ((z : ℚ_[p]))⁻¹ := by
  have hz0 : z ≠ 0 := by
    intro h
    exact not_isUnit_zero (h ▸ hz)
  apply mul_left_cancel₀ ((PadicInt.coe_ne_zero).2 hz0)
  calc
    (z : ℚ_[p]) * (z.inv : ℚ_[p]) = ((z * z.inv : ℤ_[p]) : ℚ_[p]) := by simp
    _ = 1 := by rw [PadicInt.mul_inv (PadicInt.isUnit_iff.mp hz)]; norm_num
    _ = (z : ℚ_[p]) * (z : ℚ_[p])⁻¹ := by
      rw [mul_inv_cancel₀ ((PadicInt.coe_ne_zero).2 hz0)]

private theorem padicInt_mul_twoInv_cast (a : ℤ_[p]) (hp2 : p ≠ 2) :
    ((a * (2 : ℤ_[p]).inv : ℤ_[p]) : ℚ_[p]) =
      (a : ℚ_[p]) / (2 : ℚ_[p]) := by
  calc
    ((a * (2 : ℤ_[p]).inv : ℤ_[p]) : ℚ_[p]) =
        (a : ℚ_[p]) * ((2 : ℤ_[p]).inv : ℚ_[p]) := by simp
    _ = (a : ℚ_[p]) * (2 : ℚ_[p])⁻¹ := by
      congr 1
      exact padicInt_inv_cast_of_isUnit (two_isUnit (p := p) hp2)
    _ = (a : ℚ_[p]) / (2 : ℚ_[p]) := by rw [div_eq_mul_inv]

private theorem padicTripleToField_add (u v : PadicTriple (p := p)) :
    padicTripleToField (u + v) =
      padicTripleToField u + padicTripleToField v := by
  ext <;> simp [padicTripleToField]

private theorem padicTripleToField_sub (u v : PadicTriple (p := p)) :
    padicTripleToField (u - v) =
      padicTripleToField u - padicTripleToField v := by
  ext <;> simp [padicTripleToField]

private theorem padicTripleToField_smul (a : ℤ_[p]) (v : PadicTriple (p := p)) :
    padicTripleToField (a • v) =
      (a : ℚ_[p]) • padicTripleToField v := by
  ext <;> simp [padicTripleToField, Algebra.smul_def]

def integralPairingCoefficient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : ℤ_[p] :=
  occurrencePadicPolar occurrence
    (occurrenceExactIsotropicLift hp2 occurrence)
    (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence))

theorem integralPairingCoefficient_norm (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ‖integralPairingCoefficient hp2 occurrence‖ = 1 :=
  occurrenceExactLift_polar_witness_norm_eq_one hp2 occurrence

theorem integralPairingCoefficient_isUnit (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    IsUnit (integralPairingCoefficient hp2 occurrence) := by
  apply PadicInt.isUnit_iff.mpr
  exact integralPairingCoefficient_norm hp2 occurrence

def normalizedPartnerIntegral (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicTriple (p := p) :=
  (integralPairingCoefficient hp2 occurrence).inv •
    intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)

theorem normalizedPartnerIntegral_cast (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    padicTripleToField (normalizedPartnerIntegral hp2 occurrence) =
      occurrenceNormalizedPartner hp2 occurrence := by
  rw [normalizedPartnerIntegral, occurrenceNormalizedPartner,
    occurrencePadicIsotropicVector, occurrencePadicWitnessVector,
    occurrencePadicFieldPolar_cast, padicTripleToField_smul]
  have hinv :
      ((integralPairingCoefficient hp2 occurrence).inv : ℚ_[p]) =
        ((occurrencePadicPolar occurrence
          (occurrenceExactIsotropicLift hp2 occurrence)
          (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)) :
            ℚ_[p]))⁻¹ := by
    simpa [integralPairingCoefficient] using
      (padicInt_inv_cast_of_isUnit
        (integralPairingCoefficient_isUnit hp2 occurrence))
  rw [hinv]

def isotropicPartnerIntegral (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicTriple (p := p) :=
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := normalizedPartnerIntegral hp2 occurrence
  f - (occurrencePadicPolar occurrence f f * (2 : ℤ_[p]).inv) • e

theorem isotropicPartnerIntegral_cast (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    padicTripleToField (isotropicPartnerIntegral hp2 occurrence) =
      occurrenceIsotropicPartner hp2 occurrence := by
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := normalizedPartnerIntegral hp2 occurrence
  let a := occurrencePadicPolar occurrence f f
  have hf : padicTripleToField f = occurrenceNormalizedPartner hp2 occurrence :=
    normalizedPartnerIntegral_cast hp2 occurrence
  have he : padicTripleToField e = occurrencePadicIsotropicVector hp2 occurrence := rfl
  have hpolar :
      occurrencePadicFieldPolar occurrence (padicTripleToField f)
          (padicTripleToField f) = (a : ℚ_[p]) := by
    exact occurrencePadicFieldPolar_cast occurrence f f
  have hpolar' :
      occurrencePadicFieldPolar occurrence
          (occurrenceNormalizedPartner hp2 occurrence)
          (occurrenceNormalizedPartner hp2 occurrence) = (a : ℚ_[p]) := by
    rw [← hf]
    exact hpolar
  change padicTripleToField
      (f - (a * (2 : ℤ_[p]).inv) • e) =
    occurrenceNormalizedPartner hp2 occurrence -
      (occurrencePadicFieldPolar occurrence
          (occurrenceNormalizedPartner hp2 occurrence)
          (occurrenceNormalizedPartner hp2 occurrence) / (2 : ℚ_[p])) •
        occurrencePadicIsotropicVector hp2 occurrence
  rw [padicTripleToField_sub, padicTripleToField_smul, hf, he, hpolar',
    padicInt_mul_twoInv_cast (p := p) a hp2]

#print axioms integralPairingCoefficient_isUnit
#print axioms normalizedPartnerIntegral_cast
#print axioms isotropicPartnerIntegral_cast

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIntegralRepresentatives

import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicHensel

/-!
# Exact isotropic lifting at the defining Brandt prime

Every actual Brandt occurrence already retains an integral direction `v`
whose norm is divisible by `p^2`, and its polar residue functional is onto.
Choose an integral partner `w` with polar residue one.  The scalar Hensel
turn from `FamilyTunnellBrandtPadicHensel` then returns `s ∈ ℤ_p` such that

`e = v + p*s*w`

is exactly isotropic.  Since `e ≡ v (mod p)`, this is the source-faithful
isotropic line needed by the defining-prime neighbor isometry.  No
destination class or local-isometry conclusion is assumed here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel

variable {p : ℕ} [Fact p.Prime]

abbrev PadicTriple := ℤ_[p] × ℤ_[p] × ℤ_[p]

def intTripleToPadic (v : IntTriple) : PadicTriple (p := p) :=
  ((v.1 : ℤ_[p]), (v.2.1 : ℤ_[p]), (v.2.2 : ℤ_[p]))

/-- The retained source quadratic form before completion. -/
def occurrenceIntegralQuadratic
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) : ℤ :=
  match occurrence with
  | .inl _ => intTunnellQuadratic 32 v
  | .inr _ => brandtSecondQuadratic v

/-- Its full polar pairing. -/
def occurrenceIntegralPolar
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : IntTriple) : ℤ :=
  match occurrence with
  | .inl _ => intTunnellPolar 32 u v
  | .inr _ => brandtSecondPolar u v

theorem occurrenceIntegralPolar_comm
    (occurrence : BrandtNeighborOccurrence (p := p)) (u v : IntTriple) :
    occurrenceIntegralPolar occurrence u v =
      occurrenceIntegralPolar occurrence v u := by
  cases occurrence <;>
    simp [occurrenceIntegralPolar, intTunnellPolar, brandtSecondPolar] <;> ring

/-- The completed source quadratic form on `ℤ_p^3`. -/
def occurrencePadicQuadratic
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : PadicTriple (p := p)) : ℤ_[p] :=
  match occurrence with
  | .inl _ => 2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2
  | .inr _ =>
      2 * v.1 ^ 2 + 4 * v.2.1 ^ 2 + 4 * v.2.1 * v.2.2 + 9 * v.2.2 ^ 2

/-- The completed full polar pairing. -/
def occurrencePadicPolar
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicTriple (p := p)) : ℤ_[p] :=
  match occurrence with
  | .inl _ => 4 * u.1 * v.1 + 2 * u.2.1 * v.2.1 + 64 * u.2.2 * v.2.2
  | .inr _ =>
      4 * u.1 * v.1 + 8 * u.2.1 * v.2.1 +
        4 * (u.2.1 * v.2.2 + u.2.2 * v.2.1) + 18 * u.2.2 * v.2.2

theorem occurrencePadicQuadratic_intCast
    (occurrence : BrandtNeighborOccurrence (p := p)) (v : IntTriple) :
    occurrencePadicQuadratic occurrence (intTripleToPadic v) =
      (occurrenceIntegralQuadratic occurrence v : ℤ_[p]) := by
  cases occurrence <;>
    simp [occurrencePadicQuadratic, occurrenceIntegralQuadratic,
      intTripleToPadic, intTunnellQuadratic, brandtSecondQuadratic]

theorem occurrencePadicPolar_intCast
    (occurrence : BrandtNeighborOccurrence (p := p)) (u v : IntTriple) :
    occurrencePadicPolar occurrence (intTripleToPadic u) (intTripleToPadic v) =
      (occurrenceIntegralPolar occurrence u v : ℤ_[p]) := by
  cases occurrence <;>
    simp [occurrencePadicPolar, occurrenceIntegralPolar, intTripleToPadic,
      intTunnellPolar, brandtSecondPolar] <;> ring

theorem occurrencePadicPolar_add_left
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v w : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence (u + v) w =
      occurrencePadicPolar occurrence u w +
        occurrencePadicPolar occurrence v w := by
  cases occurrence <;> simp [occurrencePadicPolar] <;> ring

theorem occurrencePadicPolar_smul_left
    (occurrence : BrandtNeighborOccurrence (p := p))
    (a : ℤ_[p]) (u v : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence (a • u) v =
      a * occurrencePadicPolar occurrence u v := by
  cases occurrence <;> simp [occurrencePadicPolar, smul_eq_mul] <;> ring

theorem occurrencePadicPolar_self
    (occurrence : BrandtNeighborOccurrence (p := p))
    (v : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence v v =
      2 * occurrencePadicQuadratic occurrence v := by
  cases occurrence <;>
    simp [occurrencePadicPolar, occurrencePadicQuadratic] <;> ring

theorem occurrencePadicQuadratic_add_smul
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicTriple (p := p)) (a : ℤ_[p]) :
    occurrencePadicQuadratic occurrence (u + a • v) =
      occurrencePadicQuadratic occurrence u +
        a * occurrencePadicPolar occurrence u v +
          a ^ 2 * occurrencePadicQuadratic occurrence v := by
  cases occurrence <;>
    simp [occurrencePadicQuadratic, occurrencePadicPolar, smul_eq_mul] <;> ring

/-- The integral source direction retains its exact `p^2` norm quotient. -/
theorem occurrenceDirection_prime_sq_dvd (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (p : ℤ) ^ 2 ∣ occurrenceIntegralQuadratic occurrence
      (occurrenceDirectionLift hp2 occurrence) := by
  cases occurrence with
  | inl d =>
      exact prime_sq_dvd_adjustedDirectionLift_norm (p := p) hp2 32 d
  | inr d =>
      exact prime_sq_dvd_adjustedBrandtSecondDirectionLift_norm (p := p) hp2 d

def occurrenceDirectionNormQuotient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : ℤ :=
  Classical.choose (occurrenceDirection_prime_sq_dvd hp2 occurrence)

theorem occurrenceDirection_norm_eq_prime_sq_mul_quotient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceIntegralQuadratic occurrence (occurrenceDirectionLift hp2 occurrence) =
      (p : ℤ) ^ 2 * occurrenceDirectionNormQuotient hp2 occurrence := by
  exact Classical.choose_spec (occurrenceDirection_prime_sq_dvd hp2 occurrence)

/-- A source integral partner whose polar pairing with the retained direction
is one modulo `p`. -/
def occurrencePolarUnitWitness (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : IntTriple :=
  Classical.choose
    (occurrencePolarResidueHom_surjective hp2 occurrence (1 : ZMod p))

theorem occurrencePolarUnitWitness_residue (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePolarResidueHom hp2 occurrence
      (occurrencePolarUnitWitness hp2 occurrence) = 1 :=
  Classical.choose_spec
    (occurrencePolarResidueHom_surjective hp2 occurrence (1 : ZMod p))

theorem occurrenceIntegralPolar_cast_residue (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (m : IntTriple) :
    (occurrenceIntegralPolar occurrence m
      (occurrenceDirectionLift hp2 occurrence) : ZMod p) =
        occurrencePolarResidueHom hp2 occurrence m := by
  cases occurrence <;>
    simp [occurrenceIntegralPolar, occurrenceDirectionLift,
      occurrencePolarResidueHom]

def occurrenceUnitPolarCoefficient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : ℤ :=
  occurrenceIntegralPolar occurrence (occurrenceDirectionLift hp2 occurrence)
    (occurrencePolarUnitWitness hp2 occurrence)

theorem prime_not_dvd_occurrenceUnitPolarCoefficient (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ¬(p : ℤ) ∣ occurrenceUnitPolarCoefficient hp2 occurrence := by
  intro hdvd
  have hz :
      (occurrenceUnitPolarCoefficient hp2 occurrence : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 hdvd
  have hone :
      (occurrenceUnitPolarCoefficient hp2 occurrence : ZMod p) = 1 := by
    rw [occurrenceUnitPolarCoefficient,
      occurrenceIntegralPolar_comm occurrence,
      occurrenceIntegralPolar_cast_residue hp2 occurrence]
    exact occurrencePolarUnitWitness_residue hp2 occurrence
  rw [hone] at hz
  exact one_ne_zero hz

def occurrenceCorrectionRoot (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : ℤ_[p] :=
  Classical.choose (exists_exact_correction
    (p := p)
    (occurrenceDirectionNormQuotient hp2 occurrence)
    (occurrenceUnitPolarCoefficient hp2 occurrence)
    (occurrenceIntegralQuadratic occurrence
      (occurrencePolarUnitWitness hp2 occurrence))
    (prime_not_dvd_occurrenceUnitPolarCoefficient hp2 occurrence))

theorem occurrenceCorrectionRoot_equation (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (correctionPolynomial
      (p := p)
      (occurrenceDirectionNormQuotient hp2 occurrence)
      (occurrenceUnitPolarCoefficient hp2 occurrence)
      (occurrenceIntegralQuadratic occurrence
        (occurrencePolarUnitWitness hp2 occurrence))).aeval
          (occurrenceCorrectionRoot hp2 occurrence) = 0 :=
  (Classical.choose_spec (exists_exact_correction
    (p := p)
    (occurrenceDirectionNormQuotient hp2 occurrence)
    (occurrenceUnitPolarCoefficient hp2 occurrence)
    (occurrenceIntegralQuadratic occurrence
      (occurrencePolarUnitWitness hp2 occurrence))
    (prime_not_dvd_occurrenceUnitPolarCoefficient hp2 occurrence))).1

theorem occurrenceCorrectionRoot_norm_lt_one (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ‖occurrenceCorrectionRoot hp2 occurrence‖ < 1 :=
  (Classical.choose_spec (exists_exact_correction
    (p := p)
    (occurrenceDirectionNormQuotient hp2 occurrence)
    (occurrenceUnitPolarCoefficient hp2 occurrence)
    (occurrenceIntegralQuadratic occurrence
      (occurrencePolarUnitWitness hp2 occurrence))
    (prime_not_dvd_occurrenceUnitPolarCoefficient hp2 occurrence))).2

/-- The exact `p`-adic isotropic lift of the retained residue direction. -/
def occurrenceExactIsotropicLift (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) : PadicTriple (p := p) :=
  intTripleToPadic (occurrenceDirectionLift hp2 occurrence) +
    ((p : ℤ_[p]) * occurrenceCorrectionRoot hp2 occurrence) •
      intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)

/-- The lifted direction is exactly isotropic, not merely isotropic to a
finite residue depth. -/
theorem occurrenceExactIsotropicLift_quadratic_eq_zero (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicQuadratic occurrence
      (occurrenceExactIsotropicLift hp2 occurrence) = 0 := by
  let q := occurrenceDirectionNormQuotient hp2 occurrence
  let b := occurrenceUnitPolarCoefficient hp2 occurrence
  let c := occurrenceIntegralQuadratic occurrence
    (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  have hroot :
      (((p : ℤ) * q : ℤ) : ℤ_[p]) + (b : ℤ_[p]) * s +
          (((p : ℤ) * c : ℤ) : ℤ_[p]) * s ^ 2 = 0 := by
    simpa [correctionPolynomial, q, b, c, s] using
      occurrenceCorrectionRoot_equation hp2 occurrence
  rw [occurrenceExactIsotropicLift,
    occurrencePadicQuadratic_add_smul]
  rw [occurrencePadicQuadratic_intCast,
    occurrencePadicPolar_intCast,
    occurrencePadicQuadratic_intCast]
  rw [occurrenceDirection_norm_eq_prime_sq_mul_quotient]
  change
    ((((p : ℤ) ^ 2 * q : ℤ) : ℤ_[p]) +
      ((p : ℤ_[p]) * s) * (b : ℤ_[p]) +
      ((p : ℤ_[p]) * s) ^ 2 * (c : ℤ_[p])) = 0
  calc
    ((((p : ℤ) ^ 2 * q : ℤ) : ℤ_[p]) +
        ((p : ℤ_[p]) * s) * (b : ℤ_[p]) +
        ((p : ℤ_[p]) * s) ^ 2 * (c : ℤ_[p])) =
      (p : ℤ_[p]) *
        ((((p : ℤ) * q : ℤ) : ℤ_[p]) + (b : ℤ_[p]) * s +
          (((p : ℤ) * c : ℤ) : ℤ_[p]) * s ^ 2) := by
            push_cast
            ring
    _ = 0 := by rw [hroot, mul_zero]

#print axioms occurrenceDirection_prime_sq_dvd
#print axioms occurrencePolarUnitWitness_residue
#print axioms prime_not_dvd_occurrenceUnitPolarCoefficient
#print axioms occurrenceCorrectionRoot_equation
#print axioms occurrenceCorrectionRoot_norm_lt_one
#print axioms occurrenceExactIsotropicLift_quadratic_eq_zero

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift

import ElementaryHolonics.Millennium.FamilyTunnellBrandtDestinationReduction
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborRankThree

/-!
# The exact two-adic receiver carried by every actual Brandt neighbor

The two Tunnell--Brandt target forms have the same complete residue profile
modulo four.  The determinant-`64` third form exhibited by destination
reduction does not: the first two forms represent residue three, whereas the
third form cannot.

More importantly, this receiver is transported by the actual odd-prime
neighbor construction.  Multiplication by `p` sends every neighbor point to
its unique integral numerator, and multiplication by `p` sends every source
integral point into the neighbor.  Since an odd prime has square congruent to
one modulo four, these two passages prove equality of the complete source and
neighbor residue profiles.  No destination-class assumption is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtModFourReceiver

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuadraticQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtDestinationReduction

variable {p : ℕ} [Fact p.Prime]

/-! ## Exact target profiles -/

/-- The first target reading has the same residue as a second-target reading
after moving its second coordinate into the third coordinate. -/
theorem brandtSecond_mod_four_of_brandtFirst (m : IntTriple) :
    brandtSecondQuadratic (m.1, 0, m.2.1) % 4 =
      brandtFirstQuadratic m % 4 := by
  apply Int.modEq_of_dvd
  change (4 : ℤ) ∣
    brandtFirstQuadratic m - brandtSecondQuadratic (m.1, 0, m.2.1)
  refine ⟨8 * m.2.2 ^ 2 - 2 * m.2.1 ^ 2, ?_⟩
  simp only [brandtFirstQuadratic, brandtSecondQuadratic]
  ring

/-- Conversely, the second target reading has the same residue as a
first-target reading after retaining its first and third coordinates. -/
theorem brandtFirst_mod_four_of_brandtSecond (m : IntTriple) :
    brandtFirstQuadratic (m.1, m.2.2, 0) % 4 =
      brandtSecondQuadratic m % 4 := by
  apply Int.modEq_of_dvd
  change (4 : ℤ) ∣
    brandtSecondQuadratic m - brandtFirstQuadratic (m.1, m.2.2, 0)
  refine ⟨m.2.1 ^ 2 + m.2.1 * m.2.2 + 2 * m.2.2 ^ 2, ?_⟩
  simp only [brandtFirstQuadratic, brandtSecondQuadratic]
  ring

/-- The two target forms have exactly the same complete representation
profile modulo four, with explicit coordinate transports in both directions. -/
theorem brandtTarget_mod_four_profiles_equivalent (r : ℤ) :
    (∃ m : IntTriple, brandtFirstQuadratic m % 4 = r % 4) ↔
      ∃ m : IntTriple, brandtSecondQuadratic m % 4 = r % 4 := by
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨(m.1, 0, m.2.1),
      (brandtSecond_mod_four_of_brandtFirst m).trans hm⟩
  · rintro ⟨m, hm⟩
    exact ⟨(m.1, m.2.2, 0),
      (brandtFirst_mod_four_of_brandtSecond m).trans hm⟩

theorem brandtFirst_represents_three_mod_four :
    ∃ m : IntTriple, brandtFirstQuadratic m % 4 = 3 := by
  exact ⟨(1, 1, 0), by norm_num [brandtFirstQuadratic]⟩

theorem brandtSecond_represents_three_mod_four :
    ∃ m : IntTriple, brandtSecondQuadratic m % 4 = 3 := by
  exact ⟨(1, 0, 1), by norm_num [brandtSecondQuadratic]⟩

private theorem int_square_emod_four (x : ℤ) :
    x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := by
  rcases x.even_or_odd with ⟨u, hu⟩ | ⟨u, hu⟩
  · left
    rw [hu, show (u + u) ^ 2 = 4 * u ^ 2 by ring]
    simp
  · right
    rw [hu, show (2 * u + 1) ^ 2 = 4 * (u ^ 2 + u) + 1 by ring]
    simp

/-- The determinant-`64` third form cannot represent residue three modulo
four.  This is an exact two-adic separator omitted by determinant and
positivity. -/
theorem brandtThird_cannot_represent_three_mod_four (m : IntTriple) :
    brandtThirdQuadratic m % 4 ≠ 3 := by
  intro h
  rcases int_square_emod_four m.1 with hx | hx <;>
    rcases int_square_emod_four m.2.1 with hy | hy <;>
    simp only [brandtThirdQuadratic] at h <;> omega

theorem target_mod_four_separator :
    (∃ m : IntTriple, brandtFirstQuadratic m % 4 = 3) ∧
      (∃ m : IntTriple, brandtSecondQuadratic m % 4 = 3) ∧
      (∀ m : IntTriple, brandtThirdQuadratic m % 4 ≠ 3) :=
  ⟨brandtFirst_represents_three_mod_four,
    brandtSecond_represents_three_mod_four,
    brandtThird_cannot_represent_three_mod_four⟩

/-! ## The exact source receiver and odd-prime scale law -/

/-- The retained source-class quadratic reading on integral coordinates. -/
def occurrenceSourceQuadratic
    (occurrence : BrandtNeighborOccurrence (p := p)) : IntTriple → ℤ :=
  match occurrence with
  | .inl _ => brandtFirstQuadratic
  | .inr _ => brandtSecondQuadratic

theorem occurrenceSourceQuadratic_cast
    (occurrence : BrandtNeighborOccurrence (p := p)) (m : IntTriple) :
    (occurrenceSourceQuadratic occurrence m : ℚ) =
      occurrence.quadraticReceiver (intTripleInclusion m) := by
  cases occurrence with
  | inl d =>
      simp [occurrenceSourceQuadratic,
        BrandtNeighborOccurrence.quadraticReceiver, brandtFirstQuadratic,
        intTripleInclusion, intTripleToRat, ratTunnellQuadratic]
  | inr d =>
      simp [occurrenceSourceQuadratic,
        BrandtNeighborOccurrence.quadraticReceiver, brandtSecondQuadratic,
        intTripleInclusion, intTripleToRat, ratBrandtSecondQuadratic]

/-- The integral numerator of an actual neighbor point has exactly `p²`
times its neighbor quadratic reading. -/
theorem occurrenceSourceQuadratic_integralPScale (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    (occurrenceSourceQuadratic occurrence
        (BrandtNeighborOccurrence.integralPScale hp2 occurrence x) : ℚ) =
      (p : ℚ) ^ 2 * occurrence.quadraticReceiver x.1 := by
  rw [occurrenceSourceQuadratic_cast]
  rw [BrandtNeighborOccurrence.intTripleInclusion_integralPScale]
  cases occurrence with
  | inl d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver]
      simp [ratTripleScaleP, ratTripleScale, ratTunnellQuadratic]
      ring
  | inr d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver]
      simp [ratTripleScaleP, ratTripleScale, ratBrandtSecondQuadratic]
      ring

/-- The opposite scale passage embeds every source point into the actual
neighbor and multiplies its quadratic reading by exactly `p²`. -/
theorem occurrenceNeighborQuadratic_integralToNeighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (m : IntTriple) :
    occurrence.quadraticReceiver
        ((BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence m).1) =
      (p : ℚ) ^ 2 * (occurrenceSourceQuadratic occurrence m : ℚ) := by
  rw [occurrenceSourceQuadratic_cast]
  cases occurrence with
  | inl d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver]
      simp [BrandtNeighborOccurrence.integralToNeighbor, ratTripleScaleP,
        ratTripleScale, ratTunnellQuadratic]
      ring
  | inr d =>
      simp only [BrandtNeighborOccurrence.quadraticReceiver]
      simp [BrandtNeighborOccurrence.integralToNeighbor, ratTripleScaleP,
        ratTripleScale, ratBrandtSecondQuadratic]
      ring

/-- An odd prime square acts identically on every integer residue modulo four. -/
theorem oddPrime_square_mul_emod_four (hp2 : p ≠ 2) (n : ℤ) :
    ((p : ℤ) ^ 2 * n) % 4 = n % 4 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hp : (p : ℤ) = 2 * (k : ℤ) + 1 := by
    exact_mod_cast hk
  rw [hp]
  rw [show (2 * (k : ℤ) + 1) ^ 2 * n =
      4 * ((k ^ 2 + k) * n) + n by ring]
  omega

/-- The source quadratic is homogeneous under an integral current scale. -/
theorem occurrenceSourceQuadratic_zsmul
    (occurrence : BrandtNeighborOccurrence (p := p))
    (a : ℤ) (m : IntTriple) :
    occurrenceSourceQuadratic occurrence (a • m) =
      a ^ 2 * occurrenceSourceQuadratic occurrence m := by
  cases occurrence <;> rcases m with ⟨x, y, z⟩ <;>
    simp [occurrenceSourceQuadratic, brandtFirstQuadratic,
      brandtSecondQuadratic] <;> ring

/-- An odd prime fourth power acts identically on every integer residue
modulo sixteen.  Two source/neighbor scale passages therefore preserve the
complete depth-four two-adic receiver without choosing an inverse. -/
theorem oddPrime_fourth_mul_emod_sixteen (hp2 : p ≠ 2) (n : ℤ) :
    ((p : ℤ) ^ 4 * n) % 16 = n % 16 := by
  obtain ⟨k, hk⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  rcases k.even_or_odd with ⟨u, hu⟩ | ⟨u, hu⟩
  · have hp : (p : ℤ) = 4 * (u : ℤ) + 1 := by
      have hpNat : p = 4 * u + 1 := by omega
      exact_mod_cast hpNat
    rw [hp]
    rw [show (4 * (u : ℤ) + 1) ^ 4 * n =
        16 * ((16 * u ^ 4 + 16 * u ^ 3 + 6 * u ^ 2 + u) * n) + n by ring]
    omega
  · have hp : (p : ℤ) = 4 * (u : ℤ) + 3 := by
      have hpNat : p = 4 * u + 3 := by omega
      exact_mod_cast hpNat
    rw [hp]
    rw [show (4 * (u : ℤ) + 3) ^ 4 * n =
        16 * ((16 * u ^ 4 + 48 * u ^ 3 + 54 * u ^ 2 + 27 * u + 5) * n) + n by ring]
    omega

/-! ## Complete source/neighbor mod-four profile equivalence -/

/-- The finite receiver asking whether the source class represents a residue
modulo four. -/
def SourceRepresentsModFour
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) : Prop :=
  ∃ m : IntTriple, occurrenceSourceQuadratic occurrence m % 4 = r % 4

/-- The same receiver on the actual rational neighbor, retaining the exact
integer witness returned by integrality. -/
def NeighborRepresentsModFour (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) : Prop :=
  ∃ x : occurrenceNeighborSubgroup hp2 occurrence, ∃ N : ℤ,
    occurrence.quadraticReceiver x.1 = (N : ℚ) ∧ N % 4 = r % 4

/-- **EVERY ACTUAL ODD-PRIME BRANDT NEIGHBOR HAS EXACTLY THE SOURCE MOD-FOUR
REPRESENTATION PROFILE.**  The forward passage is the scaled integral
inclusion; the reverse passage is the unique integral numerator. -/
theorem source_neighbor_mod_four_profile_equivalence (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) :
    SourceRepresentsModFour occurrence r ↔
      NeighborRepresentsModFour hp2 occurrence r := by
  constructor
  · rintro ⟨m, hm⟩
    let x := BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence m
    refine ⟨x, (p : ℤ) ^ 2 * occurrenceSourceQuadratic occurrence m, ?_, ?_⟩
    · simpa [x] using
        occurrenceNeighborQuadratic_integralToNeighbor hp2 occurrence m
    · rw [oddPrime_square_mul_emod_four hp2]
      exact hm
  · rintro ⟨x, N, hN, hmod⟩
    let m := BrandtNeighborOccurrence.integralPScale hp2 occurrence x
    refine ⟨m, ?_⟩
    have hscale : occurrenceSourceQuadratic occurrence m = (p : ℤ) ^ 2 * N := by
      have h := occurrenceSourceQuadratic_integralPScale hp2 occurrence x
      rw [hN] at h
      exact_mod_cast h
    rw [hscale, oddPrime_square_mul_emod_four hp2]
    exact hmod

/-! ## The complete depth-four two-adic profile -/

def SourceRepresentsModSixteen
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) : Prop :=
  ∃ m : IntTriple, occurrenceSourceQuadratic occurrence m % 16 = r % 16

def NeighborRepresentsModSixteen (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) : Prop :=
  ∃ x : occurrenceNeighborSubgroup hp2 occurrence, ∃ N : ℤ,
    occurrence.quadraticReceiver x.1 = (N : ℚ) ∧ N % 16 = r % 16

/-- Every actual odd-prime neighbor has exactly its retained source's
modulo-sixteen representation profile.  Scaling the witness once before the
already constructed passage makes the total quadratic scale `p⁴`, which is
the identity modulo sixteen for every odd `p`. -/
theorem source_neighbor_mod_sixteen_profile_equivalence (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (r : ℤ) :
    SourceRepresentsModSixteen occurrence r ↔
      NeighborRepresentsModSixteen hp2 occurrence r := by
  constructor
  · rintro ⟨m, hm⟩
    let m' : IntTriple := (p : ℤ) • m
    let x := BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence m'
    refine ⟨x, (p : ℤ) ^ 4 * occurrenceSourceQuadratic occurrence m, ?_, ?_⟩
    · change occurrence.quadraticReceiver
          ((BrandtNeighborOccurrence.integralToNeighbor hp2 occurrence m').1) = _
      rw [occurrenceNeighborQuadratic_integralToNeighbor,
        occurrenceSourceQuadratic_zsmul]
      push_cast
      ring
    · rw [oddPrime_fourth_mul_emod_sixteen hp2]
      exact hm
  · rintro ⟨x, N, hN, hmod⟩
    let m := BrandtNeighborOccurrence.integralPScale hp2 occurrence x
    refine ⟨(p : ℤ) • m, ?_⟩
    have hscale : occurrenceSourceQuadratic occurrence m = (p : ℤ) ^ 2 * N := by
      have h := occurrenceSourceQuadratic_integralPScale hp2 occurrence x
      rw [hN] at h
      exact_mod_cast h
    rw [occurrenceSourceQuadratic_zsmul, hscale]
    have hpow : (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * N) = (p : ℤ) ^ 4 * N := by ring
    rw [hpow, oddPrime_fourth_mul_emod_sixteen hp2]
    exact hmod

/-- Either retained source class represents residue three. -/
theorem occurrenceSource_represents_three_mod_four
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    SourceRepresentsModFour occurrence 3 := by
  cases occurrence with
  | inl d =>
      exact ⟨(1, 1, 0), by
        norm_num [SourceRepresentsModFour, occurrenceSourceQuadratic,
          brandtFirstQuadratic]⟩
  | inr d =>
      exact ⟨(1, 0, 1), by
        norm_num [SourceRepresentsModFour, occurrenceSourceQuadratic,
          brandtSecondQuadratic]⟩

/-- Every actual odd-prime Brandt neighbor represents residue three; combined
with the exact third-form obstruction, this removes that determinant-`64`
destination from the source-specific neighbor passage. -/
theorem occurrenceNeighbor_represents_three_and_third_cannot (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    NeighborRepresentsModFour hp2 occurrence 3 ∧
      ∀ m : IntTriple, brandtThirdQuadratic m % 4 ≠ 3 := by
  exact ⟨(source_neighbor_mod_four_profile_equivalence hp2 occurrence 3).mp
      (occurrenceSource_represents_three_mod_four occurrence),
    brandtThird_cannot_represent_three_mod_four⟩

#print axioms brandtTarget_mod_four_profiles_equivalent
#print axioms brandtThird_cannot_represent_three_mod_four
#print axioms occurrenceSourceQuadratic_integralPScale
#print axioms occurrenceNeighborQuadratic_integralToNeighbor
#print axioms oddPrime_square_mul_emod_four
#print axioms oddPrime_fourth_mul_emod_sixteen
#print axioms source_neighbor_mod_four_profile_equivalence
#print axioms source_neighbor_mod_sixteen_profile_equivalence
#print axioms occurrenceNeighbor_represents_three_and_third_cannot

end Soma.Holonics.Millennium.FamilyTunnellBrandtModFourReceiver

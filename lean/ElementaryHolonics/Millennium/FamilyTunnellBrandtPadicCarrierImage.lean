import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicPolarKernelBaseChange
import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicIntegralRepresentatives

/-!
# Integral carriers for the defining-prime isometry

This file gives the completed source lattice its literal carrier inside
`ℚ_p^3` and proves that the Hensel-lifted isotropic direction and its normalized
polar partner are points of that carrier.  The actual rational neighbor has
two initially different presentations: the scalar extension of its integral
rank-three basis, and the completed polar core plus the fractional direction.
The final theorem identifies those presentations exactly.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicCarrierImage

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicPolarKernelBaseChange
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIntegralRepresentatives
open Soma.Holonics.Millennium.FamilyTunnellBrandtLocalReflection

variable {p : ℕ} [Fact p.Prime]

/-- Coordinatewise inclusion `ℤ_p^3 → ℚ_p^3`. -/
def padicTripleToFieldLinear :
    PadicTriple (p := p) →ₗ[ℤ_[p]] PadicFieldTriple (p := p) where
  toFun := padicTripleToField
  map_add' x y := by
    ext <;> simp [padicTripleToField]
  map_smul' a x := by
    ext <;> simp [padicTripleToField, Algebra.smul_def]

/-- The completed source lattice, literally embedded in its fraction-field
ambient space. -/
def completedSourceLattice : Submodule ℤ_[p] (PadicFieldTriple (p := p)) :=
  LinearMap.range (padicTripleToFieldLinear (p := p))

theorem mem_completedSourceLattice_iff
    (x : PadicFieldTriple (p := p)) :
    x ∈ completedSourceLattice (p := p) ↔
      ∃ z : PadicTriple (p := p), padicTripleToField z = x := by
  rfl

/-- The completed source as a literal image predicate in `ℚ_p^3`. -/
def completedSourceCarrier : Set (PadicFieldTriple (p := p)) :=
  Set.range padicTripleToField

theorem mem_completedSourceCarrier_iff
    (x : PadicFieldTriple (p := p)) :
    x ∈ completedSourceCarrier (p := p) ↔
      ∃ z : PadicTriple (p := p), padicTripleToField z = x := by
  rfl

/-- Coordinatewise embedding of the rational ambient receiver. -/
def ratTripleToPadicField (x : RatTriple) : PadicFieldTriple (p := p) :=
  ((x.1 : ℚ_[p]), (x.2.1 : ℚ_[p]), (x.2.2 : ℚ_[p]))

/-- Scalar extension of the actual occurrence neighbor, using its proved
integral `Fin 3` basis.  This definition does not choose a destination class. -/
def completedOccurrenceNeighborLattice (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Submodule ℤ_[p] (PadicFieldTriple (p := p)) :=
  Submodule.span ℤ_[p]
    (Set.range fun i : Fin 3 =>
      ratTripleToPadicField (p := p)
        ((BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence i :
          occurrenceNeighborSubgroup hp2 occurrence) : RatTriple))

/-! ## The exact completed polar-core neighbor predicate -/

/-- The completed `p`-polar core of the retained source direction. -/
def completedPolarCore (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Set (PadicFieldTriple (p := p)) :=
  {x | ∃ m : PadicTriple (p := p), ∃ k : ℤ_[p],
      occurrencePadicPolar occurrence m
        (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
          (p : ℤ_[p]) * k ∧
      padicTripleToField m = x}

private def completedFractionalDirection (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) :=
  ((p : ℚ_[p])⁻¹) •
    padicTripleToField
      (intTripleToPadic (occurrenceDirectionLift hp2 occurrence))

/-- The completed neighbor as a genuine `ℤ_p`-submodule: the image of the
completed polar kernel joined with the cyclic fractional direction. -/
def completedOccurrenceNeighborPresentation (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Submodule ℤ_[p] (PadicFieldTriple (p := p)) :=
  (completedOriginalPolarKernel hp2 occurrence).map
      (padicTripleToFieldLinear (p := p)) ⊔
    Submodule.span ℤ_[p] {completedFractionalDirection hp2 occurrence}

theorem mem_completedOccurrenceNeighborPresentation_iff
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : PadicFieldTriple (p := p)) :
    x ∈ completedOccurrenceNeighborPresentation hp2 occurrence ↔
      ∃ m : PadicTriple (p := p), ∃ k : ℤ_[p],
        occurrencePadicPolar occurrence m
          (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
            (p : ℤ_[p]) * k ∧
        ∃ a : ℤ_[p],
          padicTripleToField m + a • completedFractionalDirection hp2 occurrence = x := by
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hx
    obtain ⟨m, hm, rfl⟩ := hu
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
    obtain ⟨k, hk⟩ := hm
    refine ⟨m, k, hk, a, ?_⟩
    rw [ha]
    exact huv
  · rintro ⟨m, k, hk, a, rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨padicTripleToField m, ?_,
      a • completedFractionalDirection hp2 occurrence, ?_, rfl⟩
    · exact ⟨m, ⟨k, hk⟩, rfl⟩
    · exact Submodule.mem_span_singleton.mpr ⟨a, rfl⟩

/-- The actual completed neighbor is the integral polar core plus a
`ℤ_p`-multiple of the retained fractional direction `v/p`. -/
def completedOccurrenceNeighborCarrier (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Set (PadicFieldTriple (p := p)) :=
  {x | ∃ m : PadicTriple (p := p), ∃ k : ℤ_[p],
      occurrencePadicPolar occurrence m
        (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
          (p : ℤ_[p]) * k ∧
      ∃ a : ℤ_[p],
        padicTripleToField m + a • completedFractionalDirection hp2 occurrence = x}

theorem completedOccurrenceNeighborCarrier_mem_iff
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : PadicFieldTriple (p := p)) :
    x ∈ completedOccurrenceNeighborCarrier hp2 occurrence ↔
      ∃ m : PadicTriple (p := p), ∃ k : ℤ_[p],
        occurrencePadicPolar occurrence m
          (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
            (p : ℤ_[p]) * k ∧
        ∃ a : ℤ_[p],
          padicTripleToField m + a • completedFractionalDirection hp2 occurrence = x := by
  rfl

theorem completedOccurrenceNeighborPresentation_carrier_eq
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (completedOccurrenceNeighborPresentation hp2 occurrence :
      Set (PadicFieldTriple (p := p))) =
        completedOccurrenceNeighborCarrier hp2 occurrence := by
  ext x
  change (x ∈ completedOccurrenceNeighborPresentation hp2 occurrence) ↔
    x ∈ completedOccurrenceNeighborCarrier hp2 occurrence
  rw [mem_completedOccurrenceNeighborPresentation_iff,
    completedOccurrenceNeighborCarrier_mem_iff]

private theorem intTriple_embedding_commutes (m : IntTriple) :
    padicTripleToField (p := p) (intTripleToPadic (p := p) m) =
      ratTripleToPadicField (p := p) (intTripleInclusion m) := by
  ext <;>
    simp [padicTripleToField, intTripleToPadic, ratTripleToPadicField,
      intTripleInclusion, intTripleToRat]

private theorem fractionalGenerator_embedding_commutes (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    ratTripleToPadicField (p := p)
        (occurrenceFractionalGenerator hp2 occurrence) =
      completedFractionalDirection hp2 occurrence := by
  ext <;>
    simp [ratTripleToPadicField, occurrenceFractionalGenerator,
      completedFractionalDirection, ratTripleScale, intTripleToRat,
      padicTripleToField, intTripleToPadic, Algebra.smul_def, div_eq_mul_inv]

/-- Every literal rational neighbor occurrence enters the completed
polar-core-plus-generator presentation. -/
theorem ratTripleToPadicField_neighbor_mem_presentation
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    ratTripleToPadicField (p := p) (x : RatTriple) ∈
      completedOccurrenceNeighborPresentation hp2 occurrence := by
  rw [mem_completedOccurrenceNeighborPresentation_iff]
  cases occurrence with
  | inl d =>
      rcases x.property with ⟨m, hm, a, hx⟩
      change (p : ℤ) ∣ intTunnellPolar 32 m
        (adjustedDirectionLift 32 d) at hm
      rcases hm with ⟨q, hq⟩
      refine ⟨intTripleToPadic (p := p) m, (q : ℤ_[p]), ?_,
        (a : ℤ_[p]), ?_⟩
      · rw [occurrencePadicPolar_intCast]
        simp only [occurrenceIntegralPolar, occurrenceDirectionLift]
        rw [hq]
        push_cast
        rfl
      · rw [hx]
        ext <;>
          simp [ratTripleToPadicField, completedFractionalDirection,
            occurrenceDirectionLift, ratTripleAdd, ratTripleScale,
            intTripleToRat, padicTripleToField, intTripleToPadic,
            Algebra.smul_def, div_eq_mul_inv] <;> ring
  | inr d =>
      rcases x.property with ⟨m, hm, a, hx⟩
      change (p : ℤ) ∣ brandtSecondPolar m
        (adjustedBrandtSecondDirectionLift hp2 d) at hm
      rcases hm with ⟨q, hq⟩
      refine ⟨intTripleToPadic (p := p) m, (q : ℤ_[p]), ?_,
        (a : ℤ_[p]), ?_⟩
      · rw [occurrencePadicPolar_intCast]
        simp only [occurrenceIntegralPolar, occurrenceDirectionLift]
        rw [hq]
        push_cast
        rfl
      · rw [hx]
        ext <;>
          simp [ratTripleToPadicField, completedFractionalDirection,
            occurrenceDirectionLift, ratTripleAdd, ratTripleScale,
            intTripleToRat, padicTripleToField, intTripleToPadic,
            Algebra.smul_def, div_eq_mul_inv] <;> ring

theorem occurrencePadicIsotropicVector_mem_completedSource
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicIsotropicVector hp2 occurrence ∈
      completedSourceLattice (p := p) := by
  exact ⟨occurrenceExactIsotropicLift hp2 occurrence, rfl⟩

theorem occurrencePadicWitnessVector_mem_completedSource
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicWitnessVector hp2 occurrence ∈
      completedSourceLattice (p := p) := by
  exact ⟨intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence), rfl⟩

theorem ratTripleToPadicField_neighbor_mem_completed
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (x : occurrenceNeighborSubgroup hp2 occurrence) :
    ratTripleToPadicField (p := p) (x : RatTriple) ∈
      completedOccurrenceNeighborLattice hp2 occurrence := by
  let b := BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence
  have heq :
      ratTripleToPadicField (p := p) (x : RatTriple) =
        ∑ i : Fin 3, ((b.repr x i : ℤ) : ℤ_[p]) •
          ratTripleToPadicField (p := p) ((b i :
            occurrenceNeighborSubgroup hp2 occurrence) : RatTriple) := by
    let f₁ : occurrenceNeighborSubgroup hp2 occurrence →+ ℚ_[p] :=
      { toFun := fun y => ((y : RatTriple).1 : ℚ_[p])
        map_zero' := by simp
        map_add' := by intro y z; simp }
    let f₂ : occurrenceNeighborSubgroup hp2 occurrence →+ ℚ_[p] :=
      { toFun := fun y => ((y : RatTriple).2.1 : ℚ_[p])
        map_zero' := by simp
        map_add' := by intro y z; simp }
    let f₃ : occurrenceNeighborSubgroup hp2 occurrence →+ ℚ_[p] :=
      { toFun := fun y => ((y : RatTriple).2.2 : ℚ_[p])
        map_zero' := by simp
        map_add' := by intro y z; simp }
    have hx := congrArg f₁ (b.sum_repr x)
    have hy := congrArg f₂ (b.sum_repr x)
    have hz := congrArg f₃ (b.sum_repr x)
    rw [map_sum] at hx hy hz
    apply Prod.ext
    · simpa [f₁, ratTripleToPadicField, Algebra.smul_def, Fin.sum_univ_succ] using hx.symm
    · apply Prod.ext <;>
        first
        | simpa [f₂, ratTripleToPadicField, Algebra.smul_def, Fin.sum_univ_succ] using hy.symm
        | simpa [f₃, ratTripleToPadicField, Algebra.smul_def, Fin.sum_univ_succ] using hz.symm
  rw [heq]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i))

/-- Scalar extension of the integral polar kernel maps into the completed
actual-neighbor lattice.  This is where the exact reverse base-change
inclusion is consumed. -/
theorem completedPolarKernel_image_le_completedOccurrenceNeighborLattice
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (completedOriginalPolarKernel hp2 occurrence).map
        (padicTripleToFieldLinear (p := p)) ≤
      completedOccurrenceNeighborLattice hp2 occurrence := by
  rintro _ ⟨m, hm, rfl⟩
  have hmSpan : m ∈ integralPolarKernelPadicSpan hp2 occurrence := by
    rw [integralPolarKernelPadicSpan_eq_completedOriginalPolarKernel]
    exact hm
  have hSpanLe : integralPolarKernelPadicSpan hp2 occurrence ≤
      (completedOccurrenceNeighborLattice hp2 occurrence).comap
        (padicTripleToFieldLinear (p := p)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change padicTripleToField (intTripleToPadic (p := p) (n : IntTriple)) ∈
      completedOccurrenceNeighborLattice hp2 occurrence
    rw [intTriple_embedding_commutes]
    have hnCore : intTripleInclusion (n : IntTriple) ∈
        sourcePolarCore hp2 occurrence := by
      rw [sourcePolarCore, AddSubgroup.mem_map]
      exact ⟨(n : IntTriple), n.property, rfl⟩
    let y : occurrenceNeighborSubgroup hp2 occurrence :=
      ⟨intTripleInclusion (n : IntTriple),
        sourcePolarCore_le_neighbor hp2 occurrence hnCore⟩
    exact ratTripleToPadicField_neighbor_mem_completed hp2 occurrence y
  exact hSpanLe hmSpan

theorem completedFractionalDirection_mem_completedOccurrenceNeighborLattice
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedFractionalDirection hp2 occurrence ∈
      completedOccurrenceNeighborLattice hp2 occurrence := by
  rw [← fractionalGenerator_embedding_commutes]
  exact ratTripleToPadicField_neighbor_mem_completed hp2 occurrence
    ⟨occurrenceFractionalGenerator hp2 occurrence,
      occurrenceFractionalGenerator_mem_neighbor hp2 occurrence⟩

theorem completedOccurrenceNeighborPresentation_le_lattice
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedOccurrenceNeighborPresentation hp2 occurrence ≤
      completedOccurrenceNeighborLattice hp2 occurrence := by
  apply sup_le
  · exact completedPolarKernel_image_le_completedOccurrenceNeighborLattice
      hp2 occurrence
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact completedFractionalDirection_mem_completedOccurrenceNeighborLattice
      hp2 occurrence

theorem completedOccurrenceNeighborLattice_le_presentation
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedOccurrenceNeighborLattice hp2 occurrence ≤
      completedOccurrenceNeighborPresentation hp2 occurrence := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ratTripleToPadicField_neighbor_mem_presentation hp2 occurrence
    (BrandtNeighborOccurrence.rankThreeBasis hp2 occurrence i)

/-- **THE TWO COMPLETED ACTUAL-NEIGHBOR CARRIERS ARE IDENTICAL.**

The basis-span completion and the source-faithful polar-core-plus-fractional-
generator completion are one `ℤ_p`-submodule of the common `ℚ_p³` receiver.
This theorem consumes the reverse polar-kernel base-change law rather than
merely restating the two presentations. -/
theorem completedOccurrenceNeighborLattice_eq_presentation
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedOccurrenceNeighborLattice hp2 occurrence =
      completedOccurrenceNeighborPresentation hp2 occurrence :=
  le_antisymm
    (completedOccurrenceNeighborLattice_le_presentation hp2 occurrence)
    (completedOccurrenceNeighborPresentation_le_lattice hp2 occurrence)

theorem completedOccurrenceNeighborLattice_carrier_eq
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (completedOccurrenceNeighborLattice hp2 occurrence :
      Set (PadicFieldTriple (p := p))) =
        completedOccurrenceNeighborCarrier hp2 occurrence := by
  rw [completedOccurrenceNeighborLattice_eq_presentation,
    completedOccurrenceNeighborPresentation_carrier_eq]

theorem occurrenceNormalizedPartner_mem_completedSource
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceNormalizedPartner hp2 occurrence ∈
      completedSourceLattice (p := p) := by
  refine ⟨normalizedPartnerIntegral hp2 occurrence, ?_⟩
  exact normalizedPartnerIntegral_cast hp2 occurrence

/-- The exact lift retains the original projective direction modulo `p`. -/
theorem occurrenceExactIsotropicLift_sub_direction
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceExactIsotropicLift hp2 occurrence -
        intTripleToPadic (occurrenceDirectionLift hp2 occurrence) =
      (p : ℤ_[p]) •
        (occurrenceCorrectionRoot hp2 occurrence •
          intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)) := by
  rw [occurrenceExactIsotropicLift]
  module

/-- The Hensel correction scalar is in the principal maximal ideal of
`ℤ_p`; this is the exact divisibility form of its strict neighbourhood
condition. -/
theorem occurrenceCorrectionRoot_dvd_prime
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (p : ℤ_[p]) ∣ occurrenceCorrectionRoot hp2 occurrence := by
  rw [← PadicInt.norm_lt_one_iff_dvd]
  exact occurrenceCorrectionRoot_norm_lt_one hp2 occurrence

/-- Dividing the exact Hensel lift by `p` exposes the source direction and the
correction current without any approximation:
`e/p = v/p + s*w`. -/
theorem occurrenceExactIsotropicLift_div_prime_eq_source_plus_correction
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    ((p : ℚ_[p])⁻¹) •
        padicTripleToField (occurrenceExactIsotropicLift hp2 occurrence) =
    ((p : ℚ_[p])⁻¹) •
          padicTripleToField
            (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) +
        (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p]) •
          occurrencePadicWitnessVector hp2 occurrence := by
  have hpQ : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hsplit :
      padicTripleToField (occurrenceExactIsotropicLift hp2 occurrence) =
        padicTripleToField
            (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) +
          ((p : ℚ_[p]) *
            (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p])) •
            occurrencePadicWitnessVector hp2 occurrence := by
    rw [occurrenceExactIsotropicLift, occurrencePadicWitnessVector]
    apply Prod.ext <;>
      simp [padicTripleToField, intTripleToPadic, Algebra.smul_def]
  rw [hsplit, smul_add, smul_smul]
  have hpinv : (p : ℚ_[p])⁻¹ *
      ((p : ℚ_[p]) * (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p])) =
        (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p]) := by
    rw [← mul_assoc, inv_mul_cancel₀ hpQ, one_mul]
  rw [hpinv]

/-- The correction term in the divided lift is itself an integral source
current, since the correction scalar is divisible by `p`. -/
theorem occurrenceCorrection_current_mem_completedSource
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p]) •
        occurrencePadicWitnessVector hp2 occurrence ∈
      completedSourceLattice (p := p) := by
  rcases occurrenceCorrectionRoot_dvd_prime hp2 occurrence with ⟨k, hk⟩
  let w : PadicTriple (p := p) :=
    intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)
  have hmap : padicTripleToFieldLinear (p := p)
        (((p : ℤ_[p]) * k) • w) =
      ((p : ℚ_[p]) * (k : ℚ_[p])) • padicTripleToField w := by
    apply Prod.ext <;>
      simp [padicTripleToFieldLinear, padicTripleToField, w,
        intTripleToPadic, Algebra.smul_def]
  refine ⟨((p : ℤ_[p]) * k) • w, ?_⟩
  change padicTripleToFieldLinear (p := p) (((p : ℤ_[p]) * k) • w) =
    (occurrenceCorrectionRoot hp2 occurrence : ℚ_[p]) •
      occurrencePadicWitnessVector hp2 occurrence
  rw [hmap, occurrencePadicWitnessVector, hk]
  simp [w]

/-! ## The ambient isometry returns the actual completed neighbor -/

private theorem occurrencePadicPolar_sub_left
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v w : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence (u - v) w =
      occurrencePadicPolar occurrence u w -
        occurrencePadicPolar occurrence v w := by
  cases occurrence <;> simp [occurrencePadicPolar] <;> ring

private theorem occurrencePadicPolar_add_right
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v w : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence u (v + w) =
      occurrencePadicPolar occurrence u v +
        occurrencePadicPolar occurrence u w := by
  cases occurrence <;> simp [occurrencePadicPolar] <;> ring

private theorem occurrencePadicPolar_sub_right
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v w : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence u (v - w) =
      occurrencePadicPolar occurrence u v -
        occurrencePadicPolar occurrence u w := by
  cases occurrence <;> simp [occurrencePadicPolar] <;> ring

private theorem occurrencePadicPolar_smul_right
    (occurrence : BrandtNeighborOccurrence (p := p))
    (a : ℤ_[p]) (u v : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence u (a • v) =
      a * occurrencePadicPolar occurrence u v := by
  cases occurrence <;>
    simp [occurrencePadicPolar, smul_eq_mul] <;> ring

private theorem occurrencePadicPolar_symmetric
    (occurrence : BrandtNeighborOccurrence (p := p))
    (u v : PadicTriple (p := p)) :
    occurrencePadicPolar occurrence u v =
      occurrencePadicPolar occurrence v u := by
  cases occurrence <;> simp [occurrencePadicPolar] <;> ring

private theorem exactLift_polar_self_eq_zero (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicPolar occurrence
      (occurrenceExactIsotropicLift hp2 occurrence)
      (occurrenceExactIsotropicLift hp2 occurrence) = 0 := by
  rw [occurrencePadicPolar_self,
    occurrenceExactIsotropicLift_quadratic_eq_zero]
  ring

private theorem exactLift_polar_isotropicPartnerIntegral_eq_one
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicPolar occurrence
      (occurrenceExactIsotropicLift hp2 occurrence)
      (isotropicPartnerIntegral hp2 occurrence) = 1 := by
  apply Subtype.coe_injective
  change
    (occurrencePadicPolar occurrence
      (occurrenceExactIsotropicLift hp2 occurrence)
      (isotropicPartnerIntegral hp2 occurrence) : ℚ_[p]) = 1
  rw [← occurrencePadicFieldPolar_cast,
    isotropicPartnerIntegral_cast]
  exact occurrenceIsotropicPartner_pairing hp2 occurrence

/-- The field isometry viewed through the integral scalar chart. -/
def occurrenceDefiningPrimeIsometryPadicLinear (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    PadicFieldTriple (p := p) →ₗ[ℤ_[p]] PadicFieldTriple (p := p) :=
  ((occurrenceDefiningPrimeIsometry hp2 occurrence).restrictScalars ℤ_[p]).toLinearMap

/-- Integral remainder left after the isometry's fractional `e/p` current is
rewritten through the retained source direction `v/p`. -/
private def sourceImageIntegralRemainder (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (z : PadicTriple (p := p)) : PadicTriple (p := p) :=
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := isotropicPartnerIntegral hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let α := occurrencePadicPolar occurrence z f
  let β := occurrencePadicPolar occurrence z e
  z - α • e + (((p : ℤ_[p]) - 1) * β) • f + (α * s) • w

private theorem sourceImageIntegralRemainder_mem_completedKernel
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (z : PadicTriple (p := p)) :
    sourceImageIntegralRemainder hp2 occurrence z ∈
      completedOriginalPolarKernel hp2 occurrence := by
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := isotropicPartnerIntegral hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let v := intTripleToPadic (p := p) (occurrenceDirectionLift hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let α := occurrencePadicPolar occurrence z f
  let β := occurrencePadicPolar occurrence z e
  let m := sourceImageIntegralRemainder hp2 occurrence z
  rcases occurrenceCorrectionRoot_dvd_prime hp2 occurrence with ⟨t, ht⟩
  have hs : s = (p : ℤ_[p]) * t := ht
  have hee : occurrencePadicPolar occurrence e e = 0 := by
    exact exactLift_polar_self_eq_zero hp2 occurrence
  have hef : occurrencePadicPolar occurrence e f = 1 := by
    exact exactLift_polar_isotropicPartnerIntegral_eq_one hp2 occurrence
  have hfe : occurrencePadicPolar occurrence f e = 1 := by
    rw [occurrencePadicPolar_symmetric]
    exact hef
  have hmE :
      occurrencePadicPolar occurrence m e =
        (p : ℤ_[p]) *
          (β + α * t * occurrencePadicPolar occurrence w e) := by
    change occurrencePadicPolar occurrence
      (z - α • e + (((p : ℤ_[p]) - 1) * β) • f +
        (α * s) • w) e = _
    rw [occurrencePadicPolar_add_left,
      occurrencePadicPolar_add_left,
      occurrencePadicPolar_sub_left,
      occurrencePadicPolar_smul_left,
      occurrencePadicPolar_smul_left,
      occurrencePadicPolar_smul_left,
      hee, hfe, hs]
    change β - α * 0 + ((p : ℤ_[p]) - 1) * β * 1 +
      α * ((p : ℤ_[p]) * t) *
        occurrencePadicPolar occurrence w e = _
    ring
  have hv : v = e - ((p : ℤ_[p]) * s) • w := by
    change intTripleToPadic (occurrenceDirectionLift hp2 occurrence) =
      occurrenceExactIsotropicLift hp2 occurrence -
        ((p : ℤ_[p]) * occurrenceCorrectionRoot hp2 occurrence) •
          intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence)
    rw [occurrenceExactIsotropicLift]
    module
  refine ⟨β + α * t * occurrencePadicPolar occurrence w e -
      s * occurrencePadicPolar occurrence m w, ?_⟩
  change occurrencePadicPolar occurrence m v = _
  rw [hv, occurrencePadicPolar_sub_right,
    occurrencePadicPolar_smul_right, hmE]
  ring

private theorem definingPrimeIsometry_integral_decomposition
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (z : PadicTriple (p := p)) :
    occurrenceDefiningPrimeIsometry hp2 occurrence (padicTripleToField z) =
      padicTripleToField (sourceImageIntegralRemainder hp2 occurrence z) +
        occurrencePadicPolar occurrence z
            (isotropicPartnerIntegral hp2 occurrence) •
          completedFractionalDirection hp2 occurrence := by
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := isotropicPartnerIntegral hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let α := occurrencePadicPolar occurrence z f
  let β := occurrencePadicPolar occurrence z e
  let zF := padicTripleToField z
  let eF := padicTripleToField e
  let fF := padicTripleToField f
  let wF := padicTripleToField w
  have hfF : fF = occurrenceIsotropicPartner hp2 occurrence := by
    exact isotropicPartnerIntegral_cast hp2 occurrence
  have hα : occurrencePadicFieldPolar occurrence zF
      (occurrenceIsotropicPartner hp2 occurrence) = (α : ℚ_[p]) := by
    rw [← hfF]
    exact occurrencePadicFieldPolar_cast occurrence z f
  have hβ : occurrencePadicFieldPolar occurrence zF
      (occurrencePadicIsotropicVector hp2 occurrence) = (β : ℚ_[p]) := by
    exact occurrencePadicFieldPolar_cast occurrence z e
  have hdiv :
      ((p : ℚ_[p])⁻¹) • eF =
        completedFractionalDirection hp2 occurrence +
          (s : ℚ_[p]) • wF := by
    simpa [eF, wF, completedFractionalDirection,
      occurrencePadicWitnessVector] using
        occurrenceExactIsotropicLift_div_prime_eq_source_plus_correction
          hp2 occurrence
  change
    hyperbolicScale
        (occurrencePadicFieldPolar occurrence)
        (occurrencePadicIsotropicVector hp2 occurrence)
        (occurrenceIsotropicPartner hp2 occurrence) (p : ℚ_[p]) zF = _
  rw [hyperbolicScale_apply
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence), hα, hβ]
  rw [← hfF]
  change
    zF + (((p : ℚ_[p])⁻¹ - 1) * (α : ℚ_[p])) • eF +
        (((p : ℚ_[p]) - 1) * (β : ℚ_[p])) • fF =
      padicTripleToField (sourceImageIntegralRemainder hp2 occurrence z) +
        α • completedFractionalDirection hp2 occurrence
  calc
    zF + (((p : ℚ_[p])⁻¹ - 1) * (α : ℚ_[p])) • eF +
        (((p : ℚ_[p]) - 1) * (β : ℚ_[p])) • fF =
      zF - (α : ℚ_[p]) • eF +
          (((p : ℚ_[p]) - 1) * (β : ℚ_[p])) • fF +
        (α : ℚ_[p]) • (((p : ℚ_[p])⁻¹) • eF) := by module
    _ = zF - (α : ℚ_[p]) • eF +
          (((p : ℚ_[p]) - 1) * (β : ℚ_[p])) • fF +
        (α : ℚ_[p]) •
          (completedFractionalDirection hp2 occurrence + (s : ℚ_[p]) • wF) := by
      rw [hdiv]
    _ = padicTripleToField (sourceImageIntegralRemainder hp2 occurrence z) +
        α • completedFractionalDirection hp2 occurrence := by
      ext <;>
        simp [sourceImageIntegralRemainder, zF, eF, fF, wF, e, f, w, s,
          α, β, padicTripleToField, Algebra.smul_def] <;> ring

theorem definingPrimeIsometry_completedSource_le_presentation
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) ≤
      completedOccurrenceNeighborPresentation hp2 occurrence := by
  rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
  have hm := sourceImageIntegralRemainder_mem_completedKernel
    hp2 occurrence z
  rcases hm with ⟨k, hk⟩
  rw [mem_completedOccurrenceNeighborPresentation_iff]
  refine ⟨sourceImageIntegralRemainder hp2 occurrence z, k, hk,
    occurrencePadicPolar occurrence z
      (isotropicPartnerIntegral hp2 occurrence), ?_⟩
  exact (definingPrimeIsometry_integral_decomposition hp2 occurrence z).symm

private theorem isotropicPartnerIntegral_polar_self_eq_zero
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrencePadicPolar occurrence
      (isotropicPartnerIntegral hp2 occurrence)
      (isotropicPartnerIntegral hp2 occurrence) = 0 := by
  apply Subtype.coe_injective
  change
    (occurrencePadicPolar occurrence
      (isotropicPartnerIntegral hp2 occurrence)
      (isotropicPartnerIntegral hp2 occurrence) : ℚ_[p]) = 0
  rw [← occurrencePadicFieldPolar_cast,
    isotropicPartnerIntegral_cast]
  exact occurrenceIsotropicPartner_isotropic hp2 occurrence

/-- Integral preimage of a completed-kernel point under the defining-prime
isometry.  The supplied `k` is retained as its exact divisibility witness. -/
private def completedKernelPreimage (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (m : PadicTriple (p := p)) (k : ℤ_[p]) : PadicTriple (p := p) :=
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := isotropicPartnerIntegral hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let α := occurrencePadicPolar occurrence m f
  let κ := k + s * occurrencePadicPolar occurrence m w
  m + (((p : ℤ_[p]) - 1) * α) • e +
    ((1 - (p : ℤ_[p])) * κ) • f

private theorem definingPrimeIsometry_completedKernelPreimage
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (m : PadicTriple (p := p)) (k : ℤ_[p])
    (hm : occurrencePadicPolar occurrence m
      (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
        (p : ℤ_[p]) * k) :
    occurrenceDefiningPrimeIsometry hp2 occurrence
        (padicTripleToField (completedKernelPreimage hp2 occurrence m k)) =
      padicTripleToField m := by
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let f := isotropicPartnerIntegral hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let v := intTripleToPadic (p := p) (occurrenceDirectionLift hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  let α := occurrencePadicPolar occurrence m f
  let κ := k + s * occurrencePadicPolar occurrence m w
  let z := completedKernelPreimage hp2 occurrence m k
  have hee : occurrencePadicPolar occurrence e e = 0 :=
    exactLift_polar_self_eq_zero hp2 occurrence
  have hef : occurrencePadicPolar occurrence e f = 1 :=
    exactLift_polar_isotropicPartnerIntegral_eq_one hp2 occurrence
  have hfe : occurrencePadicPolar occurrence f e = 1 := by
    rw [occurrencePadicPolar_symmetric]
    exact hef
  have hff : occurrencePadicPolar occurrence f f = 0 :=
    isotropicPartnerIntegral_polar_self_eq_zero hp2 occurrence
  have he : e = v + ((p : ℤ_[p]) * s) • w := by
    rfl
  have hmE : occurrencePadicPolar occurrence m e = (p : ℤ_[p]) * κ := by
    rw [he, occurrencePadicPolar_add_right,
      occurrencePadicPolar_smul_right]
    change occurrencePadicPolar occurrence m v +
      (p : ℤ_[p]) * s * occurrencePadicPolar occurrence m w =
        (p : ℤ_[p]) *
          (k + s * occurrencePadicPolar occurrence m w)
    rw [hm]
    ring
  have hzF : occurrencePadicPolar occurrence z f = (p : ℤ_[p]) * α := by
    change occurrencePadicPolar occurrence
      (m + (((p : ℤ_[p]) - 1) * α) • e +
        ((1 - (p : ℤ_[p])) * κ) • f) f = _
    rw [occurrencePadicPolar_add_left,
      occurrencePadicPolar_add_left,
      occurrencePadicPolar_smul_left,
      occurrencePadicPolar_smul_left, hef, hff]
    change α + ((p : ℤ_[p]) - 1) * α * 1 +
      (1 - (p : ℤ_[p])) * κ * 0 = _
    ring
  have hzE : occurrencePadicPolar occurrence z e = κ := by
    change occurrencePadicPolar occurrence
      (m + (((p : ℤ_[p]) - 1) * α) • e +
        ((1 - (p : ℤ_[p])) * κ) • f) e = _
    rw [occurrencePadicPolar_add_left,
      occurrencePadicPolar_add_left,
      occurrencePadicPolar_smul_left,
      occurrencePadicPolar_smul_left, hmE, hee, hfe]
    ring
  let zF := padicTripleToField z
  let eF := padicTripleToField e
  let fF := padicTripleToField f
  have hfF : fF = occurrenceIsotropicPartner hp2 occurrence :=
    isotropicPartnerIntegral_cast hp2 occurrence
  have hzFField : occurrencePadicFieldPolar occurrence zF
      (occurrenceIsotropicPartner hp2 occurrence) =
        (p : ℚ_[p]) * (α : ℚ_[p]) := by
    rw [← hfF, occurrencePadicFieldPolar_cast, hzF]
    push_cast
    rfl
  have hzEField : occurrencePadicFieldPolar occurrence zF
      (occurrencePadicIsotropicVector hp2 occurrence) = (κ : ℚ_[p]) := by
    change occurrencePadicFieldPolar occurrence zF (padicTripleToField e) =
      (κ : ℚ_[p])
    rw [occurrencePadicFieldPolar_cast, hzE]
  have hpQ : (p : ℚ_[p]) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  change hyperbolicScale
      (occurrencePadicFieldPolar occurrence)
      (occurrencePadicIsotropicVector hp2 occurrence)
      (occurrenceIsotropicPartner hp2 occurrence) (p : ℚ_[p]) zF =
    padicTripleToField m
  rw [hyperbolicScale_apply
    (occurrencePadicFieldPolar occurrence)
    (occurrencePadicFieldPolar_symmetric occurrence), hzFField, hzEField,
    ← hfF]
  change zF + (((p : ℚ_[p])⁻¹ - 1) *
      ((p : ℚ_[p]) * (α : ℚ_[p]))) • eF +
      (((p : ℚ_[p]) - 1) * (κ : ℚ_[p])) • fF =
    padicTripleToField m
  have hpinv : (p : ℚ_[p])⁻¹ * (p : ℚ_[p]) = 1 :=
    inv_mul_cancel₀ hpQ
  ext <;>
    simp [completedKernelPreimage, zF, eF, fF, z, e, f, w, s, α, κ,
      padicTripleToField, Algebra.smul_def] <;>
    field_simp [hpQ] <;> ring

theorem completedPolarKernel_image_le_definingPrimeIsometry_source
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    (completedOriginalPolarKernel hp2 occurrence).map
        (padicTripleToFieldLinear (p := p)) ≤
      completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) := by
  rintro _ ⟨m, hm, rfl⟩
  rcases hm with ⟨k, hk⟩
  refine ⟨padicTripleToField (completedKernelPreimage hp2 occurrence m k),
    ⟨completedKernelPreimage hp2 occurrence m k, rfl⟩, ?_⟩
  exact definingPrimeIsometry_completedKernelPreimage hp2 occurrence m k hk

private theorem correctionPadicCurrent_mem_completedKernel
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    occurrenceCorrectionRoot hp2 occurrence •
        intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence) ∈
      completedOriginalPolarKernel hp2 occurrence := by
  rcases occurrenceCorrectionRoot_dvd_prime hp2 occurrence with ⟨t, ht⟩
  refine ⟨t * occurrencePadicPolar occurrence
      (intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence))
      (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)), ?_⟩
  rw [occurrencePadicPolar_smul_left, ht]
  ring

theorem completedFractionalDirection_mem_definingPrimeIsometry_source
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedFractionalDirection hp2 occurrence ∈
      completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) := by
  let I := completedSourceLattice.map
    (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence)
  let e := occurrenceExactIsotropicLift hp2 occurrence
  let w := intTripleToPadic (p := p) (occurrencePolarUnitWitness hp2 occurrence)
  let s := occurrenceCorrectionRoot hp2 occurrence
  change completedFractionalDirection hp2 occurrence ∈ I
  have he : ((p : ℚ_[p])⁻¹) • padicTripleToField e ∈ I := by
    refine ⟨padicTripleToField e, ⟨e, rfl⟩, ?_⟩
    exact occurrenceDefiningPrimeIsometry_isotropic_direction hp2 occurrence
  have hcMap : padicTripleToField (s • w) ∈
      (completedOriginalPolarKernel hp2 occurrence).map
        (padicTripleToFieldLinear (p := p)) := by
    exact ⟨s • w,
      correctionPadicCurrent_mem_completedKernel hp2 occurrence, rfl⟩
  have hc : padicTripleToField (s • w) ∈ I :=
    completedPolarKernel_image_le_definingPrimeIsometry_source
      hp2 occurrence hcMap
  have hsub := Submodule.sub_mem I he hc
  have hdiv := occurrenceExactIsotropicLift_div_prime_eq_source_plus_correction
    hp2 occurrence
  change ((p : ℚ_[p])⁻¹) • padicTripleToField e =
      completedFractionalDirection hp2 occurrence +
        (s : ℚ_[p]) • padicTripleToField w at hdiv
  have hcCast : padicTripleToField (s • w) =
      (s : ℚ_[p]) • padicTripleToField w := by
    ext <;> simp [padicTripleToField, Algebra.smul_def]
  rw [hcCast] at hsub
  rw [hdiv] at hsub
  simpa using hsub

theorem completedOccurrenceNeighborPresentation_le_definingPrimeIsometry_source
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedOccurrenceNeighborPresentation hp2 occurrence ≤
      completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) := by
  apply sup_le
  · exact completedPolarKernel_image_le_definingPrimeIsometry_source
      hp2 occurrence
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact completedFractionalDirection_mem_definingPrimeIsometry_source
      hp2 occurrence

/-- **THE DEFINING-PRIME ISOMETRY MAPS THE COMPLETED SOURCE ONTO THE ACTUAL
COMPLETED NEIGHBOR.**

This is the formerly missing carrier-image theorem.  It composes the exact
Hensel lift, integral hyperbolic partner, reciprocal isometry, reverse
polar-kernel base change, fractional generator, and the actual rank-three
neighbor basis into one equality of `ℤ_p`-submodules. -/
theorem definingPrimeIsometry_completedSource_eq_completedNeighbor
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedSourceLattice.map
        (occurrenceDefiningPrimeIsometryPadicLinear hp2 occurrence) =
      completedOccurrenceNeighborLattice hp2 occurrence := by
  rw [completedOccurrenceNeighborLattice_eq_presentation]
  exact le_antisymm
    (definingPrimeIsometry_completedSource_le_presentation hp2 occurrence)
    (completedOccurrenceNeighborPresentation_le_definingPrimeIsometry_source
      hp2 occurrence)

#print axioms completedOccurrenceNeighborLattice_eq_presentation
#print axioms definingPrimeIsometry_completedSource_eq_completedNeighbor

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicCarrierImage

import ElementaryHolonics.Millennium.FamilyTunnellBrandtPadicHyperbolicPair

/-!
# Exact polar-kernel base change

The integral polar residue kernel embeds in `ℤ_p^3`.  Its entire `ℤ_p`-span
is exactly the completed kernel cut out by divisibility of the polar reading
by `p`.

The reverse inclusion is constructive.  If `w` is an integral polar-unit
partner for the retained direction `v`, and `b = B(v,w)`, then the three
vectors

`b e_i - B(e_i,v) w`

and `p w` lie in the integral residue kernel.  They reconstruct every
completed-kernel point after scalar extension; `b` is a unit in `ℤ_p`, so
it can be cancelled without losing the reconstruction fibre.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtPadicPolarKernelBaseChange

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicIsotropicLift
open Soma.Holonics.Millennium.FamilyTunnellBrandtPadicHensel

variable {p : ℕ} [Fact p.Prime]

/-- The completed polar kernel, expressed without a quotient: its polar
reading is an exact multiple of `p` in `ℤ_p`. -/
def completedOriginalPolarKernel (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Submodule ℤ_[p] (PadicTriple (p := p)) where
  carrier := {x | ∃ k : ℤ_[p],
    occurrencePadicPolar occurrence x
      (intTripleToPadic (occurrenceDirectionLift hp2 occurrence)) =
        (p : ℤ_[p]) * k}
  zero_mem' := by
    refine ⟨0, ?_⟩
    cases occurrence <;> simp [occurrencePadicPolar]
  add_mem' := by
    rintro x y ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [occurrencePadicPolar_add_left, ha, hb]
    ring
  smul_mem' := by
    rintro a x ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    rw [occurrencePadicPolar_smul_left, hb]
    ring

/-- Scalar extension of the already-owned integral polar residue kernel. -/
def integralPolarKernelPadicSpan (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    Submodule ℤ_[p] (PadicTriple (p := p)) :=
  Submodule.span ℤ_[p]
    (Set.range fun m : (occurrencePolarResidueHom hp2 occurrence).ker =>
      intTripleToPadic (p := p) (m : IntTriple))

/-- Every embedded integral residue-kernel point has a `p`-divisible completed
polar reading. -/
theorem intKernelPoint_mem_completedOriginalPolarKernel
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p))
    (m : (occurrencePolarResidueHom hp2 occurrence).ker) :
    intTripleToPadic (p := p) (m : IntTriple) ∈
      completedOriginalPolarKernel hp2 occurrence := by
  have hres :
      (occurrenceIntegralPolar occurrence (m : IntTriple)
        (occurrenceDirectionLift hp2 occurrence) : ZMod p) = 0 := by
    rw [occurrenceIntegralPolar_cast_residue hp2 occurrence]
    exact m.property
  have hdvd :
      (p : ℤ) ∣ occurrenceIntegralPolar occurrence (m : IntTriple)
        (occurrenceDirectionLift hp2 occurrence) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hres
  rcases hdvd with ⟨q, hq⟩
  refine ⟨(q : ℤ_[p]), ?_⟩
  rw [occurrencePadicPolar_intCast, hq]
  push_cast
  rfl

/-- The proved base-change direction. -/
theorem integralPolarKernelPadicSpan_le_completedOriginalPolarKernel
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    integralPolarKernelPadicSpan hp2 occurrence ≤
      completedOriginalPolarKernel hp2 occurrence := by
  apply Submodule.span_le.mpr
  rintro x ⟨m, rfl⟩
  exact intKernelPoint_mem_completedOriginalPolarKernel hp2 occurrence m

private def coordinateVector (i : Fin 3) : IntTriple :=
  match i with
  | ⟨0, _⟩ => (1, 0, 0)
  | ⟨1, _⟩ => (0, 1, 0)
  | ⟨2, _⟩ => (0, 0, 1)

/-- Integral residue-kernel generators obtained by subtracting the polar
component along the chosen unit partner. -/
private def integralKernelGenerator (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) : IntTriple :=
  occurrenceUnitPolarCoefficient hp2 occurrence • coordinateVector i -
    occurrenceIntegralPolar occurrence (coordinateVector i)
        (occurrenceDirectionLift hp2 occurrence) •
      occurrencePolarUnitWitness hp2 occurrence

private theorem integralKernelGenerator_polar_eq_zero (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    occurrenceIntegralPolar occurrence
      (integralKernelGenerator hp2 occurrence i)
      (occurrenceDirectionLift hp2 occurrence) = 0 := by
  fin_cases i <;>
    cases occurrence <;>
    simp [integralKernelGenerator, coordinateVector,
      occurrenceUnitPolarCoefficient, occurrenceIntegralPolar,
      intTunnellPolar, brandtSecondPolar] <;> ring

private def integralKernelGeneratorPoint (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    (occurrencePolarResidueHom hp2 occurrence).ker :=
  ⟨integralKernelGenerator hp2 occurrence i, by
    change occurrencePolarResidueHom hp2 occurrence
      (integralKernelGenerator hp2 occurrence i) = 0
    rw [← occurrenceIntegralPolar_cast_residue hp2 occurrence,
      integralKernelGenerator_polar_eq_zero hp2 occurrence i]
    simp⟩

private theorem integralKernelGenerator_mem_span (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (i : Fin 3) :
    intTripleToPadic (p := p) (integralKernelGenerator hp2 occurrence i) ∈
      integralPolarKernelPadicSpan hp2 occurrence := by
  exact Submodule.subset_span
    (Set.mem_range_self (integralKernelGeneratorPoint hp2 occurrence i))

private def primePolarPartnerPoint (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    (occurrencePolarResidueHom hp2 occurrence).ker :=
  ⟨(p : ℤ) • occurrencePolarUnitWitness hp2 occurrence, by
    change occurrencePolarResidueHom hp2 occurrence
      ((p : ℤ) • occurrencePolarUnitWitness hp2 occurrence) = 0
    rw [map_zsmul]
    simp⟩

private theorem primePolarPartner_mem_span (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) :
    intTripleToPadic (p := p)
      ((p : ℤ) • occurrencePolarUnitWitness hp2 occurrence) ∈
        integralPolarKernelPadicSpan hp2 occurrence := by
  exact Submodule.subset_span
    (Set.mem_range_self (primePolarPartnerPoint hp2 occurrence))

/-- The four integral kernel generators reconstruct the unit multiple of an
arbitrary completed point before the divisibility hypothesis is used. -/
private theorem integralKernelGenerator_reconstruction (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    (x : PadicTriple (p := p)) :
    (occurrenceUnitPolarCoefficient hp2 occurrence : ℤ_[p]) • x =
      x.1 • intTripleToPadic (p := p)
          (integralKernelGenerator hp2 occurrence 0) +
        x.2.1 • intTripleToPadic (p := p)
          (integralKernelGenerator hp2 occurrence 1) +
        x.2.2 • intTripleToPadic (p := p)
          (integralKernelGenerator hp2 occurrence 2) +
        occurrencePadicPolar occurrence x
            (intTripleToPadic
              (occurrenceDirectionLift hp2 occurrence)) •
          intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence) := by
  cases occurrence <;>
    ext <;>
    simp [integralKernelGenerator, coordinateVector,
      occurrenceUnitPolarCoefficient, occurrenceIntegralPolar,
      occurrencePadicPolar, intTripleToPadic, intTunnellPolar,
      brandtSecondPolar, smul_eq_mul] <;> ring

/-- Every completed polar-kernel point is generated by embedded integral
residue-kernel points. -/
theorem completedOriginalPolarKernel_le_integralPolarKernelPadicSpan
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    completedOriginalPolarKernel hp2 occurrence ≤
      integralPolarKernelPadicSpan hp2 occurrence := by
  rintro x ⟨k, hk⟩
  let S := integralPolarKernelPadicSpan hp2 occurrence
  let b : ℤ_[p] := occurrenceUnitPolarCoefficient hp2 occurrence
  have hlast :
      occurrencePadicPolar occurrence x
          (intTripleToPadic
            (occurrenceDirectionLift hp2 occurrence)) •
        intTripleToPadic (occurrencePolarUnitWitness hp2 occurrence) =
      k • intTripleToPadic (p := p)
        ((p : ℤ) • occurrencePolarUnitWitness hp2 occurrence) := by
    rw [hk]
    ext <;> simp [intTripleToPadic, smul_eq_mul] <;> ring
  have hscaled : b • x ∈ S := by
    rw [integralKernelGenerator_reconstruction hp2 occurrence, hlast]
    have h0 := Submodule.smul_mem S x.1
      (integralKernelGenerator_mem_span hp2 occurrence 0)
    have h1 := Submodule.smul_mem S x.2.1
      (integralKernelGenerator_mem_span hp2 occurrence 1)
    have h2 := Submodule.smul_mem S x.2.2
      (integralKernelGenerator_mem_span hp2 occurrence 2)
    have hpw := Submodule.smul_mem S k
      (primePolarPartner_mem_span hp2 occurrence)
    exact Submodule.add_mem S (Submodule.add_mem S
      (Submodule.add_mem S h0 h1) h2) hpw
  have hbNorm : ‖b‖ = 1 :=
    norm_intCast_eq_one_of_not_dvd
      (occurrenceUnitPolarCoefficient hp2 occurrence)
      (prime_not_dvd_occurrenceUnitPolarCoefficient hp2 occurrence)
  have hinv := S.smul_mem b.inv hscaled
  have hcancel : b.inv * b = 1 := by
    rw [mul_comm, PadicInt.mul_inv hbNorm]
  simpa only [smul_smul, hcancel, one_smul] using hinv

/-- Exact scalar-extension identity for the source polar residue kernel. -/
theorem integralPolarKernelPadicSpan_eq_completedOriginalPolarKernel
    (hp2 : p ≠ 2) (occurrence : BrandtNeighborOccurrence (p := p)) :
    integralPolarKernelPadicSpan hp2 occurrence =
      completedOriginalPolarKernel hp2 occurrence :=
  le_antisymm
    (integralPolarKernelPadicSpan_le_completedOriginalPolarKernel hp2 occurrence)
    (completedOriginalPolarKernel_le_integralPolarKernelPadicSpan hp2 occurrence)

#print axioms intKernelPoint_mem_completedOriginalPolarKernel
#print axioms integralPolarKernelPadicSpan_le_completedOriginalPolarKernel
#print axioms completedOriginalPolarKernel_le_integralPolarKernelPadicSpan
#print axioms integralPolarKernelPadicSpan_eq_completedOriginalPolarKernel

end Soma.Holonics.Millennium.FamilyTunnellBrandtPadicPolarKernelBaseChange

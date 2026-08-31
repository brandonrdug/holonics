import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex

/-!
# Exact localization of an actual Brandt neighbor at its defining prime

For an actual odd-prime neighbor, the source lattice and the returned neighbor
are separated only by the one `p`-turn: `pL ⊆ L' ⊆ p⁻¹L`.  This file proves
those inclusions in the common rational receiver and packages their exact
`p`-power saturation equivalence.  Thus the two lattices become equal after
inverting `p`, without claiming the unresolved local isometry at the `p`-adic
place or complete genus membership.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtLocalizeAtPrime

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborRankThree
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborWorldTube
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborQuotient
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighborCommonIndex

variable {p : ℕ} [Fact p.Prime]

private theorem rational_prime_ne_zero : (p : ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private theorem ratTripleScale_scale (a b : ℚ) (x : RatTriple) :
    ratTripleScale a (ratTripleScale b x) = ratTripleScale (a * b) x := by
  apply Prod.ext
  · simp [ratTripleScale]
    ring
  · apply Prod.ext <;> simp [ratTripleScale] <;> ring

omit [Fact p.Prime] in
private theorem ratTripleScale_prime_pow_succ (n : ℕ) (x : RatTriple) :
    ratTripleScale (p : ℚ) (ratTripleScale ((p : ℚ) ^ n) x) =
      ratTripleScale ((p : ℚ) ^ (n + 1)) x := by
  rw [ratTripleScale_scale]
  congr 1
  rw [pow_succ]
  ring

/-! ## The two exact one-turn inclusions -/

/-- Multiplying a source-lattice point by `p` lands in the actual neighbor.
This is the integral-kernel half of the `pL ⊆ L'` sandwich. -/
theorem prime_smul_source_mem_neighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    {x : RatTriple} (hx : x ∈ sourceIntegralLattice) :
    ratTripleScale (p : ℚ) x ∈ occurrenceNeighborSubgroup hp2 occurrence := by
  rw [sourceIntegralLattice, AddSubgroup.mem_map] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  simpa [ratTripleScaleP, intTripleInclusion] using
    BrandtNeighborOccurrence.scaled_integral_mem hp2 occurrence m

/-- Multiplying an actual neighbor point by `p` returns to the source lattice.
This is the fractional-generator half of the `L' ⊆ p⁻¹L` sandwich. -/
theorem prime_smul_neighbor_mem_source (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p))
    {x : RatTriple} (hx : x ∈ occurrenceNeighborSubgroup hp2 occurrence) :
    ratTripleScale (p : ℚ) x ∈ sourceIntegralLattice := by
  let y : occurrenceNeighborSubgroup hp2 occurrence := ⟨x, hx⟩
  rw [sourceIntegralLattice, AddSubgroup.mem_map]
  refine ⟨BrandtNeighborOccurrence.integralPScale hp2 occurrence y, trivial, ?_⟩
  simpa [ratTripleScaleP, y] using
    (BrandtNeighborOccurrence.intTripleInclusion_integralPScale hp2 occurrence y)

/-! ## Inverting the defining prime -/

/-- The exact `p`-power saturation of a rational point in a lattice.  This is
the concrete receiver for localization obtained by inverting `p`. -/
def primePowerSaturation (S : AddSubgroup RatTriple) (x : RatTriple) : Prop :=
  ∃ n : ℕ, ratTripleScale ((p : ℚ) ^ n) x ∈ S

/-- The source and actual-neighbor lattices have the same `p`-power saturation.
This is equality after inverting `p`; the possible difference at the defining
prime itself remains visible in the unsaturated subgroups. -/
theorem primePowerSaturation_source_iff_neighbor (hp2 : p ≠ 2)
    (occurrence : BrandtNeighborOccurrence (p := p)) (x : RatTriple) :
    primePowerSaturation (p := p) sourceIntegralLattice x ↔
      primePowerSaturation (p := p)
        (occurrenceNeighborSubgroup hp2 occurrence) x := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [← ratTripleScale_prime_pow_succ (p := p) n x]
    exact prime_smul_source_mem_neighbor hp2 occurrence hn
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [← ratTripleScale_prime_pow_succ (p := p) n x]
    exact prime_smul_neighbor_mem_source hp2 occurrence hn

#print axioms prime_smul_source_mem_neighbor
#print axioms prime_smul_neighbor_mem_source
#print axioms primePowerSaturation_source_iff_neighbor

end Soma.Holonics.Millennium.FamilyTunnellBrandtLocalizeAtPrime

import ElementaryHolonics.Millennium.FamilyTunnellPrimeSquareCensus

/-!
# The middle-zero boundary of the first Tunnell neighbor conic

For the first Brandt form

`Q₁(x,y,z) = 2x² + y² + 32z²`,

the projective neighbor directions carrying the pre-existing norm-one vector are
exactly the affine directions `(1,0,z)`.  Their isotropy equation is

`z² = -1/16`.

This file constructs that boundary as a finite addressed population and proves
its exact cardinality `1 + χ(-1)`.  The proof retains the chart embedding and
derives the character value through the nonzero square `(1/4)²`; it does not
appeal to a packaged conic-classification theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellMiddleZeroDirections

open Finset
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors

variable {p : ℕ} [Fact p.Prime]

/-- The complete addressed projective population whose normalized vector has
zero middle coordinate. -/
def middleZeroDirections : Finset ((ZMod p × ZMod p) ⊕ ZMod p) :=
  (projectiveConicDirections (((32 : ℤ) : ZMod p))).filter fun d =>
    (projectiveDirectionVector d).2.1 = 0

/-- The square-root chart to which the middle-zero boundary returns. -/
def middleZeroRootPopulation : Finset (ZMod p) :=
  Finset.univ.filter fun z => z ^ 2 = (-1 : ZMod p) / 16

/-- The root coordinate retains its affine projective address `(1,0,z)`. -/
def middleZeroRootEmbedding : ZMod p ↪ ((ZMod p × ZMod p) ⊕ ZMod p) where
  toFun z := .inl (0, z)
  inj' := by
    intro z w h
    simpa using h

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem sixteen_ne_zero (hp2 : p ≠ 2) : (16 : ZMod p) ≠ 0 := by
  rw [show (16 : ZMod p) = 2 ^ 4 by norm_num]
  exact pow_ne_zero 4 (two_ne_zero hp2)

/-- The affine root chart is exactly the complete middle-zero direction
population, including its projective chart address. -/
theorem middleZeroDirections_eq_root_map (hp2 : p ≠ 2) :
    middleZeroDirections (p := p) =
      (middleZeroRootPopulation (p := p)).map middleZeroRootEmbedding := by
  ext d
  cases d with
  | inl q =>
      rcases q with ⟨y, z⟩
      have hleft :
          Sum.inl (y, z) ∈
              projectiveConicDirections (((32 : ℤ) : ZMod p)) ↔
            2 + y ^ 2 + (32 : ZMod p) * z ^ 2 = 0 := by
        simp [projectiveConicDirections, affineConicPopulation]
      have hright :
          Sum.inl (y, z) ∈
              (middleZeroRootPopulation (p := p)).map middleZeroRootEmbedding ↔
            y = 0 ∧ z ^ 2 = (-1 : ZMod p) / 16 := by
        simp [middleZeroRootPopulation, middleZeroRootEmbedding, eq_comm, and_comm]
      simp only [middleZeroDirections, Finset.mem_filter,
        projectiveDirectionVector, hleft, hright]
      constructor
      · rintro ⟨hiso, hy⟩
        refine ⟨hy, ?_⟩
        have h2 := two_ne_zero (p := p) hp2
        have h16 := sixteen_ne_zero (p := p) hp2
        have hfactor : (2 : ZMod p) * (1 + 16 * z ^ 2) = 0 := by
          rw [hy] at hiso
          linear_combination hiso
        have hzero : 1 + 16 * z ^ 2 = 0 :=
          (mul_eq_zero.mp hfactor).resolve_left h2
        field_simp
        linear_combination hzero
      · rintro ⟨hy, hroot⟩
        refine ⟨?_, hy⟩
        have h16 := sixteen_ne_zero (p := p) hp2
        field_simp at hroot
        rw [hy]
        calc
          2 + 0 ^ 2 + (32 : ZMod p) * z ^ 2 =
              2 * (z ^ 2 * 16 + 1) := by ring
          _ = 2 * ((-1 : ZMod p) + 1) := by rw [hroot]
          _ = 0 := by ring
  | inr z =>
      simp [middleZeroDirections, projectiveDirectionVector,
        middleZeroRootPopulation, middleZeroRootEmbedding]

/-- The quadratic character does not see the nonzero square denominator `16`. -/
theorem quadraticChar_neg_one_div_sixteen (hp2 : p ≠ 2) :
    quadraticChar (ZMod p) ((-1 : ZMod p) / 16) =
      quadraticChar (ZMod p) (-1) := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 (two_ne_zero (p := p) hp2)
  have harg : ((-1 : ZMod p) / 16) =
      (-1 : ZMod p) * ((4 : ZMod p)⁻¹) ^ 2 := by
    rw [div_eq_mul_inv, show (16 : ZMod p) = 4 ^ 2 by norm_num, inv_pow]
  rw [harg, map_mul, quadraticChar_sq_one' (inv_ne_zero h4), mul_one]

/-- **THE MIDDLE-ZERO BOUNDARY HAS EXACT SIGNED CARDINALITY
`1 + χ(-1)`.** -/
theorem middleZeroDirections_card_cast (hp2 : p ≠ 2) :
    ((middleZeroDirections (p := p)).card : ℤ) =
      quadraticChar (ZMod p) (-1) + 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  rw [middleZeroDirections_eq_root_map (p := p) hp2, Finset.card_map]
  have hroot := quadraticChar_card_sqrts hchar ((-1 : ZMod p) / 16)
  have hroot' :
      (((Finset.univ.filter fun z : ZMod p =>
        z ^ 2 = (-1 : ZMod p) / 16).card : ℤ)) =
          quadraticChar (ZMod p) ((-1 : ZMod p) / 16) + 1 := by
    simpa [Set.toFinset_setOf] using hroot
  rw [middleZeroRootPopulation, hroot', quadraticChar_neg_one_div_sixteen hp2]

#print axioms middleZeroDirections_eq_root_map
#print axioms quadraticChar_neg_one_div_sixteen
#print axioms middleZeroDirections_card_cast

end Soma.Holonics.Millennium.FamilyTunnellMiddleZeroDirections

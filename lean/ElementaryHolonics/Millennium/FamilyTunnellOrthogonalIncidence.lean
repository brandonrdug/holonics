import ElementaryHolonics.Millennium.FamilyProjectiveBinaryQuadratic

/-!
# Orthogonal incidence on the Tunnell projective conic

The middle term in the ternary `T(p²)` coefficient law is the number of isotropic
directions orthogonal to a returned residue vector.  This file derives that number
from projective incidence.  It first closes the chart where the third coordinate of
the receiver vector is nonzero by eliminating the third direction coordinate and
transporting the intersection to the binary-projective carrier.

The discriminant of the restricted binary form returns

`-8 c m_z² Q_c(m) = (2m_z)² (-2c Q_c(m))`,

so its projective root count is `1+χ(-2cQ_c(m))`.  For the Tunnell coefficients
`c=8,32`, the factor `2c` is a square at every odd prime, leaving precisely the
quadratic middle orientation `χ(-Q_c(m))`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellOrthogonalIncidence

open Finset
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyProjectiveBinaryQuadratic

variable {p : ℕ} [Fact p.Prime]

/-- The half-polar incidence; the omitted factor two is invertible at odd primes. -/
def reducedTunnellHalfPolar (c : ZMod p)
    (m v : CoordinateTriple (ZMod p)) : ZMod p :=
  2 * m.1 * v.1 + m.2.1 * v.2.1 + c * m.2.2 * v.2.2

/-- Isotropic projective directions meeting the receiver vector orthogonally. -/
def orthogonalProjectiveDirections (c : ZMod p)
    (m : CoordinateTriple (ZMod p)) :
    Finset ((ZMod p × ZMod p) ⊕ ZMod p) :=
  (projectiveConicDirections c).filter fun d =>
    reducedTunnellHalfPolar c m (projectiveDirectionVector d) = 0

/-! ## Eliminate the third coordinate when `m_z ≠ 0` -/

def zElimA (c : ZMod p) (m : CoordinateTriple (ZMod p)) : ZMod p :=
  2 * c * m.2.2 ^ 2 + 4 * m.1 ^ 2

def zElimB (m : CoordinateTriple (ZMod p)) : ZMod p :=
  4 * m.1 * m.2.1

def zElimC (c : ZMod p) (m : CoordinateTriple (ZMod p)) : ZMod p :=
  c * m.2.2 ^ 2 + m.2.1 ^ 2

private def zElimForward :
    ((ZMod p × ZMod p) ⊕ ZMod p) → (ZMod p ⊕ Unit)
  | .inl q => .inl q.1
  | .inr _ => .inr ()

private def zElimBackward (c : ZMod p) (m : CoordinateTriple (ZMod p)) :
    (ZMod p ⊕ Unit) → ((ZMod p × ZMod p) ⊕ ZMod p)
  | .inl y => .inl (y, -(2 * m.1 + m.2.1 * y) / (c * m.2.2))
  | .inr _ => .inr (-m.2.1 / (c * m.2.2))

private theorem zElim_coefficients_nonzero (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) (m : CoordinateTriple (ZMod p))
    (hmz : m.2.2 ≠ 0) :
    zElimA c m ≠ 0 ∨ zElimB m ≠ 0 ∨ zElimC c m ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 h2
  by_cases hmx : m.1 = 0
  · left
    simpa [zElimA, hmx] using
      mul_ne_zero (mul_ne_zero h2 hc) (pow_ne_zero 2 hmz)
  · by_cases hmy : m.2.1 = 0
    · right; right
      simpa [zElimC, hmy] using mul_ne_zero hc (pow_ne_zero 2 hmz)
    · right; left
      exact mul_ne_zero (mul_ne_zero h4 hmx) hmy

private theorem zElim_card (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) (m : CoordinateTriple (ZMod p))
    (hmz : m.2.2 ≠ 0) :
    (orthogonalProjectiveDirections c m).card =
      (binaryProjectiveZeros (zElimA c m) (zElimB m) (zElimC c m)).card := by
  classical
  have hcmz : c * m.2.2 ≠ 0 := mul_ne_zero hc hmz
  refine Finset.card_nbij' zElimForward (zElimBackward c m) ?_ ?_ ?_ ?_
  · intro d hd
    have hd' : d ∈ projectiveConicDirections c ∧
        reducedTunnellHalfPolar c m (projectiveDirectionVector d) = 0 := by
      simpa [orthogonalProjectiveDirections] using hd
    have hdmem := hd'.1
    have hpolar := hd'.2
    cases d with
    | inl q =>
        have hq : 2 + q.1 ^ 2 + c * q.2 ^ 2 = 0 := by
          simpa [projectiveConicDirections, affineConicPopulation] using hdmem
        rw [Finset.mem_coe]
        simp only [binaryProjectiveZeros, Finset.mem_disjSum]
        left
        refine ⟨q.1, ?_, rfl⟩
        simp only [binaryAffineZeros, Finset.mem_filter, Finset.mem_univ, true_and]
        change zElimA c m + zElimB m * q.1 + zElimC c m * q.1 ^ 2 = 0
        have hL : 2 * m.1 + m.2.1 * q.1 + c * m.2.2 * q.2 = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector] using hpolar
        unfold zElimA zElimB zElimC
        linear_combination c * m.2.2 ^ 2 * hq +
          (2 * m.1 + m.2.1 * q.1 - c * m.2.2 * q.2) * hL
    | inr z =>
        have hq : 1 + c * z ^ 2 = 0 := by
          simpa [projectiveConicDirections, infinityConicPopulation] using hdmem
        have hL : m.2.1 + c * m.2.2 * z = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector] using hpolar
        rw [Finset.mem_coe]
        simp only [binaryProjectiveZeros, Finset.mem_disjSum]
        right
        refine ⟨(), ?_, rfl⟩
        simp only [binaryInfinityZeros]
        rw [if_pos]
        · simp
        · unfold zElimC
          linear_combination c * m.2.2 ^ 2 * hq +
            (m.2.1 - c * m.2.2 * z) * hL
  · intro d hd
    cases d with
    | inl y =>
        have hF :
            zElimA c m + zElimB m * y + zElimC c m * y ^ 2 = 0 := by
          simpa [binaryProjectiveZeros, binaryAffineZeros] using hd
        let z := -(2 * m.1 + m.2.1 * y) / (c * m.2.2)
        have hL : 2 * m.1 + m.2.1 * y + c * m.2.2 * z = 0 := by
          dsimp [z]
          field_simp
          ring
        have hqscaled : c * m.2.2 ^ 2 * (2 + y ^ 2 + c * z ^ 2) = 0 := by
          unfold zElimA zElimB zElimC at hF
          linear_combination hF -
            (2 * m.1 + m.2.1 * y - c * m.2.2 * z) * hL
        have hfactor : c * m.2.2 ^ 2 ≠ 0 :=
          mul_ne_zero hc (pow_ne_zero 2 hmz)
        have hq : 2 + y ^ 2 + c * z ^ 2 = 0 :=
          (mul_eq_zero.mp hqscaled).resolve_left hfactor
        rw [Finset.mem_coe]
        simp only [orthogonalProjectiveDirections, Finset.mem_filter]
        constructor
        · simp [projectiveConicDirections, affineConicPopulation,
            zElimBackward]
          convert hq using 1 <;> ring
        · simpa [zElimBackward, reducedTunnellHalfPolar,
            projectiveDirectionVector, z] using hL
    | inr u =>
        rcases u with ⟨⟩
        have hdInfinity : () ∈ binaryInfinityZeros (zElimC c m) := by
          simpa [binaryProjectiveZeros] using hd
        have hC : zElimC c m = 0 := by
          by_contra hC
          simp [binaryInfinityZeros, hC] at hdInfinity
        let z := -m.2.1 / (c * m.2.2)
        have hL : m.2.1 + c * m.2.2 * z = 0 := by
          dsimp [z]
          field_simp
          ring
        have hqscaled : c * m.2.2 ^ 2 * (1 + c * z ^ 2) = 0 := by
          unfold zElimC at hC
          linear_combination hC - (m.2.1 - c * m.2.2 * z) * hL
        have hfactor : c * m.2.2 ^ 2 ≠ 0 :=
          mul_ne_zero hc (pow_ne_zero 2 hmz)
        have hq : 1 + c * z ^ 2 = 0 :=
          (mul_eq_zero.mp hqscaled).resolve_left hfactor
        rw [Finset.mem_coe]
        simp only [orthogonalProjectiveDirections, Finset.mem_filter]
        constructor
        · simp [projectiveConicDirections, infinityConicPopulation,
            zElimBackward, z, hq]
        · simpa [zElimBackward, reducedTunnellHalfPolar,
            projectiveDirectionVector, z] using hL
  · intro d hd
    cases d with
    | inl q =>
        dsimp [zElimForward, zElimBackward]
        simp only [Sum.inl.injEq]
        apply Prod.ext
        · rfl
        · have hpolar :
              reducedTunnellHalfPolar c m (projectiveDirectionVector (.inl q)) = 0 := by
            have hd' : (.inl q) ∈ projectiveConicDirections c ∧
                reducedTunnellHalfPolar c m (projectiveDirectionVector (.inl q)) = 0 := by
              simpa [orthogonalProjectiveDirections] using hd
            exact hd'.2
          have hL : 2 * m.1 + m.2.1 * q.1 + c * m.2.2 * q.2 = 0 := by
            simpa [reducedTunnellHalfPolar, projectiveDirectionVector] using hpolar
          field_simp
          linear_combination -1 * hL
    | inr z =>
        dsimp [zElimForward, zElimBackward]
        simp only [Sum.inr.injEq]
        have hd' : (.inr z) ∈ projectiveConicDirections c ∧
            reducedTunnellHalfPolar c m (projectiveDirectionVector (.inr z)) = 0 := by
          simpa [orthogonalProjectiveDirections] using hd
        have hpolar := hd'.2
        have hL : m.2.1 + c * m.2.2 * z = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector] using hpolar
        field_simp
        linear_combination -1 * hL
  · intro d hd
    cases d <;> rfl

private theorem zElim_discriminant (c : ZMod p)
    (m : CoordinateTriple (ZMod p)) :
    binaryDiscriminant (zElimA c m) (zElimB m) (zElimC c m) =
      (2 * m.2.2) ^ 2 *
        (-2 * c * reducedTunnellQuadratic c m) := by
  simp [binaryDiscriminant, zElimA, zElimB, zElimC,
    reducedTunnellQuadratic]
  ring

/-- The orthogonal incidence count in the third-coordinate elimination chart. -/
theorem orthogonalProjectiveDirections_card_of_third_ne_zero (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) (m : CoordinateTriple (ZMod p))
    (hmz : m.2.2 ≠ 0) :
    ((orthogonalProjectiveDirections c m).card : ℤ) =
      quadraticChar (ZMod p) (-2 * c * reducedTunnellQuadratic c m) + 1 := by
  have hbinary := binaryProjectiveZeros_card_cast (p := p) hp2
    (zElim_coefficients_nonzero hp2 hc m hmz)
  have hcard := zElim_card (p := p) hp2 hc m hmz
  rw [hcard, hbinary, zElim_discriminant]
  rw [map_mul, quadraticChar_sq_one']
  · ring
  · exact mul_ne_zero (by
      apply Ring.two_ne_zero
      rw [ZMod.ringChar_zmod_n]
      exact hp2) hmz

#print axioms orthogonalProjectiveDirections_card_of_third_ne_zero

/-! ## Eliminate the second coordinate when `m_z = 0` and `m_y ≠ 0` -/

def yElimA (m : CoordinateTriple (ZMod p)) : ZMod p :=
  2 * m.2.1 ^ 2 + 4 * m.1 ^ 2

def yElimC (c : ZMod p) (m : CoordinateTriple (ZMod p)) : ZMod p :=
  c * m.2.1 ^ 2

private def yElimForward :
    ((ZMod p × ZMod p) ⊕ ZMod p) → (ZMod p ⊕ Unit)
  | .inl q => .inl q.2
  | .inr _ => .inr ()

private def yElimBackward (m : CoordinateTriple (ZMod p)) :
    (ZMod p ⊕ Unit) → ((ZMod p × ZMod p) ⊕ ZMod p)
  | .inl z => .inl (-2 * m.1 / m.2.1, z)
  | .inr _ => .inr 0

private theorem yElim_card (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) (m : CoordinateTriple (ZMod p))
    (hmz : m.2.2 = 0) (hmy : m.2.1 ≠ 0) :
    (orthogonalProjectiveDirections c m).card =
      (binaryProjectiveZeros (yElimA m) 0 (yElimC c m)).card := by
  classical
  have hC : yElimC c m ≠ 0 :=
    mul_ne_zero hc (pow_ne_zero 2 hmy)
  refine Finset.card_nbij' yElimForward (yElimBackward m) ?_ ?_ ?_ ?_
  · intro d hd
    have hd' : d ∈ projectiveConicDirections c ∧
        reducedTunnellHalfPolar c m (projectiveDirectionVector d) = 0 := by
      simpa [orthogonalProjectiveDirections] using hd
    cases d with
    | inl q =>
        have hq : 2 + q.1 ^ 2 + c * q.2 ^ 2 = 0 := by
          simpa [projectiveConicDirections, affineConicPopulation] using hd'.1
        have hL : 2 * m.1 + m.2.1 * q.1 = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector, hmz] using hd'.2
        rw [Finset.mem_coe]
        simp only [binaryProjectiveZeros, Finset.mem_disjSum]
        left
        refine ⟨q.2, ?_, rfl⟩
        simp only [binaryAffineZeros, Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [zero_mul, add_zero]
        unfold yElimA yElimC
        linear_combination m.2.1 ^ 2 * hq +
          (2 * m.1 - m.2.1 * q.1) * hL
    | inr z =>
        have hL : m.2.1 = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector, hmz] using hd'.2
        exact (hmy hL).elim
  · intro d hd
    cases d with
    | inl z =>
        have hF : yElimA m + yElimC c m * z ^ 2 = 0 := by
          simpa [binaryProjectiveZeros, binaryAffineZeros] using hd
        let y := -2 * m.1 / m.2.1
        have hL : 2 * m.1 + m.2.1 * y = 0 := by
          dsimp [y]
          field_simp
          ring
        have hqscaled : m.2.1 ^ 2 * (2 + y ^ 2 + c * z ^ 2) = 0 := by
          unfold yElimA yElimC at hF
          linear_combination hF - (2 * m.1 - m.2.1 * y) * hL
        have hq : 2 + y ^ 2 + c * z ^ 2 = 0 :=
          (mul_eq_zero.mp hqscaled).resolve_left (pow_ne_zero 2 hmy)
        rw [Finset.mem_coe]
        simp only [orthogonalProjectiveDirections, Finset.mem_filter]
        constructor
        · simpa [projectiveConicDirections, affineConicPopulation,
            yElimBackward, y] using hq
        · simpa [yElimBackward, reducedTunnellHalfPolar,
            projectiveDirectionVector, hmz, y] using hL
    | inr u =>
        rcases u with ⟨⟩
        have hInfinity : () ∈ binaryInfinityZeros (yElimC c m) := by
          simpa [binaryProjectiveZeros] using hd
        exfalso
        simp [binaryInfinityZeros, hC] at hInfinity
  · intro d hd
    cases d with
    | inl q =>
        dsimp [yElimForward, yElimBackward]
        simp only [Sum.inl.injEq]
        apply Prod.ext
        · have hd' : (.inl q) ∈ projectiveConicDirections c ∧
              reducedTunnellHalfPolar c m (projectiveDirectionVector (.inl q)) = 0 := by
            simpa [orthogonalProjectiveDirections] using hd
          have hL : 2 * m.1 + m.2.1 * q.1 = 0 := by
            simpa [reducedTunnellHalfPolar, projectiveDirectionVector, hmz] using hd'.2
          field_simp
          linear_combination -1 * hL
        · rfl
    | inr z =>
        have hd' : (.inr z) ∈ projectiveConicDirections c ∧
            reducedTunnellHalfPolar c m (projectiveDirectionVector (.inr z)) = 0 := by
          simpa [orthogonalProjectiveDirections] using hd
        have hL : m.2.1 = 0 := by
          simpa [reducedTunnellHalfPolar, projectiveDirectionVector, hmz] using hd'.2
        exact (hmy hL).elim
  · intro d hd
    cases d with
    | inl z => rfl
    | inr u =>
        rcases u with ⟨⟩
        have hInfinity : () ∈ binaryInfinityZeros (yElimC c m) := by
          simpa [binaryProjectiveZeros] using hd
        exfalso
        simp [binaryInfinityZeros, hC] at hInfinity

private theorem yElim_discriminant (c : ZMod p)
    (m : CoordinateTriple (ZMod p)) (hmz : m.2.2 = 0) :
    binaryDiscriminant (yElimA m) 0 (yElimC c m) =
      (2 * m.2.1) ^ 2 * (-2 * c * reducedTunnellQuadratic c m) := by
  simp [binaryDiscriminant, yElimA, yElimC, reducedTunnellQuadratic, hmz]
  ring

/-- The orthogonal incidence count when the third receiver coordinate vanishes
but the second one does not. -/
theorem orthogonalProjectiveDirections_card_of_third_zero_second_ne_zero
    (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0)
    (m : CoordinateTriple (ZMod p)) (hmz : m.2.2 = 0) (hmy : m.2.1 ≠ 0) :
    ((orthogonalProjectiveDirections c m).card : ℤ) =
      quadraticChar (ZMod p) (-2 * c * reducedTunnellQuadratic c m) + 1 := by
  have hbinary := binaryProjectiveZeros_card_cast (p := p) hp2
    (A := yElimA m) (B := 0) (C := yElimC c m)
    (Or.inr (Or.inr (mul_ne_zero hc (pow_ne_zero 2 hmy))))
  have hcard := yElim_card (p := p) hp2 hc m hmz hmy
  rw [hcard, hbinary, yElim_discriminant c m hmz]
  rw [map_mul, quadraticChar_sq_one']
  · ring
  · exact mul_ne_zero (by
      apply Ring.two_ne_zero
      rw [ZMod.ringChar_zmod_n]
      exact hp2) hmy

#print axioms orthogonalProjectiveDirections_card_of_third_zero_second_ne_zero

/-! ## The remaining coordinate axis and the uniform incidence law -/

private theorem orthogonalProjectiveDirections_eq_infinity_of_axis
    (hp2 : p ≠ 2) (c : ZMod p) (m : CoordinateTriple (ZMod p))
    (hmz : m.2.2 = 0) (hmy : m.2.1 = 0) (hmx : m.1 ≠ 0) :
    orthogonalProjectiveDirections c m =
      (∅ : Finset (ZMod p × ZMod p)).disjSum (infinityConicPopulation c) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2mx : (2 : ZMod p) * m.1 ≠ 0 :=
    mul_ne_zero (Ring.two_ne_zero hchar) hmx
  ext d
  cases d with
  | inl q =>
      simp [orthogonalProjectiveDirections, projectiveConicDirections,
        reducedTunnellHalfPolar, projectiveDirectionVector, hmz, hmy, h2mx]
  | inr z =>
      simp [orthogonalProjectiveDirections, projectiveConicDirections,
        reducedTunnellHalfPolar, projectiveDirectionVector, hmz, hmy]

/-- If only the first receiver coordinate survives, orthogonality forces the
isotropic line into the infinity chart and the same discriminant character returns. -/
theorem orthogonalProjectiveDirections_card_of_axis
    (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0)
    (m : CoordinateTriple (ZMod p)) (hmz : m.2.2 = 0)
    (hmy : m.2.1 = 0) (hmx : m.1 ≠ 0) :
    ((orthogonalProjectiveDirections c m).card : ℤ) =
      quadraticChar (ZMod p) (-2 * c * reducedTunnellQuadratic c m) + 1 := by
  rw [orthogonalProjectiveDirections_eq_infinity_of_axis hp2 c m hmz hmy hmx,
    Finset.card_disjSum, Finset.card_empty, zero_add,
    infinityConicPopulation_card_cast hp2 hc]
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2mx : (2 : ZMod p) * m.1 ≠ 0 :=
    mul_ne_zero (Ring.two_ne_zero hchar) hmx
  have harg :
      -2 * c * reducedTunnellQuadratic c m = (-c) * (2 * m.1) ^ 2 := by
    simp [reducedTunnellQuadratic, hmz, hmy]
    ring
  rw [harg, map_mul, quadraticChar_sq_one' h2mx]
  ring

/-- **UNIFORM NONZERO ORTHOGONAL-INCIDENCE LAW.**

Every nonzero returned residue vector has exactly the discriminant-governed
population of isotropic neighbor directions, independent of which coordinate chart
is available. -/
theorem orthogonalProjectiveDirections_card_of_ne_zero
    (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0)
    (m : CoordinateTriple (ZMod p)) (hm : m ≠ 0) :
    ((orthogonalProjectiveDirections c m).card : ℤ) =
      quadraticChar (ZMod p) (-2 * c * reducedTunnellQuadratic c m) + 1 := by
  by_cases hmz : m.2.2 = 0
  · by_cases hmy : m.2.1 = 0
    · have hmx : m.1 ≠ 0 := by
        intro hmx
        apply hm
        rcases m with ⟨mx, my, mz⟩
        simp_all
      exact orthogonalProjectiveDirections_card_of_axis hp2 hc m hmz hmy hmx
    · exact orthogonalProjectiveDirections_card_of_third_zero_second_ne_zero
        hp2 hc m hmz hmy
  · exact orthogonalProjectiveDirections_card_of_third_ne_zero hp2 hc m hmz

/-- The zero receiver is orthogonal to every projective neighbor direction. -/
theorem orthogonalProjectiveDirections_zero_card
    (hp2 : p ≠ 2) {c : ZMod p} (hc : c ≠ 0) :
    (orthogonalProjectiveDirections c (0, 0, 0)).card = p + 1 := by
  have hall : orthogonalProjectiveDirections c (0, 0, 0) =
      projectiveConicDirections c := by
    ext d
    simp [orthogonalProjectiveDirections, reducedTunnellHalfPolar]
  rw [hall, projectiveConicDirections_card hp2 hc]

#print axioms orthogonalProjectiveDirections_card_of_ne_zero
#print axioms orthogonalProjectiveDirections_zero_card

end Soma.Holonics.Millennium.FamilyTunnellOrthogonalIncidence

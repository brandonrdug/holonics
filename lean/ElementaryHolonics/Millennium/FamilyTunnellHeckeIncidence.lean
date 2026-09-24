import ElementaryHolonics.Millennium.FamilyTunnellIntegralNeighbors
import ElementaryHolonics.Millennium.FamilyTunnellOrthogonalIncidence

/-!
# The middle Tunnell Hecke layer as a finite incidence population

The projective-neighbor directions and the integral Tunnell lattice meet in one
finite incidence plate.  For every integral vector `m`, the fiber over `m` is the
complete population of isotropic directions orthogonal to `m mod p`.  The previous
projective calculation then returns exactly the quadratic-character coefficient in
the half-integral `T(p²)` law, with the exceptional `p+1` fiber occurring precisely
when all three coordinates vanish modulo `p`.

This file does not assume a packaged Hecke theorem.  It constructs the occurrence
population and proves its fiberwise count from the finite conic swings.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence

open Finset
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellOrthogonalIncidence
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.LatticeCount

variable {p : ℕ} [Fact p.Prime]

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem eight_ne_zero (hp2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  rw [show (8 : ZMod p) = 2 ^ 3 by norm_num]
  exact pow_ne_zero 3 (two_ne_zero hp2)

private theorem thirtyTwo_ne_zero (hp2 : p ≠ 2) : (32 : ZMod p) ≠ 0 := by
  rw [show (32 : ZMod p) = 2 ^ 5 by norm_num]
  exact pow_ne_zero 5 (two_ne_zero hp2)

/-- In the thin form the discriminant factor `2c=16` is the square `4²`. -/
theorem quadraticChar_tunnellFactor_eight (hp2 : p ≠ 2) (q : ZMod p) :
    quadraticChar (ZMod p) (-2 * 8 * q) = quadraticChar (ZMod p) (-q) := by
  have h4 : (4 : ZMod p) ≠ 0 := by
    rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
    exact pow_ne_zero 2 (two_ne_zero hp2)
  have harg : -2 * (8 : ZMod p) * q = (-q) * (4 : ZMod p) ^ 2 := by ring
  rw [harg, map_mul, quadraticChar_sq_one' h4, mul_one]

/-- In the thick form the discriminant factor `2c=64` is the square `8²`. -/
theorem quadraticChar_tunnellFactor_thirtyTwo (hp2 : p ≠ 2) (q : ZMod p) :
    quadraticChar (ZMod p) (-2 * 32 * q) = quadraticChar (ZMod p) (-q) := by
  have h8 : (8 : ZMod p) ≠ 0 := eight_ne_zero hp2
  have harg : -2 * (32 : ZMod p) * q = (-q) * (8 : ZMod p) ^ 2 := by ring
  rw [harg, map_mul, quadraticChar_sq_one' h8, mul_one]

/-- The complete incidence fiber over one integral vector. -/
def integralOrthogonalDirections (C : ℤ) (m : IntTriple) :
    Finset ((ZMod p × ZMod p) ⊕ ZMod p) :=
  orthogonalProjectiveDirections (C : ZMod p) (reduceTriple (p := p) m)

/-- Thin-lattice pointwise incidence.  The two branches distinguish the retained
projective quotient fiber from the origin where projectivization has no direction. -/
theorem thin_integralOrthogonalDirections_card (hp2 : p ≠ 2) (m : IntTriple) :
    ((integralOrthogonalDirections (p := p) 8 m).card : ℤ) =
      if reduceTriple (p := p) m = 0 then (p : ℤ) + 1
      else quadraticChar (ZMod p) (-(intTunnellQuadratic 8 m : ZMod p)) + 1 := by
  by_cases hm : reduceTriple (p := p) m = 0
  · rw [if_pos hm]
    unfold integralOrthogonalDirections
    rw [hm]
    exact_mod_cast orthogonalProjectiveDirections_zero_card
      (p := p) hp2 (c := ((8 : ℤ) : ZMod p)) (by simpa using eight_ne_zero hp2)
  · rw [if_neg hm]
    unfold integralOrthogonalDirections
    have hc8 : ((8 : ℤ) : ZMod p) ≠ 0 := by simpa using eight_ne_zero hp2
    have hfactor : ∀ q : ZMod p,
        quadraticChar (ZMod p) (-2 * ((8 : ℤ) : ZMod p) * q) =
          quadraticChar (ZMod p) (-q) := by
      intro q
      simpa using quadraticChar_tunnellFactor_eight (p := p) hp2 q
    calc
      ((orthogonalProjectiveDirections ((8 : ℤ) : ZMod p)
          (reduceTriple (p := p) m)).card : ℤ) =
          quadraticChar (ZMod p)
            (-2 * ((8 : ℤ) : ZMod p) * reducedTunnellQuadratic ((8 : ℤ) : ZMod p)
              (reduceTriple (p := p) m)) + 1 :=
        orthogonalProjectiveDirections_card_of_ne_zero hp2
          hc8 (reduceTriple (p := p) m) hm
      _ = quadraticChar (ZMod p)
          (-reducedTunnellQuadratic ((8 : ℤ) : ZMod p) (reduceTriple (p := p) m)) + 1 := by
            rw [hfactor]
      _ = quadraticChar (ZMod p) (-(intTunnellQuadratic 8 m : ZMod p)) + 1 := by
            rw [cast_intTunnellQuadratic]

/-- Thick-lattice pointwise incidence. -/
theorem thick_integralOrthogonalDirections_card (hp2 : p ≠ 2) (m : IntTriple) :
    ((integralOrthogonalDirections (p := p) 32 m).card : ℤ) =
      if reduceTriple (p := p) m = 0 then (p : ℤ) + 1
      else quadraticChar (ZMod p) (-(intTunnellQuadratic 32 m : ZMod p)) + 1 := by
  by_cases hm : reduceTriple (p := p) m = 0
  · rw [if_pos hm]
    unfold integralOrthogonalDirections
    rw [hm]
    exact_mod_cast orthogonalProjectiveDirections_zero_card
      (p := p) hp2 (c := ((32 : ℤ) : ZMod p)) (by simpa using thirtyTwo_ne_zero hp2)
  · rw [if_neg hm]
    unfold integralOrthogonalDirections
    have hc32 : ((32 : ℤ) : ZMod p) ≠ 0 := by simpa using thirtyTwo_ne_zero hp2
    have hfactor : ∀ q : ZMod p,
        quadraticChar (ZMod p) (-2 * ((32 : ℤ) : ZMod p) * q) =
          quadraticChar (ZMod p) (-q) := by
      intro q
      simpa using quadraticChar_tunnellFactor_thirtyTwo (p := p) hp2 q
    calc
      ((orthogonalProjectiveDirections ((32 : ℤ) : ZMod p)
          (reduceTriple (p := p) m)).card : ℤ) =
          quadraticChar (ZMod p)
            (-2 * ((32 : ℤ) : ZMod p) * reducedTunnellQuadratic ((32 : ℤ) : ZMod p)
              (reduceTriple (p := p) m)) + 1 :=
        orthogonalProjectiveDirections_card_of_ne_zero hp2
          hc32 (reduceTriple (p := p) m) hm
      _ = quadraticChar (ZMod p)
          (-reducedTunnellQuadratic ((32 : ℤ) : ZMod p) (reduceTriple (p := p) m)) + 1 := by
            rw [hfactor]
      _ = quadraticChar (ZMod p) (-(intTunnellQuadratic 32 m : ZMod p)) + 1 := by
            rw [cast_intTunnellQuadratic]

/-- All addressed pairs `(integral vector, projective neighbor direction)` meeting
the polar incidence relation. -/
def integralOrthogonalIncidencePopulation (C : ℤ) (s : Finset IntTriple) :
    Finset (IntTriple × ((ZMod p × ZMod p) ⊕ ZMod p)) :=
  (s ×ˢ projectiveConicDirections (C : ZMod p)).filter fun md =>
    reducedTunnellHalfPolar (C : ZMod p) (reduceTriple (p := p) md.1)
      (projectiveDirectionVector md.2) = 0

/-- The total incidence population is the exact sum of its complete vector fibers. -/
theorem integralOrthogonalIncidencePopulation_card (C : ℤ) (s : Finset IntTriple) :
    (integralOrthogonalIncidencePopulation (p := p) C s).card =
      ∑ m ∈ s, (integralOrthogonalDirections (p := p) C m).card := by
  unfold integralOrthogonalIncidencePopulation integralOrthogonalDirections
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro m hm
  unfold orthogonalProjectiveDirections
  rw [Finset.card_filter]

/-- The direction carried by an incidence occurrence, with its projective
membership retained as a subtype witness. -/
def incidenceProjectiveDirection (C : ℤ) (s : Finset IntTriple)
    (q : {q // q ∈ integralOrthogonalIncidencePopulation (p := p) C s}) :
    ProjectiveConicDirection (p := p) (C : ZMod p) := by
  refine ⟨q.1.2, ?_⟩
  have hq := q.2
  simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
    Finset.mem_product] at hq
  exact hq.1.2

/-- **EVERY LOWER INCIDENCE OCCURRENCE IS AN ACTUAL NEIGHBOR POINT.** -/
theorem incidenceVector_mem_integralNeighbor (hp2 : p ≠ 2)
    (C : ℤ) (s : Finset IntTriple)
    (q : {q // q ∈ integralOrthogonalIncidencePopulation (p := p) C s}) :
    intTripleToRat q.1.1 ∈ integralNeighbor (p := p) C
      (incidenceProjectiveDirection (p := p) C s q) := by
  apply intTripleToRat_mem_integralNeighbor_of_polar_zero hp2
  have hq := q.2
  simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
    Finset.mem_product] at hq
  have horth := hq.2
  rw [cast_intTunnellPolar]
  change 2 * reducedTunnellHalfPolar (C : ZMod p)
    (reduceTriple (p := p) q.1.1)
    (reduceTriple (p := p) (adjustedDirectionLift C
      (incidenceProjectiveDirection (p := p) C s q))) = 0
  rw [reduce_adjustedDirectionLift hp2]
  exact mul_eq_zero_of_right 2 horth

/-! ## The exact middle/quotient split -/

/-- Vectors whose complete coordinate address vanishes in the prime receiver. -/
def zeroResiduePopulation (s : Finset IntTriple) : Finset IntTriple :=
  s.filter fun m => reduceTriple (p := p) m = 0

/-- Vectors retaining a nonzero projective direction after reduction. -/
def nonzeroResiduePopulation (s : Finset IntTriple) : Finset IntTriple :=
  s.filter fun m => reduceTriple (p := p) m ≠ 0

private theorem split_incidence_sum (C : ℤ) (s : Finset IntTriple) :
    (∑ m ∈ s, ((integralOrthogonalDirections (p := p) C m).card : ℤ)) =
      (∑ m ∈ zeroResiduePopulation (p := p) s,
        ((integralOrthogonalDirections (p := p) C m).card : ℤ)) +
      (∑ m ∈ nonzeroResiduePopulation (p := p) s,
        ((integralOrthogonalDirections (p := p) C m).card : ℤ)) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s
    (fun m : IntTriple => reduceTriple (p := p) m = 0)
    (fun m => ((integralOrthogonalDirections (p := p) C m).card : ℤ))
  simpa [zeroResiduePopulation, nonzeroResiduePopulation] using hsplit.symm

/-- The complete thin incidence plate separates into the `p+1` zero-residue fiber
and the quadratic-character middle fiber whenever the source population lies on one
norm level. -/
theorem thin_incidence_middle_quotient_split (hp2 : p ≠ 2)
    (s : Finset IntTriple) (n : ℤ)
    (hnorm : ∀ m ∈ s, intTunnellQuadratic 8 m = n) :
    ((integralOrthogonalIncidencePopulation (p := p) 8 s).card : ℤ) =
      ((p : ℤ) + 1) * ((zeroResiduePopulation (p := p) s).card : ℤ) +
      (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) *
        ((nonzeroResiduePopulation (p := p) s).card : ℤ) := by
  have hcard :
      ((integralOrthogonalIncidencePopulation (p := p) 8 s).card : ℤ) =
        ∑ m ∈ s, ((integralOrthogonalDirections (p := p) 8 m).card : ℤ) := by
    exact_mod_cast integralOrthogonalIncidencePopulation_card (p := p) 8 s
  rw [hcard, split_incidence_sum]
  congr 1
  · calc
      (∑ m ∈ zeroResiduePopulation (p := p) s,
          ((integralOrthogonalDirections (p := p) 8 m).card : ℤ)) =
          ∑ _m ∈ zeroResiduePopulation (p := p) s, ((p : ℤ) + 1) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hm0 : reduceTriple (p := p) m = 0 := by
              have hm' : m ∈ s ∧ reduceTriple (p := p) m = 0 := by
                simpa [zeroResiduePopulation] using hm
              exact hm'.2
            rw [thin_integralOrthogonalDirections_card hp2, if_pos hm0]
      _ = ((p : ℤ) + 1) * ((zeroResiduePopulation (p := p) s).card : ℤ) := by
            simp
            ring
  · calc
      (∑ m ∈ nonzeroResiduePopulation (p := p) s,
          ((integralOrthogonalDirections (p := p) 8 m).card : ℤ)) =
          ∑ _m ∈ nonzeroResiduePopulation (p := p) s,
            (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) := by
              apply Finset.sum_congr rfl
              intro m hm
              have hms : m ∈ s := by
                have hm' : m ∈ s ∧ reduceTriple (p := p) m ≠ 0 := by
                  simpa [nonzeroResiduePopulation] using hm
                exact hm'.1
              have hm0 : reduceTriple (p := p) m ≠ 0 := by
                have hm' : m ∈ s ∧ reduceTriple (p := p) m ≠ 0 := by
                  simpa [nonzeroResiduePopulation] using hm
                exact hm'.2
              rw [thin_integralOrthogonalDirections_card hp2, if_neg hm0,
                hnorm m hms]
      _ = (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) *
          ((nonzeroResiduePopulation (p := p) s).card : ℤ) := by
            simp
            ring

/-- The corresponding thick incidence split. -/
theorem thick_incidence_middle_quotient_split (hp2 : p ≠ 2)
    (s : Finset IntTriple) (n : ℤ)
    (hnorm : ∀ m ∈ s, intTunnellQuadratic 32 m = n) :
    ((integralOrthogonalIncidencePopulation (p := p) 32 s).card : ℤ) =
      ((p : ℤ) + 1) * ((zeroResiduePopulation (p := p) s).card : ℤ) +
      (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) *
        ((nonzeroResiduePopulation (p := p) s).card : ℤ) := by
  have hcard :
      ((integralOrthogonalIncidencePopulation (p := p) 32 s).card : ℤ) =
        ∑ m ∈ s, ((integralOrthogonalDirections (p := p) 32 m).card : ℤ) := by
    exact_mod_cast integralOrthogonalIncidencePopulation_card (p := p) 32 s
  rw [hcard, split_incidence_sum]
  congr 1
  · calc
      (∑ m ∈ zeroResiduePopulation (p := p) s,
          ((integralOrthogonalDirections (p := p) 32 m).card : ℤ)) =
          ∑ _m ∈ zeroResiduePopulation (p := p) s, ((p : ℤ) + 1) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hm0 : reduceTriple (p := p) m = 0 := by
              have hm' : m ∈ s ∧ reduceTriple (p := p) m = 0 := by
                simpa [zeroResiduePopulation] using hm
              exact hm'.2
            rw [thick_integralOrthogonalDirections_card hp2, if_pos hm0]
      _ = ((p : ℤ) + 1) * ((zeroResiduePopulation (p := p) s).card : ℤ) := by
            simp
            ring

  · calc
      (∑ m ∈ nonzeroResiduePopulation (p := p) s,
          ((integralOrthogonalDirections (p := p) 32 m).card : ℤ)) =
          ∑ _m ∈ nonzeroResiduePopulation (p := p) s,
            (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) := by
              apply Finset.sum_congr rfl
              intro m hm
              have hms : m ∈ s := by
                have hm' : m ∈ s ∧ reduceTriple (p := p) m ≠ 0 := by
                  simpa [nonzeroResiduePopulation] using hm
                exact hm'.1
              have hm0 : reduceTriple (p := p) m ≠ 0 := by
                have hm' : m ∈ s ∧ reduceTriple (p := p) m ≠ 0 := by
                  simpa [nonzeroResiduePopulation] using hm
                exact hm'.2
              rw [thick_integralOrthogonalDirections_card hp2, if_neg hm0,
                hnorm m hms]
      _ = (quadraticChar (ZMod p) (-(n : ZMod p)) + 1) *
          ((nonzeroResiduePopulation (p := p) s).card : ℤ) := by
            simp
            ring

/-! ## Exact reconstruction of the zero-residue predecessor -/

/-- Coordinatewise prime scaling. -/
def scaleTripleByPrime (m : IntTriple) : IntTriple :=
  ((p : ℤ) * m.1, (p : ℤ) * m.2.1, (p : ℤ) * m.2.2)

/-- Coordinatewise exact quotient chart.  Its inverse law is only claimed on the
zero-residue fiber where divisibility has been proved. -/
def divideTripleByPrime (m : IntTriple) : IntTriple :=
  (m.1 / (p : ℤ), m.2.1 / (p : ℤ), m.2.2 / (p : ℤ))

/-- Vanishing of the returned coordinate triple is exactly coordinatewise prime
divisibility; no scalar-only divisibility surrogate is used. -/
theorem reduceTriple_eq_zero_iff (m : IntTriple) :
    reduceTriple (p := p) m = 0 ↔
      (p : ℤ) ∣ m.1 ∧ (p : ℤ) ∣ m.2.1 ∧ (p : ℤ) ∣ m.2.2 := by
  constructor
  · intro hm
    have hx : (m.1 : ZMod p) = 0 := congrArg Prod.fst hm
    have hy : (m.2.1 : ZMod p) = 0 := congrArg (fun q => q.2.1) hm
    have hz : (m.2.2 : ZMod p) = 0 := congrArg (fun q => q.2.2) hm
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd m.1 p).mp hx,
      (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.1 p).mp hy,
      (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.2 p).mp hz⟩
  · rintro ⟨hx, hy, hz⟩
    apply Prod.ext
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd m.1 p).mpr hx
    · apply Prod.ext
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.1 p).mpr hy
      · exact (ZMod.intCast_zmod_eq_zero_iff_dvd m.2.2 p).mpr hz

/-- Scaling enters the zero-residue fiber. -/
theorem reduce_scaleTripleByPrime (m : IntTriple) :
    reduceTriple (p := p) (scaleTripleByPrime (p := p) m) = 0 := by
  simp [reduceTriple, scaleTripleByPrime]

/-- Exact reconstruction after quotienting a zero-residue occurrence. -/
theorem scale_divideTripleByPrime {m : IntTriple}
    (hm : reduceTriple (p := p) m = 0) :
    scaleTripleByPrime (p := p) (divideTripleByPrime (p := p) m) = m := by
  obtain ⟨hx, hy, hz⟩ := (reduceTriple_eq_zero_iff (p := p) m).mp hm
  apply Prod.ext
  · simp only [scaleTripleByPrime, divideTripleByPrime]
    simpa [mul_comm] using Int.ediv_mul_cancel hx
  · apply Prod.ext
    · simp only [scaleTripleByPrime, divideTripleByPrime]
      simpa [mul_comm] using Int.ediv_mul_cancel hy
    · simp only [scaleTripleByPrime, divideTripleByPrime]
      simpa [mul_comm] using Int.ediv_mul_cancel hz

/-- Quotienting a scaled occurrence returns the source triple. -/
theorem divide_scaleTripleByPrime (m : IntTriple) :
    divideTripleByPrime (p := p) (scaleTripleByPrime (p := p) m) = m := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply Prod.ext
  · exact Int.mul_ediv_cancel_left m.1 hp
  · apply Prod.ext
    · exact Int.mul_ediv_cancel_left m.2.1 hp
    · exact Int.mul_ediv_cancel_left m.2.2 hp

/-- The predecessor population retained by exact coordinatewise division. -/
def scalePredecessorPopulation (s : Finset IntTriple) : Finset IntTriple :=
  (zeroResiduePopulation (p := p) s).image (divideTripleByPrime (p := p))

/-- Projecting to the predecessor loses no occurrences inside the declared
zero-residue fiber. -/
theorem scalePredecessorPopulation_card (s : Finset IntTriple) :
    (scalePredecessorPopulation (p := p) s).card =
      (zeroResiduePopulation (p := p) s).card := by
  unfold scalePredecessorPopulation
  rw [Finset.card_image_iff.mpr]
  intro a ha b hb hab
  have ha0 : reduceTriple (p := p) a = 0 := by
    have ha' : a ∈ s ∧ reduceTriple (p := p) a = 0 := by
      simpa [zeroResiduePopulation] using ha
    exact ha'.2
  have hb0 : reduceTriple (p := p) b = 0 := by
    have hb' : b ∈ s ∧ reduceTriple (p := p) b = 0 := by
      simpa [zeroResiduePopulation] using hb
    exact hb'.2
  calc
    a = scaleTripleByPrime (p := p) (divideTripleByPrime (p := p) a) :=
      (scale_divideTripleByPrime (p := p) ha0).symm
    _ = scaleTripleByPrime (p := p) (divideTripleByPrime (p := p) b) := by rw [hab]
    _ = b := scale_divideTripleByPrime (p := p) hb0

/-- Quadratic norm has the exact scale degree two. -/
theorem intTunnellQuadratic_scaleTripleByPrime (C : ℤ) (m : IntTriple) :
    intTunnellQuadratic C (scaleTripleByPrime (p := p) m) =
      (p : ℤ) ^ 2 * intTunnellQuadratic C m := by
  simp [intTunnellQuadratic, scaleTripleByPrime]
  ring

/-- Every reconstructed predecessor of a norm-`n` zero-residue population has
exactly the quotient norm witnessed by multiplication with `p²`. -/
theorem scalePredecessorPopulation_norm
    (C n : ℤ) (s : Finset IntTriple)
    (hnorm : ∀ m ∈ s, intTunnellQuadratic C m = n)
    {u : IntTriple} (hu : u ∈ scalePredecessorPopulation (p := p) s) :
    (p : ℤ) ^ 2 * intTunnellQuadratic C u = n := by
  rcases Finset.mem_image.mp hu with ⟨m, hm, rfl⟩
  have hm' : m ∈ s ∧ reduceTriple (p := p) m = 0 := by
    simpa [zeroResiduePopulation] using hm
  rw [← intTunnellQuadratic_scaleTripleByPrime (p := p),
    scale_divideTripleByPrime (p := p) hm'.2, hnorm m hm'.1]

/-! ## Identification with the actual Tunnell quotient coefficient -/

/-- The tight box in the thin coefficient is a proved aperture, so membership is
equivalent to the quadratic equation alone. -/
theorem mem_canonicalThinPopulation_iff_intTunnellQuadratic
    (n : ℕ) (m : IntTriple) :
    m ∈ canonicalThinPopulation n ↔ intTunnellQuadratic 8 m = (n : ℤ) := by
  simp only [canonicalThinPopulation, SolFr, Finset.mem_filter, Finset.mem_product,
    theReducibleBoxIsTheInterval, Finset.mem_Icc]
  constructor
  · rintro ⟨_, hq⟩
    simpa [intTunnellQuadratic] using hq
  · intro hq
    have hq' : 2 * m.1 ^ 2 + m.2.1 ^ 2 + 8 * m.2.2 ^ 2 = (n : ℤ) := by
      simpa [intTunnellQuadratic] using hq
    obtain ⟨hx, hy, hz⟩ := theSolutionsAreTightlyBounded hq'
    exact ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
      ⟨by omega, by omega⟩⟩, hq'⟩

private theorem thickSolutionsTightlyBounded {n : ℕ} {m : IntTriple}
    (h : intTunnellQuadratic 32 m = (n : ℤ)) :
    m.1.natAbs ≤ Nat.sqrt n ∧ m.2.1.natAbs ≤ Nat.sqrt n ∧
      m.2.2.natAbs ≤ Nat.sqrt n := by
  have hx2 : m.1 ^ 2 ≤ (n : ℤ) := by
    simp [intTunnellQuadratic] at h
    nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
  have hy2 : m.2.1 ^ 2 ≤ (n : ℤ) := by
    simp [intTunnellQuadratic] at h
    nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
  have hz2 : m.2.2 ^ 2 ≤ (n : ℤ) := by
    simp [intTunnellQuadratic] at h
    nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
  refine ⟨Nat.le_sqrt.mpr ?_, Nat.le_sqrt.mpr ?_, Nat.le_sqrt.mpr ?_⟩
  · have : ((m.1.natAbs * m.1.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by
      push_cast [Int.natCast_natAbs]
      nlinarith [sq_abs m.1, abs_nonneg m.1]
    exact_mod_cast this
  · have : ((m.2.1.natAbs * m.2.1.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by
      push_cast [Int.natCast_natAbs]
      nlinarith [sq_abs m.2.1, abs_nonneg m.2.1]
    exact_mod_cast this
  · have : ((m.2.2.natAbs * m.2.2.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by
      push_cast [Int.natCast_natAbs]
      nlinarith [sq_abs m.2.2, abs_nonneg m.2.2]
    exact_mod_cast this

/-- The same aperture theorem for the thick coefficient. -/
theorem mem_canonicalThickPopulation_iff_intTunnellQuadratic
    (n : ℕ) (m : IntTriple) :
    m ∈ canonicalThickPopulation n ↔ intTunnellQuadratic 32 m = (n : ℤ) := by
  rw [mem_canonicalThickPopulation_iff]
  constructor
  · rintro ⟨_, hq⟩
    simpa [intTunnellQuadratic] using hq
  · intro hq
    obtain ⟨hx, hy, hz⟩ := thickSolutionsTightlyBounded hq
    have hq' : 2 * m.1 ^ 2 + m.2.1 ^ 2 + 32 * m.2.2 ^ 2 = (n : ℤ) := by
      simpa [intTunnellQuadratic] using hq
    have hb : m.1 ∈ boxZ (Nat.sqrt n) ∧ m.2.1 ∈ boxZ (Nat.sqrt n) ∧
        m.2.2 ∈ boxZ (Nat.sqrt n) := by
      simp only [theReducibleBoxIsTheInterval, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
        ⟨by omega, by omega⟩⟩
    exact ⟨hb, hq'⟩

private theorem scale_mem_canonicalThinPopulation_iff (n : ℕ) (m : IntTriple) :
    scaleTripleByPrime (p := p) m ∈ canonicalThinPopulation (p ^ 2 * n) ↔
      m ∈ canonicalThinPopulation n := by
  rw [mem_canonicalThinPopulation_iff_intTunnellQuadratic,
    mem_canonicalThinPopulation_iff_intTunnellQuadratic,
    intTunnellQuadratic_scaleTripleByPrime]
  norm_cast
  have hp : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  constructor
  · intro h
    exact mul_left_cancel₀ hp h
  · intro h
    rw [h]
    norm_cast

private theorem scale_mem_canonicalThickPopulation_iff (n : ℕ) (m : IntTriple) :
    scaleTripleByPrime (p := p) m ∈ canonicalThickPopulation (p ^ 2 * n) ↔
      m ∈ canonicalThickPopulation n := by
  rw [mem_canonicalThickPopulation_iff_intTunnellQuadratic,
    mem_canonicalThickPopulation_iff_intTunnellQuadratic,
    intTunnellQuadratic_scaleTripleByPrime]
  norm_cast
  have hp : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (by
    exact_mod_cast (Fact.out : p.Prime).ne_zero)
  constructor
  · intro h
    exact mul_left_cancel₀ hp h
  · intro h
    rw [h]
    norm_cast

/-- **THE ZERO-RESIDUE THIN FIBER IS EXACTLY THE QUOTIENT COEFFICIENT.** -/
theorem scalePredecessor_canonicalThinPopulation (n : ℕ) :
    scalePredecessorPopulation (p := p) (canonicalThinPopulation (p ^ 2 * n)) =
      canonicalThinPopulation n := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨v, hv, hvm⟩
    have hv' : v ∈ canonicalThinPopulation (p ^ 2 * n) ∧
        reduceTriple (p := p) v = 0 := by
      simpa [zeroResiduePopulation] using hv
    have hscale : scaleTripleByPrime (p := p) m = v := by
      rw [← hvm, scale_divideTripleByPrime (p := p) hv'.2]
    rw [← scale_mem_canonicalThinPopulation_iff (p := p) n m, hscale]
    exact hv'.1
  · intro hm
    refine Finset.mem_image.mpr ⟨scaleTripleByPrime (p := p) m, ?_, ?_⟩
    · simp only [zeroResiduePopulation, Finset.mem_filter]
      exact ⟨(scale_mem_canonicalThinPopulation_iff (p := p) n m).mpr hm,
        reduce_scaleTripleByPrime (p := p) m⟩
    · exact divide_scaleTripleByPrime (p := p) m

/-- **THE ZERO-RESIDUE THICK FIBER IS EXACTLY THE QUOTIENT COEFFICIENT.** -/
theorem scalePredecessor_canonicalThickPopulation (n : ℕ) :
    scalePredecessorPopulation (p := p) (canonicalThickPopulation (p ^ 2 * n)) =
      canonicalThickPopulation n := by
  ext m
  constructor
  · intro hm
    rcases Finset.mem_image.mp hm with ⟨v, hv, hvm⟩
    have hv' : v ∈ canonicalThickPopulation (p ^ 2 * n) ∧
        reduceTriple (p := p) v = 0 := by
      simpa [zeroResiduePopulation] using hv
    have hscale : scaleTripleByPrime (p := p) m = v := by
      rw [← hvm, scale_divideTripleByPrime (p := p) hv'.2]
    rw [← scale_mem_canonicalThickPopulation_iff (p := p) n m, hscale]
    exact hv'.1
  · intro hm
    refine Finset.mem_image.mpr ⟨scaleTripleByPrime (p := p) m, ?_, ?_⟩
    · simp only [zeroResiduePopulation, Finset.mem_filter]
      exact ⟨(scale_mem_canonicalThickPopulation_iff (p := p) n m).mpr hm,
        reduce_scaleTripleByPrime (p := p) m⟩
    · exact divide_scaleTripleByPrime (p := p) m

theorem zeroResidue_canonicalThinPopulation_card (n : ℕ) :
    (zeroResiduePopulation (p := p) (canonicalThinPopulation (p ^ 2 * n))).card =
      (canonicalThinPopulation n).card := by
  rw [← scalePredecessorPopulation_card,
    scalePredecessor_canonicalThinPopulation]

theorem zeroResidue_canonicalThickPopulation_card (n : ℕ) :
    (zeroResiduePopulation (p := p) (canonicalThickPopulation (p ^ 2 * n))).card =
      (canonicalThickPopulation n).card := by
  rw [← scalePredecessorPopulation_card,
    scalePredecessor_canonicalThickPopulation]

/-- The thin zero-residue population is present exactly on the `p²`-divisible
index branch and is then the actual quotient coefficient. -/
theorem zeroResidue_canonicalThinPopulation_card_eq (n : ℕ) :
    (zeroResiduePopulation (p := p) (canonicalThinPopulation n)).card =
      if p ^ 2 ∣ n then (canonicalThinPopulation (n / p ^ 2)).card else 0 := by
  by_cases hdiv : p ^ 2 ∣ n
  · rw [if_pos hdiv]
    have hreturn : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
    have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    rw [← hreturn, zeroResidue_canonicalThinPopulation_card,
      Nat.mul_div_cancel_left (n / p ^ 2) hp2pos]
  · rw [if_neg hdiv]
    suffices zeroResiduePopulation (p := p) (canonicalThinPopulation n) = ∅ by
      rw [this, Finset.card_empty]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    have hm' : m ∈ canonicalThinPopulation n ∧ reduceTriple (p := p) m = 0 := by
      simpa [zeroResiduePopulation] using hm
    let u := divideTripleByPrime (p := p) m
    have hscale : scaleTripleByPrime (p := p) u = m :=
      scale_divideTripleByPrime (p := p) hm'.2
    have hq : intTunnellQuadratic 8 m = (n : ℤ) :=
      (mem_canonicalThinPopulation_iff_intTunnellQuadratic n m).mp hm'.1
    have hdivZ : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
      refine ⟨intTunnellQuadratic 8 u, ?_⟩
      calc
        (n : ℤ) = intTunnellQuadratic 8 m := hq.symm
        _ = intTunnellQuadratic 8 (scaleTripleByPrime (p := p) u) := by rw [hscale]
        _ = (p : ℤ) ^ 2 * intTunnellQuadratic 8 u :=
          intTunnellQuadratic_scaleTripleByPrime (p := p) 8 u
        _ = ((p ^ 2 : ℕ) : ℤ) * intTunnellQuadratic 8 u := by norm_cast
    apply hdiv
    exact_mod_cast hdivZ

/-- Thick analogue of the exact quotient branch. -/
theorem zeroResidue_canonicalThickPopulation_card_eq (n : ℕ) :
    (zeroResiduePopulation (p := p) (canonicalThickPopulation n)).card =
      if p ^ 2 ∣ n then (canonicalThickPopulation (n / p ^ 2)).card else 0 := by
  by_cases hdiv : p ^ 2 ∣ n
  · rw [if_pos hdiv]
    have hreturn : p ^ 2 * (n / p ^ 2) = n := Nat.mul_div_cancel' hdiv
    have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
    rw [← hreturn, zeroResidue_canonicalThickPopulation_card,
      Nat.mul_div_cancel_left (n / p ^ 2) hp2pos]
  · rw [if_neg hdiv]
    suffices zeroResiduePopulation (p := p) (canonicalThickPopulation n) = ∅ by
      rw [this, Finset.card_empty]
    rw [Finset.eq_empty_iff_forall_notMem]
    intro m hm
    have hm' : m ∈ canonicalThickPopulation n ∧ reduceTriple (p := p) m = 0 := by
      simpa [zeroResiduePopulation] using hm
    let u := divideTripleByPrime (p := p) m
    have hscale : scaleTripleByPrime (p := p) u = m :=
      scale_divideTripleByPrime (p := p) hm'.2
    have hq : intTunnellQuadratic 32 m = (n : ℤ) :=
      (mem_canonicalThickPopulation_iff_intTunnellQuadratic n m).mp hm'.1
    have hdivZ : ((p ^ 2 : ℕ) : ℤ) ∣ (n : ℤ) := by
      refine ⟨intTunnellQuadratic 32 u, ?_⟩
      calc
        (n : ℤ) = intTunnellQuadratic 32 m := hq.symm
        _ = intTunnellQuadratic 32 (scaleTripleByPrime (p := p) u) := by rw [hscale]
        _ = (p : ℤ) ^ 2 * intTunnellQuadratic 32 u :=
          intTunnellQuadratic_scaleTripleByPrime (p := p) 32 u
        _ = ((p ^ 2 : ℕ) : ℤ) * intTunnellQuadratic 32 u := by norm_cast
    apply hdiv
    exact_mod_cast hdivZ

private theorem zero_add_nonzero_card (s : Finset IntTriple) :
    (zeroResiduePopulation (p := p) s).card +
      (nonzeroResiduePopulation (p := p) s).card = s.card := by
  simpa [zeroResiduePopulation, nonzeroResiduePopulation] using
    Finset.card_filter_add_card_filter_not
      (s := s) (fun m : IntTriple => reduceTriple (p := p) m = 0)

/-- **THE THIN INCIDENCE DEFECT IS THE COMPLETE MIDDLE-PLUS-QUOTIENT TERM.** -/
theorem thin_incidence_defect (hp2 : p ≠ 2) (n : ℕ) :
    ((integralOrthogonalIncidencePopulation (p := p) 8
        (canonicalThinPopulation n)).card : ℤ) -
        ((canonicalThinPopulation n).card : ℤ) =
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((canonicalThinPopulation n).card : ℤ) +
        (p : ℤ) *
          (if p ^ 2 ∣ n then ((canonicalThinPopulation (n / p ^ 2)).card : ℤ)
            else 0) := by
  have hnorm : ∀ m ∈ canonicalThinPopulation n,
      intTunnellQuadratic 8 m = (n : ℤ) := by
    intro m hm
    exact (mem_canonicalThinPopulation_iff_intTunnellQuadratic n m).mp hm
  have hinc := thin_incidence_middle_quotient_split (p := p) hp2
    (canonicalThinPopulation n) (n : ℤ) hnorm
  have hpart := zero_add_nonzero_card (p := p) (canonicalThinPopulation n)
  have hpartCast :
      ((zeroResiduePopulation (p := p) (canonicalThinPopulation n)).card : ℤ) +
        ((nonzeroResiduePopulation (p := p) (canonicalThinPopulation n)).card : ℤ) =
          ((canonicalThinPopulation n).card : ℤ) := by
    exact_mod_cast hpart
  have hpartZ :
      ((nonzeroResiduePopulation (p := p) (canonicalThinPopulation n)).card : ℤ) =
        ((canonicalThinPopulation n).card : ℤ) -
          ((zeroResiduePopulation (p := p) (canonicalThinPopulation n)).card : ℤ) := by
    omega
  rw [hinc, hpartZ, zeroResidue_canonicalThinPopulation_card_eq]
  by_cases hdiv : p ^ 2 ∣ n
  · have hn0 : (n : ZMod p) = 0 := by
      obtain ⟨k, hk⟩ := hdiv
      rw [hk]
      simp
    simp [hdiv, hn0, quadraticChar_zero]
    ring
  · simp [hdiv]
    ring

/-- **THE THICK INCIDENCE DEFECT IS THE SAME COMPLETE HECKE TERM.** -/
theorem thick_incidence_defect (hp2 : p ≠ 2) (n : ℕ) :
    ((integralOrthogonalIncidencePopulation (p := p) 32
        (canonicalThickPopulation n)).card : ℤ) -
        ((canonicalThickPopulation n).card : ℤ) =
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((canonicalThickPopulation n).card : ℤ) +
        (p : ℤ) *
          (if p ^ 2 ∣ n then ((canonicalThickPopulation (n / p ^ 2)).card : ℤ)
            else 0) := by
  have hnorm : ∀ m ∈ canonicalThickPopulation n,
      intTunnellQuadratic 32 m = (n : ℤ) := by
    intro m hm
    exact (mem_canonicalThickPopulation_iff_intTunnellQuadratic n m).mp hm
  have hinc := thick_incidence_middle_quotient_split (p := p) hp2
    (canonicalThickPopulation n) (n : ℤ) hnorm
  have hpart := zero_add_nonzero_card (p := p) (canonicalThickPopulation n)
  have hpartCast :
      ((zeroResiduePopulation (p := p) (canonicalThickPopulation n)).card : ℤ) +
        ((nonzeroResiduePopulation (p := p) (canonicalThickPopulation n)).card : ℤ) =
          ((canonicalThickPopulation n).card : ℤ) := by
    exact_mod_cast hpart
  have hpartZ :
      ((nonzeroResiduePopulation (p := p) (canonicalThickPopulation n)).card : ℤ) =
        ((canonicalThickPopulation n).card : ℤ) -
          ((zeroResiduePopulation (p := p) (canonicalThickPopulation n)).card : ℤ) := by
    omega
  rw [hinc, hpartZ, zeroResidue_canonicalThickPopulation_card_eq]
  by_cases hdiv : p ^ 2 ∣ n
  · have hn0 : (n : ZMod p) = 0 := by
      obtain ⟨k, hk⟩ := hdiv
      rw [hk]
      simp
    simp [hdiv, hn0, quadraticChar_zero]
    ring
  · simp [hdiv]
    ring

#print axioms quadraticChar_tunnellFactor_eight
#print axioms thin_integralOrthogonalDirections_card
#print axioms thick_integralOrthogonalDirections_card
#print axioms integralOrthogonalIncidencePopulation_card
#print axioms incidenceVector_mem_integralNeighbor
#print axioms thin_incidence_middle_quotient_split
#print axioms thick_incidence_middle_quotient_split
#print axioms reduceTriple_eq_zero_iff
#print axioms scalePredecessorPopulation_card
#print axioms scalePredecessorPopulation_norm
#print axioms scalePredecessor_canonicalThinPopulation
#print axioms scalePredecessor_canonicalThickPopulation
#print axioms zeroResidue_canonicalThinPopulation_card_eq
#print axioms zeroResidue_canonicalThickPopulation_card_eq
#print axioms thin_incidence_defect
#print axioms thick_incidence_defect

end Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence

import ElementaryHolonics.Millennium.FamilyTunnellBrandtTestVector

/-!
# Odd-prime neighbor directions for the second Tunnell--Brandt lattice

The second Brandt norm

`Q₂(x,y,z) = 2x² + 4y² + 4yz + 9z²`

is carried to the thin diagonal norm `2x² + Y² + 8z²` by the integral
chart `Y = 2y+z`.  This chart has determinant two.  It is therefore not an
integral rebase at the two-adic aperture, but it is an exact invertible chart
over every odd residue field.  The distinction is retained here rather than
erased by calling the two forms equal.

The file constructs the local equivalence, transports the complete `p+1`
projective conic, and then lifts every transported direction to an actual
integral vector whose `Q₂`-norm is divisible by `p²`.  Thus the cross-term
lattice has the same complete odd-prime neighbor aperture as the diagonal
lattice without assuming a Brandt matrix or a modular-form eigenlaw.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector

variable {p : ℕ} [Fact p.Prime]

abbrev ResidueTriple := CoordinateTriple (ZMod p)

/-- The second Brandt norm in the odd-prime residue chart. -/
def reducedBrandtSecondQuadratic (v : ResidueTriple (p := p)) : ZMod p :=
  2 * v.1 ^ 2 + 4 * v.2.1 ^ 2 + 4 * v.2.1 * v.2.2 + 9 * v.2.2 ^ 2

/-- The determinant-two chart from the second Brandt lattice to the thin
diagonal lattice. -/
def brandtSecondToThinMod (v : ResidueTriple (p := p)) : ResidueTriple (p := p) :=
  (v.1, 2 * v.2.1 + v.2.2, v.2.2)

/-- The inverse chart over an odd residue field. -/
def thinToBrandtSecondMod (v : ResidueTriple (p := p)) : ResidueTriple (p := p) :=
  (v.1, (v.2.1 - v.2.2) / 2, v.2.2)

private theorem two_ne_zero (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

theorem brandtSecondToThinMod_thinToBrandtSecondMod (hp2 : p ≠ 2)
    (v : ResidueTriple (p := p)) :
    brandtSecondToThinMod (thinToBrandtSecondMod v) = v := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [brandtSecondToThinMod, thinToBrandtSecondMod]
      field_simp [two_ne_zero (p := p) hp2]
      ring
    · rfl

theorem thinToBrandtSecondMod_brandtSecondToThinMod (hp2 : p ≠ 2)
    (v : ResidueTriple (p := p)) :
    thinToBrandtSecondMod (brandtSecondToThinMod v) = v := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [brandtSecondToThinMod, thinToBrandtSecondMod]
      field_simp [two_ne_zero (p := p) hp2]
    · rfl

/-- The local determinant-two chart as an actual equivalence, not an
unaddressed coordinate substitution. -/
def brandtSecondThinEquiv (hp2 : p ≠ 2) :
    ResidueTriple (p := p) ≃ ResidueTriple (p := p) where
  toFun := brandtSecondToThinMod
  invFun := thinToBrandtSecondMod
  left_inv := thinToBrandtSecondMod_brandtSecondToThinMod hp2
  right_inv := brandtSecondToThinMod_thinToBrandtSecondMod hp2

/-- The quadratic receiver commutes with the local chart. -/
theorem reducedTunnellQuadratic_brandtSecondToThinMod
    (v : ResidueTriple (p := p)) :
    reducedTunnellQuadratic 8 (brandtSecondToThinMod v) =
      reducedBrandtSecondQuadratic v := by
  simp [reducedTunnellQuadratic, reducedBrandtSecondQuadratic,
    brandtSecondToThinMod]
  ring

theorem reducedBrandtSecondQuadratic_thinToBrandtSecondMod
    (hp2 : p ≠ 2) (v : ResidueTriple (p := p)) :
    reducedBrandtSecondQuadratic (thinToBrandtSecondMod v) =
      reducedTunnellQuadratic 8 v := by
  rw [← reducedTunnellQuadratic_brandtSecondToThinMod]
  rw [brandtSecondToThinMod_thinToBrandtSecondMod (p := p) hp2]

/-! ## The two Brandt classes occupy one odd-prime local genus -/

def reducedBrandtFirstQuadratic (v : ResidueTriple (p := p)) : ZMod p :=
  2 * v.1 ^ 2 + v.2.1 ^ 2 + 32 * v.2.2 ^ 2

def brandtFirstToThinMod (v : ResidueTriple (p := p)) : ResidueTriple (p := p) :=
  (v.1, v.2.1, 2 * v.2.2)

def thinToBrandtFirstMod (v : ResidueTriple (p := p)) : ResidueTriple (p := p) :=
  (v.1, v.2.1, v.2.2 / 2)

theorem brandtFirstToThinMod_thinToBrandtFirstMod (hp2 : p ≠ 2)
    (v : ResidueTriple (p := p)) :
    brandtFirstToThinMod (thinToBrandtFirstMod v) = v := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp [brandtFirstToThinMod, thinToBrandtFirstMod]
      field_simp [two_ne_zero (p := p) hp2]

theorem thinToBrandtFirstMod_brandtFirstToThinMod (hp2 : p ≠ 2)
    (v : ResidueTriple (p := p)) :
    thinToBrandtFirstMod (brandtFirstToThinMod v) = v := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simp [brandtFirstToThinMod, thinToBrandtFirstMod]
      field_simp [two_ne_zero (p := p) hp2]

def brandtFirstThinEquiv (hp2 : p ≠ 2) :
    ResidueTriple (p := p) ≃ ResidueTriple (p := p) where
  toFun := brandtFirstToThinMod
  invFun := thinToBrandtFirstMod
  left_inv := thinToBrandtFirstMod_brandtFirstToThinMod hp2
  right_inv := brandtFirstToThinMod_thinToBrandtFirstMod hp2

theorem reducedTunnellQuadratic_brandtFirstToThinMod
    (v : ResidueTriple (p := p)) :
    reducedTunnellQuadratic 8 (brandtFirstToThinMod v) =
      reducedBrandtFirstQuadratic v := by
  simp [reducedTunnellQuadratic, reducedBrandtFirstQuadratic,
    brandtFirstToThinMod]
  ring

/-- The explicit odd-prime isometry from the first Brandt class to the second:
first -> thin -> second. -/
def brandtFirstSecondEquiv (hp2 : p ≠ 2) :
    ResidueTriple (p := p) ≃ ResidueTriple (p := p) :=
  (brandtFirstThinEquiv (p := p) hp2).trans
    (brandtSecondThinEquiv (p := p) hp2).symm

/-- **THE TWO INTEGRAL CLASSES HAVE THE SAME QUADRATIC RECEIVER AT EVERY
ODD PRIME.**  Their two-adic inequivalence is retained outside this theorem. -/
theorem reducedBrandtSecondQuadratic_brandtFirstSecondEquiv
    (hp2 : p ≠ 2) (v : ResidueTriple (p := p)) :
    reducedBrandtSecondQuadratic (brandtFirstSecondEquiv hp2 v) =
      reducedBrandtFirstQuadratic v := by
  change reducedBrandtSecondQuadratic
      (thinToBrandtSecondMod (brandtFirstToThinMod v)) = _
  rw [reducedBrandtSecondQuadratic_thinToBrandtSecondMod (p := p) hp2]
  exact reducedTunnellQuadratic_brandtFirstToThinMod v

/-! ## The complete projective direction carrier -/

/-- The second-lattice projective conic is indexed by the already constructed
thin conic, but its returned vector is transported through the inverse chart. -/
abbrev BrandtSecondProjectiveDirection :=
  ProjectiveConicDirection (p := p) (8 : ZMod p)

def brandtSecondDirectionVector (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) : ResidueTriple (p := p) :=
  thinToBrandtSecondMod (projectiveDirectionVector d.1)

theorem brandtSecondDirectionVector_isotropic (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    reducedBrandtSecondQuadratic (brandtSecondDirectionVector hp2 d) = 0 := by
  unfold brandtSecondDirectionVector
  rw [reducedBrandtSecondQuadratic_thinToBrandtSecondMod (p := p) hp2]
  exact projectiveDirectionVector_isotropic d

theorem brandtSecondDirectionVector_ne_zero (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    brandtSecondDirectionVector hp2 d ≠ (0, 0, 0) := by
  intro hzero
  have hforward := congrArg brandtSecondToThinMod hzero
  have hreturn := brandtSecondToThinMod_thinToBrandtSecondMod (p := p) hp2
    (projectiveDirectionVector d.1)
  have : projectiveDirectionVector d.1 = (0, 0, 0) := by
    calc
      projectiveDirectionVector d.1 =
          brandtSecondToThinMod
            (thinToBrandtSecondMod (projectiveDirectionVector d.1)) := hreturn.symm
      _ = brandtSecondToThinMod (0, 0, 0) := by
        simpa [brandtSecondDirectionVector] using hforward
      _ = (0, 0, 0) := by simp [brandtSecondToThinMod]
  exact projectiveDirectionVector_ne_zero d this

private theorem eight_ne_zero (hp2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  have h8 : (8 : ZMod p) = (2 : ZMod p) ^ 3 := by norm_num
  rw [h8]
  exact pow_ne_zero 3 (two_ne_zero (p := p) hp2)

/-- **THE SECOND BRANDT LATTICE HAS EXACTLY `p+1` ADDRESSED ODD-PRIME
NEIGHBOR DIRECTIONS.** -/
theorem brandtSecondProjectiveDirection_card (hp2 : p ≠ 2) :
    Fintype.card (BrandtSecondProjectiveDirection (p := p)) = p + 1 := by
  exact projectiveConicDirection_fintype_card (p := p) hp2
    (eight_ne_zero (p := p) hp2)

/-! ## Integral `p²`-isotropic lifts -/

/-- Least-nonnegative componentwise lift of the transported residue direction. -/
def baseBrandtSecondDirectionLift (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) : IntTriple :=
  let v := brandtSecondDirectionVector hp2 d
  ((v.1.val : ℤ), (v.2.1.val : ℤ), (v.2.2.val : ℤ))

theorem reduce_baseBrandtSecondDirectionLift (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    reduceTriple (p := p) (baseBrandtSecondDirectionLift hp2 d) =
      brandtSecondDirectionVector hp2 d := by
  simp [baseBrandtSecondDirectionLift, reduceTriple, ZMod.natCast_zmod_val]

theorem cast_brandtSecondQuadratic (v : IntTriple) :
    (brandtSecondQuadratic v : ZMod p) =
      reducedBrandtSecondQuadratic (reduceTriple (p := p) v) := by
  simp [brandtSecondQuadratic, reducedBrandtSecondQuadratic, reduceTriple]

theorem prime_dvd_baseBrandtSecondDirectionLift_norm (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    (p : ℤ) ∣ brandtSecondQuadratic (baseBrandtSecondDirectionLift hp2 d) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [cast_brandtSecondQuadratic, reduce_baseBrandtSecondDirectionLift]
  exact brandtSecondDirectionVector_isotropic hp2 d

def baseBrandtSecondNormQuotient (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) : ℤ :=
  brandtSecondQuadratic (baseBrandtSecondDirectionLift hp2 d) / (p : ℤ)

/-- The chart pivot is `x` on the affine branch and `y` on the infinity
branch.  Both have derivative `4` modulo `p`. -/
def adjustedBrandtSecondDirectionLift (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) : IntTriple :=
  let v := baseBrandtSecondDirectionLift hp2 d
  let t := pivotCorrection (p := p) 4 (baseBrandtSecondNormQuotient hp2 d)
  match d.1 with
  | .inl _ => (v.1 + (p : ℤ) * t, v.2.1, v.2.2)
  | .inr _ => (v.1, v.2.1 + (p : ℤ) * t, v.2.2)

theorem reduce_adjustedBrandtSecondDirectionLift (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    reduceTriple (p := p) (adjustedBrandtSecondDirectionLift hp2 d) =
      brandtSecondDirectionVector hp2 d := by
  rw [← reduce_baseBrandtSecondDirectionLift (p := p) hp2 d]
  rcases d with ⟨d, hd⟩
  cases d <;>
    simp [adjustedBrandtSecondDirectionLift, reduceTriple, ZMod.natCast_self]

private theorem infinity_pivot_derivative_mod (hp2 : p ≠ 2)
    (z : ZMod p) :
    let y : ℤ := (((1 - z) / 2).val : ℤ)
    let Z : ℤ := (z.val : ℤ)
    ((8 * y + 4 * Z : ℤ) : ZMod p) = 4 := by
  dsimp
  push_cast
  simp only [ZMod.natCast_zmod_val]
  field_simp [two_ne_zero (p := p) hp2]
  ring

/-- **EVERY SECOND-CLASS DIRECTION HAS AN ACTUAL INTEGRAL `p²`-ISOTROPIC
LIFT.**  This is the cross-term analogue of the diagonal neighbor lift. -/
theorem prime_sq_dvd_adjustedBrandtSecondDirectionLift_norm (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
      (p : ℤ) ^ 2 ∣
      brandtSecondQuadratic (adjustedBrandtSecondDirectionLift hp2 d) := by
  letI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
  have hdiv := prime_dvd_baseBrandtSecondDirectionLift_norm (p := p) hp2 d
  have hquotient :
      brandtSecondQuadratic (baseBrandtSecondDirectionLift hp2 d) =
        (p : ℤ) * baseBrandtSecondNormQuotient hp2 d := by
    simpa [baseBrandtSecondNormQuotient, mul_comm] using
      (Int.ediv_mul_cancel hdiv).symm
  rcases d with ⟨d, hd⟩
  cases d with
  | inl q =>
      let D : BrandtSecondProjectiveDirection (p := p) := ⟨Sum.inl q, hd⟩
      have hquotientD :
          brandtSecondQuadratic (baseBrandtSecondDirectionLift hp2 D) =
            (p : ℤ) * baseBrandtSecondNormQuotient hp2 D := by
        simpa [D] using hquotient
      let t := pivotCorrection (p := p) 4 (baseBrandtSecondNormQuotient hp2 D)
      obtain ⟨s, hs⟩ := prime_dvd_add_four_pivotCorrection (p := p) hp2
        (baseBrandtSecondNormQuotient hp2 D)
      change baseBrandtSecondNormQuotient hp2 D + 4 * t = (p : ℤ) * s at hs
      refine ⟨2 * t ^ 2 + s, ?_⟩
      let v := baseBrandtSecondDirectionLift hp2 D
      change brandtSecondQuadratic
          (v.1 + (p : ℤ) * t, v.2.1, v.2.2) =
        (p : ℤ) ^ 2 * (2 * t ^ 2 + s)
      calc
        brandtSecondQuadratic
            (v.1 + (p : ℤ) * t, v.2.1, v.2.2) =
            brandtSecondQuadratic v + 4 * (p : ℤ) * t * v.1 +
              2 * (p : ℤ) ^ 2 * t ^ 2 := by
                unfold brandtSecondQuadratic
                ring
        _ = (p : ℤ) * baseBrandtSecondNormQuotient hp2 D +
              4 * (p : ℤ) * t + 2 * (p : ℤ) ^ 2 * t ^ 2 := by
                rw [hquotientD]
                have hvx : v.1 = 1 := by
                  simp [v, D, baseBrandtSecondDirectionLift,
                    brandtSecondDirectionVector, thinToBrandtSecondMod,
                    projectiveDirectionVector, ZMod.val_one]
                rw [hvx]
                ring
        _ = (p : ℤ) ^ 2 * (2 * t ^ 2 + s) := by
              calc
                (p : ℤ) * baseBrandtSecondNormQuotient hp2 D +
                      4 * (p : ℤ) * t + 2 * (p : ℤ) ^ 2 * t ^ 2 =
                    (p : ℤ) *
                        (baseBrandtSecondNormQuotient hp2 D + 4 * t) +
                      2 * (p : ℤ) ^ 2 * t ^ 2 := by ring
                _ = (p : ℤ) * ((p : ℤ) * s) +
                      2 * (p : ℤ) ^ 2 * t ^ 2 := by rw [hs]
                _ = (p : ℤ) ^ 2 * (2 * t ^ 2 + s) := by ring
  | inr z =>
      let D : BrandtSecondProjectiveDirection (p := p) := ⟨Sum.inr z, hd⟩
      have hquotientD :
          brandtSecondQuadratic (baseBrandtSecondDirectionLift hp2 D) =
            (p : ℤ) * baseBrandtSecondNormQuotient hp2 D := by
        simpa [D] using hquotient
      let t := pivotCorrection (p := p) 4 (baseBrandtSecondNormQuotient hp2 D)
      have hderivD :
          (p : ℤ) ∣
            (8 * (baseBrandtSecondDirectionLift hp2 D).2.1 +
              4 * (baseBrandtSecondDirectionLift hp2 D).2.2) - 4 := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        rw [Int.cast_sub]
        have hmod := infinity_pivot_derivative_mod (p := p) hp2 z
        simpa [D, baseBrandtSecondDirectionLift, brandtSecondDirectionVector,
          thinToBrandtSecondMod, projectiveDirectionVector] using sub_eq_zero.mpr hmod
      obtain ⟨r, hr⟩ := hderivD
      obtain ⟨s, hs⟩ := prime_dvd_add_four_pivotCorrection (p := p) hp2
        (baseBrandtSecondNormQuotient hp2 D)
      change baseBrandtSecondNormQuotient hp2 D + 4 * t = (p : ℤ) * s at hs
      let v := baseBrandtSecondDirectionLift hp2 D
      have hderiv : 8 * v.2.1 + 4 * v.2.2 = 4 + (p : ℤ) * r := by
        change 8 * v.2.1 + 4 * v.2.2 - 4 = (p : ℤ) * r at hr
        linarith
      refine ⟨s + t * r + 4 * t ^ 2, ?_⟩
      change brandtSecondQuadratic
          (v.1, v.2.1 + (p : ℤ) * t, v.2.2) =
        (p : ℤ) ^ 2 * (s + t * r + 4 * t ^ 2)
      calc
        brandtSecondQuadratic
            (v.1, v.2.1 + (p : ℤ) * t, v.2.2) =
            brandtSecondQuadratic v +
              (p : ℤ) * t * (8 * v.2.1 + 4 * v.2.2) +
              4 * (p : ℤ) ^ 2 * t ^ 2 := by
                unfold brandtSecondQuadratic
                ring
        _ = (p : ℤ) * baseBrandtSecondNormQuotient hp2 D +
              (p : ℤ) * t * (4 + (p : ℤ) * r) +
              4 * (p : ℤ) ^ 2 * t ^ 2 := by
                rw [hquotientD, hderiv]
        _ = (p : ℤ) ^ 2 * (s + t * r + 4 * t ^ 2) := by
              calc
                (p : ℤ) * baseBrandtSecondNormQuotient hp2 D +
                      (p : ℤ) * t * (4 + (p : ℤ) * r) +
                      4 * (p : ℤ) ^ 2 * t ^ 2 =
                    (p : ℤ) *
                        (baseBrandtSecondNormQuotient hp2 D + 4 * t) +
                      (p : ℤ) ^ 2 * t * r +
                      4 * (p : ℤ) ^ 2 * t ^ 2 := by ring
                _ = (p : ℤ) * ((p : ℤ) * s) +
                      (p : ℤ) ^ 2 * t * r +
                      4 * (p : ℤ) ^ 2 * t ^ 2 := by rw [hs]
                _ = (p : ℤ) ^ 2 * (s + t * r + 4 * t ^ 2) := by ring

/-! ## The actual second-class rational neighbor -/

/-- Full integral polar form of `Q₂`. -/
def brandtSecondPolar (v w : IntTriple) : ℤ :=
  4 * v.1 * w.1 + 8 * v.2.1 * w.2.1 +
    4 * v.2.1 * w.2.2 + 4 * v.2.2 * w.2.1 +
    18 * v.2.2 * w.2.2

theorem brandtSecondQuadratic_add (v w : IntTriple) :
    brandtSecondQuadratic (v + w) =
      brandtSecondQuadratic v + brandtSecondPolar v w +
        brandtSecondQuadratic w := by
  simp [brandtSecondQuadratic, brandtSecondPolar]
  ring

/-- The rational quadratic receiver on the common ambient coordinates. -/
def ratBrandtSecondQuadratic (v : RatTriple) : ℚ :=
  2 * v.1 ^ 2 + 4 * v.2.1 ^ 2 + 4 * v.2.1 * v.2.2 + 9 * v.2.2 ^ 2

def brandtSecondPolarKernel (v : IntTriple) : Set IntTriple :=
  {m | (p : ℤ) ∣ brandtSecondPolar m v}

/-- The cross-term `p`-neighbor generated by the polar kernel and the corrected
fractional isotropic direction. -/
def brandtSecondIntegralNeighbor (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) : AddSubgroup RatTriple where
  carrier :=
    {x | ∃ m : IntTriple,
        m ∈ brandtSecondPolarKernel (p := p)
          (adjustedBrandtSecondDirectionLift hp2 d) ∧
        ∃ a : ℤ,
          x = ratTripleAdd (intTripleToRat m)
            (ratTripleScale ((a : ℚ) / (p : ℚ))
              (intTripleToRat (adjustedBrandtSecondDirectionLift hp2 d)))}
  zero_mem' := by
    refine ⟨(0, 0, 0), ?_, 0, ?_⟩
    · simp [brandtSecondPolarKernel, brandtSecondPolar]
    · change (0, 0, 0) = _
      simp [ratTripleAdd, ratTripleScale, intTripleToRat]
  add_mem' := by
    rintro x y ⟨m, hm, a, rfl⟩ ⟨n, hn, b, rfl⟩
    refine ⟨m + n, ?_, a + b, ?_⟩
    · change (p : ℤ) ∣ brandtSecondPolar (m + n)
          (adjustedBrandtSecondDirectionLift hp2 d)
      have hadd :
          (p : ℤ) ∣ brandtSecondPolar m
              (adjustedBrandtSecondDirectionLift hp2 d) +
            brandtSecondPolar n
              (adjustedBrandtSecondDirectionLift hp2 d) := dvd_add hm hn
      convert hadd using 1 <;> simp [brandtSecondPolar] <;> ring
    · apply Prod.ext
      · simp [ratTripleAdd, ratTripleScale, intTripleToRat]
        ring
      · apply Prod.ext <;>
          simp [ratTripleAdd, ratTripleScale, intTripleToRat] <;> ring
  neg_mem' := by
    rintro x ⟨m, hm, a, rfl⟩
    refine ⟨-m, ?_, -a, ?_⟩
    · change (p : ℤ) ∣ brandtSecondPolar (-m)
          (adjustedBrandtSecondDirectionLift hp2 d)
      have hneg :
          (p : ℤ) ∣ -brandtSecondPolar m
            (adjustedBrandtSecondDirectionLift hp2 d) := dvd_neg.mpr hm
      convert hneg using 1 <;> simp [brandtSecondPolar] <;> ring
    · apply Prod.ext
      · simp [ratTripleAdd, ratTripleScale, intTripleToRat]
        ring
      · apply Prod.ext <;>
          simp [ratTripleAdd, ratTripleScale, intTripleToRat] <;> ring

theorem fractionalGenerator_mem_brandtSecondIntegralNeighbor (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p)) :
    ratTripleScale ((1 : ℚ) / (p : ℚ))
        (intTripleToRat (adjustedBrandtSecondDirectionLift hp2 d)) ∈
      brandtSecondIntegralNeighbor hp2 d := by
  refine ⟨(0, 0, 0), ?_, 1, ?_⟩
  · simp [brandtSecondPolarKernel, brandtSecondPolar]
  · simp [ratTripleAdd, intTripleToRat]

theorem ratBrandtSecondQuadratic_neighbor_coordinates
    (m v : IntTriple) (a : ℤ) :
    ratBrandtSecondQuadratic
        (ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ)) (intTripleToRat v))) =
      (brandtSecondQuadratic m : ℚ) +
        ((a : ℚ) / (p : ℚ)) * (brandtSecondPolar m v : ℚ) +
        ((a : ℚ) ^ 2 / (p : ℚ) ^ 2) *
          (brandtSecondQuadratic v : ℚ) := by
  simp [ratBrandtSecondQuadratic, ratTripleAdd, ratTripleScale, intTripleToRat,
    brandtSecondQuadratic, brandtSecondPolar]
  ring

/-- **EVERY QUADRATIC READING ON A SECOND-CLASS NEIGHBOR IS INTEGRAL.** -/
theorem brandtSecondIntegralNeighbor_norm_is_integer (hp2 : p ≠ 2)
    (d : BrandtSecondProjectiveDirection (p := p))
    {x : RatTriple} (hx : x ∈ brandtSecondIntegralNeighbor hp2 d) :
    ∃ N : ℤ, ratBrandtSecondQuadratic x = (N : ℚ) := by
  rcases hx with ⟨m, hm, a, rfl⟩
  change (p : ℤ) ∣
    brandtSecondPolar m (adjustedBrandtSecondDirectionLift hp2 d) at hm
  obtain ⟨b, hb⟩ := hm
  obtain ⟨q, hq⟩ :=
    prime_sq_dvd_adjustedBrandtSecondDirectionLift_norm (p := p) hp2 d
  refine ⟨brandtSecondQuadratic m + a * b + a ^ 2 * q, ?_⟩
  rw [ratBrandtSecondQuadratic_neighbor_coordinates]
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hbQ :
      (brandtSecondPolar m (adjustedBrandtSecondDirectionLift hp2 d) : ℚ) =
        (p : ℚ) * (b : ℚ) := by exact_mod_cast hb
  have hqQ :
      (brandtSecondQuadratic (adjustedBrandtSecondDirectionLift hp2 d) : ℚ) =
        (p : ℚ) ^ 2 * (q : ℚ) := by exact_mod_cast hq
  rw [hbQ, hqQ]
  push_cast
  field_simp

#print axioms brandtSecondThinEquiv
#print axioms brandtSecondDirectionVector_isotropic
#print axioms brandtSecondProjectiveDirection_card
#print axioms prime_sq_dvd_adjustedBrandtSecondDirectionLift_norm
#print axioms brandtSecondIntegralNeighbor_norm_is_integer

end Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors

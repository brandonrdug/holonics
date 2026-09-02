import ElementaryHolonics.Millennium.FamilyTunnellHeckeIncidence

/-!
# The odd-prime Tunnell neighbor double count

The `p`-neighbor coefficient has two disjoint geometric sources.

* A vector of norm `p²n` with nonzero residue has one unique projective direction,
  returned by the direction/scalar reconstruction equivalence.
* A vector of norm `n` contributes once for every isotropic direction orthogonal to
  its residue; the zero residue reopens all `p+1` directions and reconstructs the
  quotient coefficient at `n/p²`.

This file joins those sources into one finite numerator carrier and proves that its
cardinality is exactly the three-term half-integral Hecke coefficient.  The theorem
is a double count constructed from the source populations; it does not assume a
modular-form eigenlaw.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHeckeDoubleCount

open Finset
open Soma.Holonics.Millennium.FamilyThetaWaldspurgerBridge
open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellOrthogonalIncidence
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence

variable {p : ℕ} [Fact p.Prime]

private theorem eight_ne_zero (hp2 : p ≠ 2) : ((8 : ℤ) : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply Ring.two_ne_zero
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h8 : (8 : ZMod p) ≠ 0 := by
    rw [show (8 : ZMod p) = 2 ^ 3 by norm_num]
    exact pow_ne_zero 3 h2
  simpa using h8

private theorem thirtyTwo_ne_zero (hp2 : p ≠ 2) : ((32 : ℤ) : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    apply Ring.two_ne_zero
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h32 : (32 : ZMod p) ≠ 0 := by
    rw [show (32 : ZMod p) = 2 ^ 5 by norm_num]
    exact pow_ne_zero 5 h2
  simpa using h32

abbrev ThinUpperOccurrence (n : ℕ) :=
  {m // m ∈ nonzeroResiduePopulation (p := p)
    (canonicalThinPopulation (p ^ 2 * n))}

abbrev ThickUpperOccurrence (n : ℕ) :=
  {m // m ∈ nonzeroResiduePopulation (p := p)
    (canonicalThickPopulation (p ^ 2 * n))}

/-- A nonzero upper thin occurrence retains the complete isotropic residue vector. -/
def thinUpperIsotropicVector (n : ℕ) (m : ThinUpperOccurrence (p := p) n) :
    NonzeroIsotropicVector ((8 : ℤ) : ZMod p) := by
  have hm' : m.1 ∈ canonicalThinPopulation (p ^ 2 * n) ∧
      reduceTriple (p := p) m.1 ≠ 0 := by
    simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
  refine ⟨reduceTriple (p := p) m.1, ?_, hm'.2⟩
  rw [← cast_intTunnellQuadratic]
  rw [(mem_canonicalThinPopulation_iff_intTunnellQuadratic
    (p ^ 2 * n) m.1).mp hm'.1]
  simp

/-- Thick analogue. -/
def thickUpperIsotropicVector (n : ℕ) (m : ThickUpperOccurrence (p := p) n) :
    NonzeroIsotropicVector ((32 : ℤ) : ZMod p) := by
  have hm' : m.1 ∈ canonicalThickPopulation (p ^ 2 * n) ∧
      reduceTriple (p := p) m.1 ≠ 0 := by
    simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
  refine ⟨reduceTriple (p := p) m.1, ?_, hm'.2⟩
  rw [← cast_intTunnellQuadratic]
  rw [(mem_canonicalThickPopulation_iff_intTunnellQuadratic
    (p ^ 2 * n) m.1).mp hm'.1]
  simp

def thinUpperDirection (hp2 : p ≠ 2) (n : ℕ)
    (m : ThinUpperOccurrence (p := p) n) :
    ProjectiveConicDirection ((8 : ℤ) : ZMod p) :=
  normalizeProjectiveDirection (eight_ne_zero hp2) (thinUpperIsotropicVector n m)

def thickUpperDirection (hp2 : p ≠ 2) (n : ℕ)
    (m : ThickUpperOccurrence (p := p) n) :
    ProjectiveConicDirection ((32 : ℤ) : ZMod p) :=
  normalizeProjectiveDirection (thirtyTwo_ne_zero hp2) (thickUpperIsotropicVector n m)

/-! ## The nonzero upper branch is an actual rational neighbor point -/

def intTripleSubScale (y : IntTriple) (a : ℤ) (v : IntTriple) : IntTriple :=
  (y.1 - a * v.1, y.2.1 - a * v.2.1, y.2.2 - a * v.2.2)

/-- A line-addressed numerator of norm divisible by `p²` becomes an actual point of
the corresponding rational neighbor after division by `p`. -/
theorem scaledNumerator_mem_integralNeighbor (hp2 : p ≠ 2)
    (C : ℤ) (d : ProjectiveConicDirection (p := p) (C : ZMod p))
    (y : IntTriple) (a : ℤ)
    (ha : (a : ZMod p) ≠ 0)
    (hline : reduceTriple (p := p) y =
      scaleCoordinateTriple (a : ZMod p) (projectiveDirectionVector d.1))
    (hynorm : (p : ℤ) ^ 2 ∣ intTunnellQuadratic C y) :
    ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat y) ∈
      integralNeighbor (p := p) C d := by
  let v := adjustedDirectionLift C d
  let w := intTripleSubScale y a v
  have hw0 : reduceTriple (p := p) w = 0 := by
    have hv := reduce_adjustedDirectionLift (p := p) hp2 C d
    apply Prod.ext
    · have hx := congrArg Prod.fst hline
      have hvx := congrArg Prod.fst hv
      simp [w, intTripleSubScale, reduceTriple, scaleCoordinateTriple] at hx hvx ⊢
      rw [hvx]
      linear_combination hx
    · apply Prod.ext
      · have hy := congrArg (fun q => q.2.1) hline
        have hvy := congrArg (fun q => q.2.1) hv
        simp [w, intTripleSubScale, reduceTriple, scaleCoordinateTriple] at hy hvy ⊢
        rw [hvy]
        linear_combination hy
      · have hz := congrArg (fun q => q.2.2) hline
        have hvz := congrArg (fun q => q.2.2) hv
        simp [w, intTripleSubScale, reduceTriple, scaleCoordinateTriple] at hz hvz ⊢
        rw [hvz]
        linear_combination hz
  let m := divideTripleByPrime (p := p) w
  have hscale : scaleTripleByPrime (p := p) m = w :=
    scale_divideTripleByPrime (p := p) hw0
  have hx : y.1 = (p : ℤ) * m.1 + a * v.1 := by
    have hs := congrArg Prod.fst hscale
    simp [scaleTripleByPrime, w, intTripleSubScale] at hs
    linarith
  have hy : y.2.1 = (p : ℤ) * m.2.1 + a * v.2.1 := by
    have hs := congrArg (fun q => q.2.1) hscale
    simp [scaleTripleByPrime, w, intTripleSubScale] at hs
    linarith
  have hz : y.2.2 = (p : ℤ) * m.2.2 + a * v.2.2 := by
    have hs := congrArg (fun q => q.2.2) hscale
    simp [scaleTripleByPrime, w, intTripleSubScale] at hs
    linarith
  have hpolarization :
      intTunnellQuadratic C y =
        (p : ℤ) ^ 2 * intTunnellQuadratic C m +
        (p : ℤ) * a * intTunnellPolar C m v +
        a ^ 2 * intTunnellQuadratic C v := by
    unfold intTunnellQuadratic intTunnellPolar
    rw [hx, hy, hz]
    ring
  obtain ⟨qy, hqy⟩ := hynorm
  obtain ⟨qv, hqv⟩ :=
    prime_sq_dvd_adjustedDirectionLift_norm (p := p) hp2 C d
  have hcross : (p : ℤ) ^ 2 ∣ (p : ℤ) * a * intTunnellPolar C m v := by
    refine ⟨qy - intTunnellQuadratic C m - a ^ 2 * qv, ?_⟩
    have hqv' : intTunnellQuadratic C v = (p : ℤ) ^ 2 * qv := by
      exact hqv
    calc
      (p : ℤ) * a * intTunnellPolar C m v =
          intTunnellQuadratic C y -
            (p : ℤ) ^ 2 * intTunnellQuadratic C m -
            a ^ 2 * intTunnellQuadratic C v := by
              linear_combination -1 * hpolarization
      _ = (p : ℤ) ^ 2 *
          (qy - intTunnellQuadratic C m - a ^ 2 * qv) := by
            rw [hqy, hqv']
            ring
  obtain ⟨k, hk⟩ := hcross
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hab : a * intTunnellPolar C m v = (p : ℤ) * k := by
    apply mul_left_cancel₀ hp
    calc
      (p : ℤ) * (a * intTunnellPolar C m v) =
          (p : ℤ) * a * intTunnellPolar C m v := by ring
      _ = (p : ℤ) ^ 2 * k := hk
      _ = (p : ℤ) * ((p : ℤ) * k) := by ring
  have hprodRaw : ((a * intTunnellPolar C m v : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr ⟨k, hab⟩
  have hprod : (a : ZMod p) * (intTunnellPolar C m v : ZMod p) = 0 := by
    simpa using hprodRaw
  have hpolarCast : (intTunnellPolar C m v : ZMod p) = 0 := by
    exact (mul_eq_zero.mp hprod).resolve_left ha
  refine ⟨m, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hpolarCast, a, ?_⟩
  have hpQ : (p : ℚ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply Prod.ext
  · simp [ratTripleScale, intTripleToRat, ratTripleAdd]
    field_simp [hpQ]
    exact_mod_cast hx
  · apply Prod.ext
    · simp [ratTripleScale, intTripleToRat, ratTripleAdd]
      field_simp [hpQ]
      exact_mod_cast hy
    · simp [ratTripleScale, intTripleToRat, ratTripleAdd]
      field_simp [hpQ]
      exact_mod_cast hz

/-- Every nonzero upper thin occurrence, divided by `p`, is an actual point of its
uniquely returned neighbor. -/
theorem thinUpperScaledPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (m : ThinUpperOccurrence (p := p) n) :
    ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat m.1) ∈
      integralNeighbor (p := p) 8 (thinUpperDirection hp2 n m) := by
  let v := thinUpperIsotropicVector n m
  let aF := normalizeProjectiveScalar (eight_ne_zero hp2) v
  let a : ℤ := (aF.val : ℤ)
  apply scaledNumerator_mem_integralNeighbor hp2 8 (thinUpperDirection hp2 n m)
    m.1 a
  · have haF := normalizeProjectiveScalar_ne_zero (eight_ne_zero hp2) v
    have haCast : (aF.val : ZMod p) = aF := ZMod.natCast_zmod_val aF
    simpa [a, haCast] using haF
  · have hrecon := scale_normalizeProjectiveDirection (eight_ne_zero hp2) v
    have haCast : (aF.val : ZMod p) = aF := ZMod.natCast_zmod_val aF
    simpa [thinUpperDirection, thinUpperIsotropicVector, v, aF, a, haCast] using hrecon.symm
  · have hm' : m.1 ∈ canonicalThinPopulation (p ^ 2 * n) := by
      have hm' : m.1 ∈ canonicalThinPopulation (p ^ 2 * n) ∧
          reduceTriple (p := p) m.1 ≠ 0 := by
        simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
      exact hm'.1
    have hq := (mem_canonicalThinPopulation_iff_intTunnellQuadratic
      (p ^ 2 * n) m.1).mp hm'
    refine ⟨(n : ℤ), ?_⟩
    calc
      intTunnellQuadratic 8 m.1 = ((p ^ 2 * n : ℕ) : ℤ) := hq
      _ = (p : ℤ) ^ 2 * (n : ℤ) := by norm_cast

/-- Thick analogue. -/
theorem thickUpperScaledPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (m : ThickUpperOccurrence (p := p) n) :
    ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat m.1) ∈
      integralNeighbor (p := p) 32 (thickUpperDirection hp2 n m) := by
  let v := thickUpperIsotropicVector n m
  let aF := normalizeProjectiveScalar (thirtyTwo_ne_zero hp2) v
  let a : ℤ := (aF.val : ℤ)
  apply scaledNumerator_mem_integralNeighbor hp2 32 (thickUpperDirection hp2 n m)
    m.1 a
  · have haF := normalizeProjectiveScalar_ne_zero (thirtyTwo_ne_zero hp2) v
    have haCast : (aF.val : ZMod p) = aF := ZMod.natCast_zmod_val aF
    simpa [a, haCast] using haF
  · have hrecon := scale_normalizeProjectiveDirection (thirtyTwo_ne_zero hp2) v
    have haCast : (aF.val : ZMod p) = aF := ZMod.natCast_zmod_val aF
    simpa [thickUpperDirection, thickUpperIsotropicVector, v, aF, a, haCast] using hrecon.symm
  · have hm' : m.1 ∈ canonicalThickPopulation (p ^ 2 * n) := by
      have hm' : m.1 ∈ canonicalThickPopulation (p ^ 2 * n) ∧
          reduceTriple (p := p) m.1 ≠ 0 := by
        simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
      exact hm'.1
    have hq := (mem_canonicalThickPopulation_iff_intTunnellQuadratic
      (p ^ 2 * n) m.1).mp hm'
    refine ⟨(n : ℤ), ?_⟩
    calc
      intTunnellQuadratic 32 m.1 = ((p ^ 2 * n : ℕ) : ℤ) := hq
      _ = (p : ℤ) ^ 2 * (n : ℤ) := by norm_cast

/-- The unique-direction upper branch, now carrying its neighbor address. -/
def thinUpperDirectedPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ProjectiveConicDirection ((8 : ℤ) : ZMod p) × IntTriple) :=
  (nonzeroResiduePopulation (p := p)
      (canonicalThinPopulation (p ^ 2 * n))).attach.image fun m =>
    (thinUpperDirection hp2 n m, m.1)

def thickUpperDirectedPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ProjectiveConicDirection ((32 : ℤ) : ZMod p) × IntTriple) :=
  (nonzeroResiduePopulation (p := p)
      (canonicalThickPopulation (p ^ 2 * n))).attach.image fun m =>
    (thickUpperDirection hp2 n m, m.1)

theorem thinUpperDirectedPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (thinUpperDirectedPopulation (p := p) hp2 n).card =
      (nonzeroResiduePopulation (p := p)
        (canonicalThinPopulation (p ^ 2 * n))).card := by
  unfold thinUpperDirectedPopulation
  calc
    ((nonzeroResiduePopulation (p := p)
        (canonicalThinPopulation (p ^ 2 * n))).attach.image fun m =>
          (thinUpperDirection hp2 n m, m.1)).card =
        (nonzeroResiduePopulation (p := p)
          (canonicalThinPopulation (p ^ 2 * n))).attach.card := by
            apply Finset.card_image_of_injective
            intro a b hab
            apply Subtype.ext
            exact congrArg Prod.snd hab
    _ = (nonzeroResiduePopulation (p := p)
          (canonicalThinPopulation (p ^ 2 * n))).card := Finset.card_attach

theorem thickUpperDirectedPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    (thickUpperDirectedPopulation (p := p) hp2 n).card =
      (nonzeroResiduePopulation (p := p)
        (canonicalThickPopulation (p ^ 2 * n))).card := by
  unfold thickUpperDirectedPopulation
  calc
    ((nonzeroResiduePopulation (p := p)
        (canonicalThickPopulation (p ^ 2 * n))).attach.image fun m =>
          (thickUpperDirection hp2 n m, m.1)).card =
        (nonzeroResiduePopulation (p := p)
          (canonicalThickPopulation (p ^ 2 * n))).attach.card := by
            apply Finset.card_image_of_injective
            intro a b hab
            apply Subtype.ext
            exact congrArg Prod.snd hab
    _ = (nonzeroResiduePopulation (p := p)
          (canonicalThickPopulation (p ^ 2 * n))).card := Finset.card_attach

abbrev ThinNeighborNumeratorOccurrence :=
  (ProjectiveConicDirection ((8 : ℤ) : ZMod p) × IntTriple) ⊕
    (IntTriple × ((ZMod p × ZMod p) ⊕ ZMod p))

abbrev ThickNeighborNumeratorOccurrence :=
  (ProjectiveConicDirection ((32 : ℤ) : ZMod p) × IntTriple) ⊕
    (IntTriple × ((ZMod p × ZMod p) ⊕ ZMod p))

/-- The complete thin neighbor numerator population: unique nonzero upper lines plus
the full lower orthogonal incidence population. -/
def thinNeighborNumeratorPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ThinNeighborNumeratorOccurrence (p := p)) :=
  (thinUpperDirectedPopulation (p := p) hp2 n).disjSum
    (integralOrthogonalIncidencePopulation (p := p) 8 (canonicalThinPopulation n))

def thickNeighborNumeratorPopulation (hp2 : p ≠ 2) (n : ℕ) :
    Finset (ThickNeighborNumeratorOccurrence (p := p)) :=
  (thickUpperDirectedPopulation (p := p) hp2 n).disjSum
    (integralOrthogonalIncidencePopulation (p := p) 32 (canonicalThickPopulation n))

/-! ## The complete numerator carrier lands in actual neighbor lattices -/

theorem thinUpperDirectedPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    {q : ProjectiveConicDirection ((8 : ℤ) : ZMod p) × IntTriple}
    (hq : q ∈ thinUpperDirectedPopulation (p := p) hp2 n) :
    ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat q.2) ∈
      integralNeighbor (p := p) 8 q.1 := by
  rcases Finset.mem_image.mp hq with ⟨m, hm, hmq⟩
  rw [← hmq]
  exact thinUpperScaledPoint_mem_integralNeighbor hp2 n m

theorem thickUpperDirectedPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    {q : ProjectiveConicDirection ((32 : ℤ) : ZMod p) × IntTriple}
    (hq : q ∈ thickUpperDirectedPopulation (p := p) hp2 n) :
    ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat q.2) ∈
      integralNeighbor (p := p) 32 q.1 := by
  rcases Finset.mem_image.mp hq with ⟨m, hm, hmq⟩
  rw [← hmq]
  exact thickUpperScaledPoint_mem_integralNeighbor hp2 n m

/-- The neighbor direction returned by a complete thin numerator occurrence. -/
def thinNumeratorDirection (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thinNeighborNumeratorPopulation (p := p) hp2 n}) :
    ProjectiveConicDirection ((8 : ℤ) : ZMod p) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper => exact upper.1
  | inr lower =>
      apply incidenceProjectiveDirection (p := p) 8 (canonicalThinPopulation n)
      exact ⟨lower, by simpa [thinNeighborNumeratorPopulation] using hq⟩

def thickNumeratorDirection (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thickNeighborNumeratorPopulation (p := p) hp2 n}) :
    ProjectiveConicDirection ((32 : ℤ) : ZMod p) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper => exact upper.1
  | inr lower =>
      apply incidenceProjectiveDirection (p := p) 32 (canonicalThickPopulation n)
      exact ⟨lower, by simpa [thickNeighborNumeratorPopulation] using hq⟩

/-- The rational point returned by the same occurrence. -/
def thinNumeratorPoint (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thinNeighborNumeratorPopulation (p := p) hp2 n}) : RatTriple :=
  match q.1 with
  | .inl upper =>
      ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)
  | .inr lower => intTripleToRat lower.1

def thickNumeratorPoint (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thickNeighborNumeratorPopulation (p := p) hp2 n}) : RatTriple :=
  match q.1 with
  | .inl upper =>
      ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)
  | .inr lower => intTripleToRat lower.1

/-- **EVERY THIN NUMERATOR OCCURRENCE IS AN ADDRESSED ACTUAL NEIGHBOR POINT.** -/
theorem thinNumeratorPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thinNeighborNumeratorPopulation (p := p) hp2 n}) :
    thinNumeratorPoint hp2 n q ∈
      integralNeighbor (p := p) 8 (thinNumeratorDirection hp2 n q) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      exact thinUpperDirectedPoint_mem_integralNeighbor hp2 n
        (by simpa [thinNeighborNumeratorPopulation] using hq)
  | inr lower =>
      apply incidenceVector_mem_integralNeighbor hp2 8 (canonicalThinPopulation n)
        ⟨lower, by simpa [thinNeighborNumeratorPopulation] using hq⟩

/-- **EVERY THICK NUMERATOR OCCURRENCE IS AN ADDRESSED ACTUAL NEIGHBOR POINT.** -/
theorem thickNumeratorPoint_mem_integralNeighbor (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thickNeighborNumeratorPopulation (p := p) hp2 n}) :
    thickNumeratorPoint hp2 n q ∈
      integralNeighbor (p := p) 32 (thickNumeratorDirection hp2 n q) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      exact thickUpperDirectedPoint_mem_integralNeighbor hp2 n
        (by simpa [thickNeighborNumeratorPopulation] using hq)
  | inr lower =>
      apply incidenceVector_mem_integralNeighbor hp2 32 (canonicalThickPopulation n)
        ⟨lower, by simpa [thickNeighborNumeratorPopulation] using hq⟩

theorem ratTunnellQuadratic_intTripleToRat (C : ℤ) (m : IntTriple) :
    ratTunnellQuadratic C (intTripleToRat m) = (intTunnellQuadratic C m : ℚ) := by
  simp [ratTunnellQuadratic, intTripleToRat, intTunnellQuadratic]

theorem ratTunnellQuadratic_scaled_intTriple (C : ℤ) (m : IntTriple) :
    ratTunnellQuadratic C
        (ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat m)) =
      (intTunnellQuadratic C m : ℚ) / (p : ℚ) ^ 2 := by
  simp [ratTunnellQuadratic, ratTripleScale, intTripleToRat,
    intTunnellQuadratic]
  ring

/-- Every point of the thin numerator carrier has exactly the requested rational
quadratic norm `n`. -/
theorem thinNumeratorPoint_norm (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thinNeighborNumeratorPopulation (p := p) hp2 n}) :
    ratTunnellQuadratic 8 (thinNumeratorPoint hp2 n q) = (n : ℚ) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ thinUpperDirectedPopulation (p := p) hp2 n := by
        simpa [thinNeighborNumeratorPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      have hm' : m.1 ∈ canonicalThinPopulation (p ^ 2 * n) := by
        have hm' : m.1 ∈ canonicalThinPopulation (p ^ 2 * n) ∧
            reduceTriple (p := p) m.1 ≠ 0 := by
          simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
        exact hm'.1
      have hnorm := (mem_canonicalThinPopulation_iff_intTunnellQuadratic
        (p ^ 2 * n) m.1).mp hm'
      change ratTunnellQuadratic 8
        (ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)) = (n : ℚ)
      rw [← hmu, ratTunnellQuadratic_scaled_intTriple, hnorm]
      have hpQ : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      push_cast
      field_simp [hpQ]
  | inr lower =>
      have hl : lower ∈ integralOrthogonalIncidencePopulation (p := p) 8
          (canonicalThinPopulation n) := by
        simpa [thinNeighborNumeratorPopulation] using hq
      have hl' := hl
      simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
        Finset.mem_product] at hl'
      change ratTunnellQuadratic 8 (intTripleToRat lower.1) = (n : ℚ)
      rw [ratTunnellQuadratic_intTripleToRat,
        (mem_canonicalThinPopulation_iff_intTunnellQuadratic n lower.1).mp hl'.1.1]
      norm_cast

/-- Thick analogue. -/
theorem thickNumeratorPoint_norm (hp2 : p ≠ 2) (n : ℕ)
    (q : {q // q ∈ thickNeighborNumeratorPopulation (p := p) hp2 n}) :
    ratTunnellQuadratic 32 (thickNumeratorPoint hp2 n q) = (n : ℚ) := by
  rcases q with ⟨q, hq⟩
  cases q with
  | inl upper =>
      have hu : upper ∈ thickUpperDirectedPopulation (p := p) hp2 n := by
        simpa [thickNeighborNumeratorPopulation] using hq
      rcases Finset.mem_image.mp hu with ⟨m, hm, hmu⟩
      have hm' : m.1 ∈ canonicalThickPopulation (p ^ 2 * n) := by
        have hm' : m.1 ∈ canonicalThickPopulation (p ^ 2 * n) ∧
            reduceTriple (p := p) m.1 ≠ 0 := by
          simpa only [nonzeroResiduePopulation, Finset.mem_filter] using m.2
        exact hm'.1
      have hnorm := (mem_canonicalThickPopulation_iff_intTunnellQuadratic
        (p ^ 2 * n) m.1).mp hm'
      change ratTunnellQuadratic 32
        (ratTripleScale ((1 : ℚ) / (p : ℚ)) (intTripleToRat upper.2)) = (n : ℚ)
      rw [← hmu, ratTunnellQuadratic_scaled_intTriple, hnorm]
      have hpQ : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      push_cast
      field_simp [hpQ]
  | inr lower =>
      have hl : lower ∈ integralOrthogonalIncidencePopulation (p := p) 32
          (canonicalThickPopulation n) := by
        simpa [thickNeighborNumeratorPopulation] using hq
      have hl' := hl
      simp only [integralOrthogonalIncidencePopulation, Finset.mem_filter,
        Finset.mem_product] at hl'
      change ratTunnellQuadratic 32 (intTripleToRat lower.1) = (n : ℚ)
      rw [ratTunnellQuadratic_intTripleToRat,
        (mem_canonicalThickPopulation_iff_intTunnellQuadratic n lower.1).mp hl'.1.1]
      norm_cast

private theorem zero_add_nonzero_card (s : Finset IntTriple) :
    (zeroResiduePopulation (p := p) s).card +
      (nonzeroResiduePopulation (p := p) s).card = s.card := by
  simpa [zeroResiduePopulation, nonzeroResiduePopulation] using
    Finset.card_filter_add_card_filter_not
      (s := s) (fun m : IntTriple => reduceTriple (p := p) m = 0)

private theorem upper_nonzero_card_thin (n : ℕ) :
    ((nonzeroResiduePopulation (p := p)
      (canonicalThinPopulation (p ^ 2 * n))).card : ℤ) =
      ((canonicalThinPopulation (p ^ 2 * n)).card : ℤ) -
        ((canonicalThinPopulation n).card : ℤ) := by
  have hpart := zero_add_nonzero_card (p := p)
    (canonicalThinPopulation (p ^ 2 * n))
  have hpartZ :
      ((zeroResiduePopulation (p := p)
          (canonicalThinPopulation (p ^ 2 * n))).card : ℤ) +
        ((nonzeroResiduePopulation (p := p)
          (canonicalThinPopulation (p ^ 2 * n))).card : ℤ) =
        ((canonicalThinPopulation (p ^ 2 * n)).card : ℤ) := by
    exact_mod_cast hpart
  have hzeroZ :
      ((zeroResiduePopulation (p := p)
        (canonicalThinPopulation (p ^ 2 * n))).card : ℤ) =
        ((canonicalThinPopulation n).card : ℤ) := by
    exact_mod_cast zeroResidue_canonicalThinPopulation_card (p := p) n
  rw [hzeroZ] at hpartZ
  omega

private theorem upper_nonzero_card_thick (n : ℕ) :
    ((nonzeroResiduePopulation (p := p)
      (canonicalThickPopulation (p ^ 2 * n))).card : ℤ) =
      ((canonicalThickPopulation (p ^ 2 * n)).card : ℤ) -
        ((canonicalThickPopulation n).card : ℤ) := by
  have hpart := zero_add_nonzero_card (p := p)
    (canonicalThickPopulation (p ^ 2 * n))
  have hpartZ :
      ((zeroResiduePopulation (p := p)
          (canonicalThickPopulation (p ^ 2 * n))).card : ℤ) +
        ((nonzeroResiduePopulation (p := p)
          (canonicalThickPopulation (p ^ 2 * n))).card : ℤ) =
        ((canonicalThickPopulation (p ^ 2 * n)).card : ℤ) := by
    exact_mod_cast hpart
  have hzeroZ :
      ((zeroResiduePopulation (p := p)
        (canonicalThickPopulation (p ^ 2 * n))).card : ℤ) =
        ((canonicalThickPopulation n).card : ℤ) := by
    exact_mod_cast zeroResidue_canonicalThickPopulation_card (p := p) n
  rw [hzeroZ] at hpartZ
  omega

/-- **THIN NEIGHBOR DOUBLE COUNT.** -/
theorem thinNeighborNumeratorPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    ((thinNeighborNumeratorPopulation (p := p) hp2 n).card : ℤ) =
      ((canonicalThinPopulation (p ^ 2 * n)).card : ℤ) +
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((canonicalThinPopulation n).card : ℤ) +
      (p : ℤ) *
        (if p ^ 2 ∣ n then ((canonicalThinPopulation (n / p ^ 2)).card : ℤ)
          else 0) := by
  rw [thinNeighborNumeratorPopulation, Finset.card_disjSum,
    Int.natCast_add, thinUpperDirectedPopulation_card,
    upper_nonzero_card_thin]
  have hinc := thin_incidence_defect (p := p) hp2 n
  linear_combination hinc

/-- **THICK NEIGHBOR DOUBLE COUNT.** -/
theorem thickNeighborNumeratorPopulation_card (hp2 : p ≠ 2) (n : ℕ) :
    ((thickNeighborNumeratorPopulation (p := p) hp2 n).card : ℤ) =
      ((canonicalThickPopulation (p ^ 2 * n)).card : ℤ) +
      quadraticChar (ZMod p) (-(n : ZMod p)) *
          ((canonicalThickPopulation n).card : ℤ) +
      (p : ℤ) *
        (if p ^ 2 ∣ n then ((canonicalThickPopulation (n / p ^ 2)).card : ℤ)
          else 0) := by
  rw [thickNeighborNumeratorPopulation, Finset.card_disjSum,
    Int.natCast_add, thickUpperDirectedPopulation_card,
    upper_nonzero_card_thick]
  have hinc := thick_incidence_defect (p := p) hp2 n
  linear_combination hinc

#print axioms thinUpperIsotropicVector
#print axioms thinUpperDirectedPopulation_card
#print axioms thinNeighborNumeratorPopulation_card
#print axioms thickNeighborNumeratorPopulation_card

end Soma.Holonics.Millennium.FamilyTunnellHeckeDoubleCount

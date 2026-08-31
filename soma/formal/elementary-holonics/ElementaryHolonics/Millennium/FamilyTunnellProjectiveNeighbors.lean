import ElementaryHolonics.Millennium.FamilyTunnellOddTestVector

/-!
# The odd-prime projective neighbor carrier of the Tunnell lattices

At an odd prime, a ternary `p`-neighbor is addressed by an isotropic line in the
projective reduction of the quadratic lattice.  This file constructs that finite
projective carrier for the two Tunnell forms rather than assuming its size.

For the reduced form

`Q_c(x,y,z) = 2x² + y² + c z²`,

the normalized projective charts are

* `(1,y,z)`, and
* `(0,1,z)`.

The third possible pivot `(0,0,1)` is not isotropic when `c ≠ 0`.  We prove from
finite incidence that the two retained charts contain exactly `p+1` isotropic
directions.  The central character sum is derived by an explicit swing

`(x,y) ↔ (x-y,x+y)`

between a difference-of-squares fibre and a hyperbola, not imported as a packaged
conic theorem.  Instantiating `c=8` and `c=32` supplies the complete neighbor-index
carrier for both Tunnell lattices at every odd prime.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors

open Finset

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The finite difference-square/hyperbola swing -/

/-- The complete affine fibre `y² = x² - D`. -/
def differenceSquarePopulation (D : ZMod p) : Finset (ZMod p × ZMod p) :=
  (univ ×ˢ univ).filter fun q => q.2 ^ 2 = q.1 ^ 2 - D

/-- The complete hyperbola fibre `uv = D`. -/
def hyperbolaPopulation (D : ZMod p) : Finset (ZMod p × ZMod p) :=
  (univ ×ˢ univ).filter fun q => q.1 * q.2 = D

private def nonzeroToHyperbola (D : ZMod p) (u : ZMod p) : ZMod p × ZMod p :=
  (u, D / u)

private def hyperbolaToNonzero (q : ZMod p × ZMod p) : ZMod p := q.1

/-- A nonzero hyperbola has one point for every nonzero first coordinate. -/
theorem hyperbolaPopulation_card {D : ZMod p} (hD : D ≠ 0) :
    (hyperbolaPopulation D).card = (univ.erase (0 : ZMod p)).card := by
  classical
  refine Finset.card_nbij' hyperbolaToNonzero (nonzeroToHyperbola D) ?_ ?_ ?_ ?_
  · intro q hq
    change q ∈ hyperbolaPopulation D at hq
    simp only [hyperbolaPopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hq
    change hyperbolaToNonzero q ∈ univ.erase 0
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true]
    intro hq0
    change q.1 = 0 at hq0
    apply hD
    rw [← hq, hq0, zero_mul]
  · intro u hu
    change u ∈ univ.erase 0 at hu
    simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hu
    change nonzeroToHyperbola D u ∈ hyperbolaPopulation D
    simp only [hyperbolaPopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, nonzeroToHyperbola]
    field_simp
  · intro q hq
    change q ∈ hyperbolaPopulation D at hq
    simp only [hyperbolaPopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hq
    have hq0 : q.1 ≠ 0 := by
      intro h0
      apply hD
      rw [← hq, h0, zero_mul]
    apply Prod.ext
    · rfl
    · dsimp [nonzeroToHyperbola, hyperbolaToNonzero]
      field_simp
      rw [hq]
  · intro u hu
    rfl

private def differenceToHyperbola (q : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (q.1 - q.2, q.1 + q.2)

private def hyperbolaToDifference (q : ZMod p × ZMod p) : ZMod p × ZMod p :=
  ((q.2 + q.1) / 2, (q.2 - q.1) / 2)

/-- The swing from the difference-of-squares chart to the product chart is an exact
finite equivalence at every odd prime. -/
theorem differenceSquarePopulation_card_eq_hyperbolaPopulation_card
    (hp2 : p ≠ 2) (D : ZMod p) :
    (differenceSquarePopulation D).card = (hyperbolaPopulation D).card := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  refine Finset.card_nbij' differenceToHyperbola hyperbolaToDifference ?_ ?_ ?_ ?_
  · intro q hq
    change q ∈ differenceSquarePopulation D at hq
    simp only [differenceSquarePopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hq
    change differenceToHyperbola q ∈ hyperbolaPopulation D
    simp only [hyperbolaPopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, differenceToHyperbola]
    linear_combination -hq
  · intro q hq
    change q ∈ hyperbolaPopulation D at hq
    simp only [hyperbolaPopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and] at hq
    change hyperbolaToDifference q ∈ differenceSquarePopulation D
    simp only [differenceSquarePopulation, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and, hyperbolaToDifference]
    field_simp
    linear_combination -4 * hq
  · intro q hq
    apply Prod.ext <;>
      dsimp [differenceToHyperbola, hyperbolaToDifference] <;> field_simp <;> ring
  · intro q hq
    apply Prod.ext <;>
      dsimp [differenceToHyperbola, hyperbolaToDifference] <;> field_simp <;> ring

private theorem differenceSquarePopulation_card_eq_sum_fibres (D : ZMod p) :
    (differenceSquarePopulation D).card =
      ∑ x : ZMod p, (univ.filter fun y : ZMod p => y ^ 2 = x ^ 2 - D).card := by
  unfold differenceSquarePopulation
  rw [Finset.card_filter, Finset.sum_product]
  simp only [Finset.card_filter]

/-! ## 2. The character sum founded by the finite swing -/

/-- The classical quadratic-polynomial sum, proved here by counting the complete
difference-square occurrence population in its two charts. -/
theorem quadraticChar_sum_square_sub (hp2 : p ≠ 2)
    {D : ZMod p} (hD : D ≠ 0) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 - D) = -1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hpairFiber := differenceSquarePopulation_card_eq_sum_fibres (p := p) D
  have hpair : (differenceSquarePopulation D).card = p - 1 := by
    rw [differenceSquarePopulation_card_eq_hyperbolaPopulation_card hp2,
      hyperbolaPopulation_card hD,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : ZMod p)),
      Finset.card_univ, ZMod.card]
  have hroot : ∀ x : ZMod p,
      ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 2 - D).card : ℤ) =
        quadraticChar (ZMod p) (x ^ 2 - D) + 1 := by
    intro x
    simpa [Set.toFinset_setOf] using quadraticChar_card_sqrts hchar (x ^ 2 - D)
  have hpairZ :
      ((differenceSquarePopulation D).card : ℤ) =
        ∑ x : ZMod p,
          ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 2 - D).card : ℤ) := by
    exact_mod_cast hpairFiber
  calc
    (∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 - D)) =
        ∑ x : ZMod p,
          (((univ.filter fun y : ZMod p => y ^ 2 = x ^ 2 - D).card : ℤ) - 1) := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hroot]
            ring
    _ = ((differenceSquarePopulation D).card : ℤ) - p := by
      rw [Finset.sum_sub_distrib, hpairZ, Finset.sum_const,
        Finset.card_univ, ZMod.card]
      simp
    _ = -1 := by
      rw [hpair]
      have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
      omega

private theorem quadraticChar_inv_eq_self {a : ZMod p} (ha : a ≠ 0) :
    quadraticChar (ZMod p) a⁻¹ = quadraticChar (ZMod p) a := by
  have hforward :
      quadraticChar (ZMod p) a⁻¹ * quadraticChar (ZMod p) a = 1 := by
    rw [← map_mul, inv_mul_cancel₀ ha, map_one]
  have hreturn :
      quadraticChar (ZMod p) a * quadraticChar (ZMod p) a = 1 :=
    by simpa [pow_two] using quadraticChar_sq_one ha
  calc
    quadraticChar (ZMod p) a⁻¹ =
        quadraticChar (ZMod p) a⁻¹ *
          (quadraticChar (ZMod p) a * quadraticChar (ZMod p) a) := by rw [hreturn, mul_one]
    _ = (quadraticChar (ZMod p) a⁻¹ * quadraticChar (ZMod p) a) *
        quadraticChar (ZMod p) a := by ring
    _ = quadraticChar (ZMod p) a := by rw [hforward, one_mul]

/-- Scaling and translating the square gives the uniform binary character sum. -/
theorem quadraticChar_sum_scaled_square_add (hp2 : p ≠ 2)
    {A B : ZMod p} (hA : A ≠ 0) (hB : B ≠ 0) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (A * x ^ 2 + B) =
      -quadraticChar (ZMod p) A := by
  have hD : -B / A ≠ 0 := div_ne_zero (neg_ne_zero.mpr hB) hA
  have harg : ∀ x : ZMod p, A * x ^ 2 + B = A * (x ^ 2 - (-B / A)) := by
    intro x
    field_simp
    ring
  calc
    (∑ x : ZMod p, quadraticChar (ZMod p) (A * x ^ 2 + B)) =
        ∑ x : ZMod p,
          quadraticChar (ZMod p) A *
            quadraticChar (ZMod p) (x ^ 2 - (-B / A)) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [harg, map_mul]
    _ = quadraticChar (ZMod p) A *
        ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 2 - (-B / A)) := by
          rw [Finset.mul_sum]
    _ = -quadraticChar (ZMod p) A := by
      rw [quadraticChar_sum_square_sub hp2 hD]
      ring

/-! ## 3. The normalized projective conic carrier -/

/-- The affine projective chart `(1,y,z)` of `Q_c=0`. -/
def affineConicPopulation (c : ZMod p) : Finset (ZMod p × ZMod p) :=
  (univ ×ˢ univ).filter fun q => 2 + q.1 ^ 2 + c * q.2 ^ 2 = 0

/-- The projective chart at `x=0`, normalized as `(0,1,z)`. -/
def infinityConicPopulation (c : ZMod p) : Finset (ZMod p) :=
  univ.filter fun z => 1 + c * z ^ 2 = 0

/-- Every normalized isotropic direction, retaining its chart of origin. -/
def projectiveConicDirections (c : ZMod p) :
    Finset ((ZMod p × ZMod p) ⊕ ZMod p) :=
  (affineConicPopulation c).disjSum (infinityConicPopulation c)

private theorem affineConicPopulation_card_cast (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) :
    ((affineConicPopulation c).card : ℤ) =
      (p : ℤ) - quadraticChar (ZMod p) (-c) := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hfiber : (affineConicPopulation c).card =
      ∑ z : ZMod p,
        (univ.filter fun y : ZMod p => y ^ 2 = -(c * z ^ 2) + (-2)).card := by
    unfold affineConicPopulation
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro y hy
    by_cases h : 2 + y ^ 2 + c * z ^ 2 = 0
    · have h' : y ^ 2 = -(c * z ^ 2) + (-2) := by
        linear_combination h
      simp [h, h']
    · have h' : ¬ y ^ 2 = -(c * z ^ 2) + (-2) := by
        intro h'
        apply h
        linear_combination h'
      simp [h, h']
  have hroot : ∀ z : ZMod p,
      ((univ.filter fun y : ZMod p => y ^ 2 = -(c * z ^ 2) + (-2)).card : ℤ) =
        quadraticChar (ZMod p) (-(c * z ^ 2) + (-2)) + 1 := by
    intro z
    simpa [Set.toFinset_setOf] using
      quadraticChar_card_sqrts hchar (-(c * z ^ 2) + (-2))
  have hsum := quadraticChar_sum_scaled_square_add (p := p) hp2
    (A := -c) (B := -2) (neg_ne_zero.mpr hc) (by
      exact neg_ne_zero.mpr (Ring.two_ne_zero hchar))
  have hsum' :
      ∑ z : ZMod p, quadraticChar (ZMod p) (-(c * z ^ 2) + (-2)) =
        -quadraticChar (ZMod p) (-c) := by
    simpa [neg_mul] using hsum
  have hfiberZ : ((affineConicPopulation c).card : ℤ) =
      ∑ z : ZMod p,
        ((univ.filter fun y : ZMod p => y ^ 2 = -(c * z ^ 2) + (-2)).card : ℤ) := by
    exact_mod_cast hfiber
  calc
    ((affineConicPopulation c).card : ℤ) =
        ∑ z : ZMod p,
          ((univ.filter fun y : ZMod p => y ^ 2 = -(c * z ^ 2) + (-2)).card : ℤ) := hfiberZ
    _ = ∑ z : ZMod p,
        (quadraticChar (ZMod p) (-(c * z ^ 2) + (-2)) + 1) := by
          apply Finset.sum_congr rfl
          intro z hz
          exact hroot z
    _ = (p : ℤ) - quadraticChar (ZMod p) (-c) := by
      rw [Finset.sum_add_distrib, hsum', Finset.sum_const,
        Finset.card_univ, ZMod.card]
      simp
      ring

/-- Exact signed cardinal of the infinity chart.  This is public because later
orthogonal-incidence charts can return entirely through this boundary face. -/
theorem infinityConicPopulation_card_cast (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) :
    ((infinityConicPopulation c).card : ℤ) =
      quadraticChar (ZMod p) (-c) + 1 := by
  classical
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have harg : ∀ z : ZMod p, 1 + c * z ^ 2 = 0 ↔ z ^ 2 = (-c)⁻¹ := by
    intro z
    constructor <;> intro h
    · field_simp
      linear_combination h
    · have hcneg : -c ≠ 0 := neg_ne_zero.mpr hc
      have hmul : z ^ 2 * (-c) = 1 := by
        rw [h, inv_mul_cancel₀ hcneg]
      linear_combination -hmul
  have hset : infinityConicPopulation c =
      univ.filter fun z : ZMod p => z ^ 2 = (-c)⁻¹ := by
    ext z
    simp [infinityConicPopulation, harg]
  have hroot := quadraticChar_card_sqrts hchar ((-c)⁻¹)
  rw [hset]
  have hroot' :
      ((univ.filter fun z : ZMod p => z ^ 2 = (-c)⁻¹).card : ℤ) =
        quadraticChar (ZMod p) ((-c)⁻¹) + 1 := by
    simpa [Set.toFinset_setOf] using hroot
  rw [hroot', quadraticChar_inv_eq_self (neg_ne_zero.mpr hc)]

/-- **A NONDEGENERATE TERNARY CONIC HAS `p+1` ADDRESSED DIRECTIONS.**

This is the precise finite neighbor index.  The proof returns the two chart counts
whose character terms cancel; it does not infer the answer from projective-space
cardinality. -/
theorem projectiveConicDirections_card (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) :
    (projectiveConicDirections c).card = p + 1 := by
  have ha := affineConicPopulation_card_cast (p := p) hp2 hc
  have hi := infinityConicPopulation_card_cast (p := p) hp2 hc
  have htotalZ : ((projectiveConicDirections c).card : ℤ) = (p : ℤ) + 1 := by
    simp only [projectiveConicDirections, Finset.card_disjSum, Int.natCast_add]
    omega
  exact_mod_cast htotalZ

/-! ## 4. The directions as addressed normalized vectors -/

/-- The ternary coordinate carrier used by the reduced quadratic lattice. -/
abbrev CoordinateTriple (R : Type) := R × R × R

/-- The reduced Tunnell form on an explicitly addressed coordinate triple. -/
def reducedTunnellQuadratic (c : ZMod p) (v : CoordinateTriple (ZMod p)) : ZMod p :=
  2 * v.1 ^ 2 + v.2.1 ^ 2 + c * v.2.2 ^ 2

/-- The normalized vector carried by a projective chart occurrence.  The pivot is
retained: it is `x=1` in the affine chart and `x=0,y=1` at infinity. -/
def projectiveDirectionVector :
    ((ZMod p × ZMod p) ⊕ ZMod p) → CoordinateTriple (ZMod p)
  | .inl q => (1, q.1, q.2)
  | .inr z => (0, 1, z)

/-- The actual finite type of addressed normalized isotropic directions. -/
abbrev ProjectiveConicDirection (c : ZMod p) :=
  {d // d ∈ projectiveConicDirections c}

/-- Every admitted chart occurrence returns an isotropic vector. -/
theorem projectiveDirectionVector_isotropic {c : ZMod p}
    (d : ProjectiveConicDirection c) :
    reducedTunnellQuadratic c (projectiveDirectionVector d.1) = 0 := by
  rcases d with ⟨d, hd⟩
  cases d with
  | inl q =>
      have hd' : q ∈ affineConicPopulation c := by
        simpa [projectiveConicDirections] using hd
      simpa [affineConicPopulation, reducedTunnellQuadratic,
        projectiveDirectionVector] using hd'
  | inr z =>
      have hd' : z ∈ infinityConicPopulation c := by
        simpa [projectiveConicDirections] using hd
      simpa [infinityConicPopulation, reducedTunnellQuadratic,
        projectiveDirectionVector] using hd'

/-- No projective direction collapses to the zero coordinate triple. -/
theorem projectiveDirectionVector_ne_zero {c : ZMod p}
    (d : ProjectiveConicDirection c) :
    projectiveDirectionVector d.1 ≠ (0, 0, 0) := by
  rcases d with ⟨d, hd⟩
  cases d <;> simp [projectiveDirectionVector]

/-- The subtype carrier has the same exact `p+1` population as its finite chart. -/
theorem projectiveConicDirection_fintype_card (hp2 : p ≠ 2)
    {c : ZMod p} (hc : c ≠ 0) :
    Fintype.card (ProjectiveConicDirection c) = p + 1 := by
  simpa [ProjectiveConicDirection] using projectiveConicDirections_card hp2 hc

/-- Nonzero isotropic vectors before quotienting by scalar transport. -/
abbrev NonzeroIsotropicVector (c : ZMod p) :=
  {v : CoordinateTriple (ZMod p) //
    reducedTunnellQuadratic c v = 0 ∧ v ≠ (0, 0, 0)}

/-- Scalar transport on an addressed ternary vector. -/
def scaleCoordinateTriple (a : ZMod p) (v : CoordinateTriple (ZMod p)) :
    CoordinateTriple (ZMod p) :=
  (a * v.1, a * v.2.1, a * v.2.2)

private theorem second_ne_zero_of_first_eq_zero {c : ZMod p} (hc : c ≠ 0)
    (v : NonzeroIsotropicVector c) (hx : v.1.1 = 0) : v.1.2.1 ≠ 0 := by
  intro hy
  have hcz : c * v.1.2.2 ^ 2 = 0 := by
    have hq := v.2.1
    simpa [reducedTunnellQuadratic, hx, hy] using hq
  have hzsq : v.1.2.2 ^ 2 = 0 := (mul_eq_zero.mp hcz).resolve_left hc
  have hz : v.1.2.2 = 0 := by
    exact pow_eq_zero hzsq
  apply v.2.2
  apply Prod.ext
  · simpa using hx
  · apply Prod.ext <;> assumption

/-- Normalize a nonzero isotropic vector by its first available pivot. -/
def normalizeProjectiveDirection {c : ZMod p} (hc : c ≠ 0)
    (v : NonzeroIsotropicVector c) : ProjectiveConicDirection c := by
  by_cases hx : v.1.1 = 0
  · have hy := second_ne_zero_of_first_eq_zero hc v hx
    refine ⟨.inr (v.1.2.2 / v.1.2.1), ?_⟩
    simp only [projectiveConicDirections]
    simp [infinityConicPopulation]
    field_simp [hy]
    have hq := v.2.1
    simp [reducedTunnellQuadratic, hx] at hq
    linear_combination hq
  · refine ⟨.inl (v.1.2.1 / v.1.1, v.1.2.2 / v.1.1), ?_⟩
    simp only [projectiveConicDirections]
    simp [affineConicPopulation]
    field_simp [hx]
    have hq := v.2.1
    unfold reducedTunnellQuadratic at hq
    linear_combination hq

/-- The scalar deleted by projective normalization is retained explicitly. -/
def normalizeProjectiveScalar {c : ZMod p} (hc : c ≠ 0)
    (v : NonzeroIsotropicVector c) : ZMod p :=
  if v.1.1 = 0 then v.1.2.1 else v.1.1

/-- Projective normalization reconstructs the complete source vector together with
its nonzero scalar fibre. -/
theorem scale_normalizeProjectiveDirection {c : ZMod p} (hc : c ≠ 0)
    (v : NonzeroIsotropicVector c) :
    scaleCoordinateTriple (normalizeProjectiveScalar hc v)
        (projectiveDirectionVector (normalizeProjectiveDirection hc v).1) = v.1 := by
  by_cases hx : v.1.1 = 0
  · have hy := second_ne_zero_of_first_eq_zero hc v hx
    apply Prod.ext
    · simp [normalizeProjectiveScalar, normalizeProjectiveDirection, hx,
        scaleCoordinateTriple, projectiveDirectionVector]
    · apply Prod.ext
      · simp [normalizeProjectiveScalar, normalizeProjectiveDirection, hx,
          scaleCoordinateTriple, projectiveDirectionVector]
      · simp [normalizeProjectiveScalar, normalizeProjectiveDirection, hx,
          scaleCoordinateTriple, projectiveDirectionVector]
        field_simp
  · apply Prod.ext
    · simp [normalizeProjectiveScalar, normalizeProjectiveDirection, hx,
        scaleCoordinateTriple, projectiveDirectionVector]
    · apply Prod.ext <;>
        simp [normalizeProjectiveScalar, normalizeProjectiveDirection, hx,
          scaleCoordinateTriple, projectiveDirectionVector] <;> field_simp

theorem normalizeProjectiveScalar_ne_zero {c : ZMod p} (hc : c ≠ 0)
    (v : NonzeroIsotropicVector c) : normalizeProjectiveScalar hc v ≠ 0 := by
  by_cases hx : v.1.1 = 0
  · simpa [normalizeProjectiveScalar, hx] using
      second_ne_zero_of_first_eq_zero hc v hx
  · simpa [normalizeProjectiveScalar, hx]

/-- Quadratic scaling is the square of the retained scalar fibre. -/
theorem reducedTunnellQuadratic_scale (c a : ZMod p)
    (v : CoordinateTriple (ZMod p)) :
    reducedTunnellQuadratic c (scaleCoordinateTriple a v) =
      a ^ 2 * reducedTunnellQuadratic c v := by
  simp [reducedTunnellQuadratic, scaleCoordinateTriple]
  ring

/-- The nonzero scalar fibre deleted by the projective receiver. -/
abbrev NonzeroProjectiveScalar := {a : ZMod p // a ≠ 0}

private def directionScalarVector {c : ZMod p}
    (q : ProjectiveConicDirection c × NonzeroProjectiveScalar (p := p)) :
    NonzeroIsotropicVector c := by
  refine ⟨scaleCoordinateTriple q.2.1 (projectiveDirectionVector q.1.1), ?_, ?_⟩
  · rw [reducedTunnellQuadratic_scale, projectiveDirectionVector_isotropic]
    ring
  · rcases q with ⟨⟨d, hd⟩, a, ha⟩
    cases d with
    | inl yz =>
        intro h
        have hfirst := congrArg Prod.fst h
        simp [scaleCoordinateTriple, projectiveDirectionVector] at hfirst
        exact ha hfirst
    | inr z =>
        intro h
        have hsecond := congrArg (fun v => v.2.1) h
        simp [scaleCoordinateTriple, projectiveDirectionVector] at hsecond
        exact ha hsecond

private theorem normalize_directionScalarVector {c : ZMod p} (hc : c ≠ 0)
    (q : ProjectiveConicDirection c × NonzeroProjectiveScalar (p := p)) :
    normalizeProjectiveDirection hc (directionScalarVector q) = q.1 := by
  rcases q with ⟨⟨d, hd⟩, a, ha⟩
  apply Subtype.ext
  cases d with
  | inl yz =>
      simp [directionScalarVector, normalizeProjectiveDirection,
        scaleCoordinateTriple, projectiveDirectionVector, ha]
  | inr z =>
      simp [directionScalarVector, normalizeProjectiveDirection,
        scaleCoordinateTriple, projectiveDirectionVector, ha]

private theorem scalar_directionScalarVector {c : ZMod p} (hc : c ≠ 0)
    (q : ProjectiveConicDirection c × NonzeroProjectiveScalar (p := p)) :
    normalizeProjectiveScalar hc (directionScalarVector q) = q.2.1 := by
  rcases q with ⟨⟨d, hd⟩, a, ha⟩
  cases d <;>
    simp [directionScalarVector, normalizeProjectiveScalar,
      scaleCoordinateTriple, projectiveDirectionVector, ha]

/-- **NONZERO ISOTROPIC VECTORS ARE EXACTLY DIRECTION×NONZERO-SCALAR.**

This is the complete reconstruction fibre of projectivization and supplies the
unique direction/scalar address used by the neighbor incidence double count. -/
def nonzeroIsotropicVectorEquivDirectionScalar {c : ZMod p} (hc : c ≠ 0) :
    NonzeroIsotropicVector c ≃
      ProjectiveConicDirection c × NonzeroProjectiveScalar (p := p) where
  toFun v :=
    (normalizeProjectiveDirection hc v,
      ⟨normalizeProjectiveScalar hc v, normalizeProjectiveScalar_ne_zero hc v⟩)
  invFun := directionScalarVector
  left_inv v := by
    apply Subtype.ext
    exact scale_normalizeProjectiveDirection hc v
  right_inv q := by
    apply Prod.ext
    · exact normalize_directionScalarVector hc q
    · apply Subtype.ext
      exact scalar_directionScalarVector hc q

private theorem eight_ne_zero (hp2 : p ≠ 2) : (8 : ZMod p) ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  rw [show (8 : ZMod p) = 2 ^ 3 by norm_num]
  exact pow_ne_zero 3 h2

private theorem thirtyTwo_ne_zero (hp2 : p ≠ 2) : (32 : ZMod p) ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  rw [show (32 : ZMod p) = 2 ^ 5 by norm_num]
  exact pow_ne_zero 5 h2

/-- The thin Tunnell lattice has exactly `p+1` odd-prime neighbor directions. -/
theorem thinProjectiveNeighborDirections_card (hp2 : p ≠ 2) :
    (projectiveConicDirections (p := p) 8).card = p + 1 :=
  projectiveConicDirections_card hp2 (eight_ne_zero hp2)

/-- The thick Tunnell lattice has the same complete odd-prime neighbor aperture. -/
theorem thickProjectiveNeighborDirections_card (hp2 : p ≠ 2) :
    (projectiveConicDirections (p := p) 32).card = p + 1 :=
  projectiveConicDirections_card hp2 (thirtyTwo_ne_zero hp2)

#print axioms quadraticChar_sum_square_sub
#print axioms quadraticChar_sum_scaled_square_add
#print axioms projectiveConicDirections_card
#print axioms projectiveDirectionVector_isotropic
#print axioms projectiveConicDirection_fintype_card
#print axioms scale_normalizeProjectiveDirection
#print axioms nonzeroIsotropicVectorEquivDirectionScalar
#print axioms thinProjectiveNeighborDirections_card
#print axioms thickProjectiveNeighborDirections_card

end Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors

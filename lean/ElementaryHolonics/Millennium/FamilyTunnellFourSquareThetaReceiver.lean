import ElementaryHolonics.Millennium.FamilyTunnellHeckeThetaFactor

/-!
# Four addressed square streams retain their complete lattice population

The Hopf residue theta body is assembled from four unary square streams.  A
Cauchy coefficient must therefore be returned to the actual four-coordinate
lattice occurrence, rather than left as a nested sum of coefficient counts.

This file performs that return in two exact stages.  First, two unary streams
are identified with the existing residue-pair shell.  Second, two such pair
shells are glued across their reconstructed norm split.  The terminal theorem
identifies every coefficient of the fourfold product with the cardinality of
the complete ordered integer quadruple shell carrying the four declared
modulo-four residues.  No analytic convergence or representation-number
formula is used.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver

open Finset
open PowerSeries
open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellHeckeThetaFactor
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellQuaternionHopf
open Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus

abbrev IntegerQuadruple := (ℤ × ℤ) × (ℤ × ℤ)

/-- Two addressed unary square streams before the four-coordinate gluing. -/
def quarterPairTheta (r s : QuarterResidue) : PowerSeries ℤ :=
  quarterSquareTheta r * quarterSquareTheta s

/-- The ordinary coefficient of two square streams is the cardinality of the
complete residue-pair shell, with the norm split retained by the existing
`squareSplitEquivResiduePair`. -/
theorem coeff_quarterPairTheta (r s : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n (quarterPairTheta r s) =
      ((residuePairShell r s n).card : ℤ) := by
  rw [quarterPairTheta, PowerSeries.coeff_mul]
  simp only [coeff_quarterSquareTheta]
  have hcard :
      (squareSplitPopulation r s n).card =
        (residuePairShell r s n).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_congr (squareSplitEquivResiduePair r s n)
  rw [← hcard, squareSplitPopulation, Finset.card_sigma]
  push_cast
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [Finset.card_product]
  push_cast
  rfl

/-- The complete split population behind the product of two residue-pair
theta streams. -/
def pairPairSplitPopulation (r₀ r₁ r₂ r₃ : QuarterResidue) (n : ℕ) :
    Finset (Σ kl : ℕ × ℕ, (ℤ × ℤ) × (ℤ × ℤ)) :=
  (Finset.antidiagonal n).sigma fun kl =>
    residuePairShell r₀ r₁ kl.1 ×ˢ residuePairShell r₂ r₃ kl.2

/-- Four ordered integer coordinates with their individual modulo-four
addresses and one reconstructed total square norm. -/
def fourSquareResidueShell (r₀ r₁ r₂ r₃ : QuarterResidue) (n : ℕ) :
    Finset IntegerQuadruple :=
  ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
    ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ))).filter fun q =>
        q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = (n : ℤ) ∧
          (q.1.1 : ZMod 4) = r₀.val ∧
          (q.1.2 : ZMod 4) = r₁.val ∧
          (q.2.1 : ZMod 4) = r₂.val ∧
          (q.2.2 : ZMod 4) = r₃.val)

private theorem splitToQuad_mem
    {r₀ r₁ r₂ r₃ : QuarterResidue} {n : ℕ}
    {q : Σ kl : ℕ × ℕ, (ℤ × ℤ) × (ℤ × ℤ)}
    (hq : q ∈ pairPairSplitPopulation r₀ r₁ r₂ r₃ n) :
    q.2 ∈ fourSquareResidueShell r₀ r₁ r₂ r₃ n := by
  rcases Finset.mem_sigma.mp hq with ⟨hkl, hpairs⟩
  rcases Finset.mem_product.mp hpairs with ⟨hleft, hright⟩
  rcases Finset.mem_filter.mp hleft with
    ⟨hleftBox, hleftNorm, hleft₀, hleft₁⟩
  rcases Finset.mem_filter.mp hright with
    ⟨hrightBox, hrightNorm, hright₂, hright₃⟩
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨?_, ?_, hleft₀, hleft₁, hright₂, hright₃⟩
  · simp only [Finset.mem_product, Finset.mem_Icc] at hleftBox hrightBox
    simp only [Finset.mem_product, Finset.mem_Icc]
    rcases hleftBox with ⟨ha, hb⟩
    rcases hrightBox with ⟨hc, hd⟩
    have hk : q.1.1 ≤ n := by
      have := Finset.mem_antidiagonal.mp hkl
      omega
    have hl : q.1.2 ≤ n := by
      have := Finset.mem_antidiagonal.mp hkl
      omega
    have hkZ : (q.1.1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
    have hlZ : (q.1.2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hl
    exact
      ⟨⟨⟨le_trans (neg_le_neg hkZ) ha.1, le_trans ha.2 hkZ⟩,
          ⟨le_trans (neg_le_neg hkZ) hb.1, le_trans hb.2 hkZ⟩⟩,
        ⟨⟨le_trans (neg_le_neg hlZ) hc.1, le_trans hc.2 hlZ⟩,
          ⟨le_trans (neg_le_neg hlZ) hd.1, le_trans hd.2 hlZ⟩⟩⟩
  · have hsum := Finset.mem_antidiagonal.mp hkl
    calc
      q.2.1.1 ^ 2 + q.2.1.2 ^ 2 + q.2.2.1 ^ 2 + q.2.2.2 ^ 2 =
          (q.2.1.1 ^ 2 + q.2.1.2 ^ 2) +
            (q.2.2.1 ^ 2 + q.2.2.2 ^ 2) := by ring
      _ = (q.1.1 : ℤ) + (q.1.2 : ℤ) := by
        rw [hleftNorm, hrightNorm]
      _ = (n : ℤ) := by exact_mod_cast hsum

private theorem coordinate_square_sum_toNat_cast (q : ℤ × ℤ) :
    (((q.1 ^ 2 + q.2 ^ 2).toNat : ℕ) : ℤ) = q.1 ^ 2 + q.2 ^ 2 := by
  rw [Int.toNat_of_nonneg]
  positivity

private theorem first_coordinate_mem_pair_square_box (q : ℤ × ℤ) :
    q.1 ∈ Finset.Icc
      (-(((q.1 ^ 2 + q.2 ^ 2).toNat : ℕ) : ℤ))
      (((q.1 ^ 2 + q.2 ^ 2).toNat : ℕ) : ℤ) := by
  rw [Finset.mem_Icc, coordinate_square_sum_toNat_cast]
  constructor
  · by_cases ha : 0 ≤ q.1
    · nlinarith [sq_nonneg q.1, sq_nonneg q.2]
    · have ha' : q.1 ≤ -1 := by omega
      have hprod : 0 ≤ (-q.1) * (-q.1 - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg q.2]
  · by_cases ha : q.1 ≤ 0
    · nlinarith [sq_nonneg q.1, sq_nonneg q.2]
    · have ha' : 1 ≤ q.1 := by omega
      have hprod : 0 ≤ q.1 * (q.1 - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith [sq_nonneg q.2]

private theorem second_coordinate_mem_pair_square_box (q : ℤ × ℤ) :
    q.2 ∈ Finset.Icc
      (-(((q.1 ^ 2 + q.2 ^ 2).toNat : ℕ) : ℤ))
      (((q.1 ^ 2 + q.2 ^ 2).toNat : ℕ) : ℤ) := by
  simpa [add_comm] using first_coordinate_mem_pair_square_box (q.2, q.1)

private theorem quadToSplit_mem
    {r₀ r₁ r₂ r₃ : QuarterResidue} {n : ℕ}
    {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell r₀ r₁ r₂ r₃ n) :
    (Sigma.mk
        ((q.1.1 ^ 2 + q.1.2 ^ 2).toNat,
          (q.2.1 ^ 2 + q.2.2 ^ 2).toNat) q) ∈
      pairPairSplitPopulation r₀ r₁ r₂ r₃ n := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  rcases Finset.mem_product.mp hqBox with ⟨_hleftBox, _hrightBox⟩
  rw [pairPairSplitPopulation, Finset.mem_sigma]
  constructor
  · rw [Finset.mem_antidiagonal]
    have hcast :
        ((((q.1.1 ^ 2 + q.1.2 ^ 2).toNat +
            (q.2.1 ^ 2 + q.2.2 ^ 2).toNat : ℕ) : ℤ)) = (n : ℤ) := by
      push_cast
      rw [coordinate_square_sum_toNat_cast,
        coordinate_square_sum_toNat_cast]
      simpa [add_assoc] using hnorm
    exact_mod_cast hcast
  · rw [Finset.mem_product]
    constructor
    · rw [residuePairShell, Finset.mem_filter]
      refine ⟨?_, coordinate_square_sum_toNat_cast q.1 |>.symm, hq₀, hq₁⟩
      rw [Finset.mem_product]
      exact ⟨first_coordinate_mem_pair_square_box q.1,
        second_coordinate_mem_pair_square_box q.1⟩
    · rw [residuePairShell, Finset.mem_filter]
      refine ⟨?_, coordinate_square_sum_toNat_cast q.2 |>.symm, hq₂, hq₃⟩
      rw [Finset.mem_product]
      exact ⟨first_coordinate_mem_pair_square_box q.2,
        second_coordinate_mem_pair_square_box q.2⟩

/-- The pair norm split is reconstructed from the four integer coordinates. -/
def pairPairSplitEquivFourSquareResidue
    (r₀ r₁ r₂ r₃ : QuarterResidue) (n : ℕ) :
    {q // q ∈ pairPairSplitPopulation r₀ r₁ r₂ r₃ n} ≃
      {q // q ∈ fourSquareResidueShell r₀ r₁ r₂ r₃ n} where
  toFun q := ⟨q.1.2, splitToQuad_mem q.2⟩
  invFun q := ⟨Sigma.mk
      ((q.1.1.1 ^ 2 + q.1.1.2 ^ 2).toNat,
        (q.1.2.1 ^ 2 + q.1.2.2 ^ 2).toNat) q.1,
      quadToSplit_mem q.2⟩
  left_inv q := by
    apply Subtype.ext
    rcases Finset.mem_sigma.mp q.2 with ⟨hkl, hpairs⟩
    rcases Finset.mem_product.mp hpairs with ⟨hleft, hright⟩
    rcases Finset.mem_filter.mp hleft with
      ⟨hleftBox, hleftNorm, hleft₀, hleft₁⟩
    rcases Finset.mem_filter.mp hright with
      ⟨hrightBox, hrightNorm, hright₂, hright₃⟩
    apply Sigma.ext
    · apply Prod.ext
      · have h :
            (((q.1.2.1.1 ^ 2 + q.1.2.1.2 ^ 2).toNat : ℕ) : ℤ) =
              (q.1.1.1 : ℤ) := by
          rw [coordinate_square_sum_toNat_cast, hleftNorm]
        exact_mod_cast h
      · have h :
            (((q.1.2.2.1 ^ 2 + q.1.2.2.2 ^ 2).toNat : ℕ) : ℤ) =
              (q.1.1.2 : ℤ) := by
          rw [coordinate_square_sum_toNat_cast, hrightNorm]
        exact_mod_cast h
    · rfl
  right_inv q := by
    apply Subtype.ext
    rfl

/-- Multiplying the two pair streams retains the complete split population. -/
theorem coeff_four_pair_product_eq_split_card
    (r₀ r₁ r₂ r₃ : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n
        (quarterPairTheta r₀ r₁ * quarterPairTheta r₂ r₃) =
      ((pairPairSplitPopulation r₀ r₁ r₂ r₃ n).card : ℤ) := by
  rw [PowerSeries.coeff_mul]
  simp only [coeff_quarterPairTheta]
  rw [pairPairSplitPopulation, Finset.card_sigma]
  push_cast
  apply Finset.sum_congr rfl
  intro kl hkl
  rw [Finset.card_product]
  push_cast
  rfl

/-- **FOURFOLD COEFFICIENT RECONSTRUCTION.**  Every coefficient of four
addressed square streams is exactly the complete ordered lattice population
with those residues. -/
theorem coeff_fourQuarterSquareTheta_eq_residueShell_card
    (r₀ r₁ r₂ r₃ : QuarterResidue) (n : ℕ) :
    PowerSeries.coeff n
        ((quarterSquareTheta r₀ * quarterSquareTheta r₁) *
          (quarterSquareTheta r₂ * quarterSquareTheta r₃)) =
      ((fourSquareResidueShell r₀ r₁ r₂ r₃ n).card : ℤ) := by
  rw [← quarterPairTheta, ← quarterPairTheta,
    coeff_four_pair_product_eq_split_card]
  have hcard :
      (pairPairSplitPopulation r₀ r₁ r₂ r₃ n).card =
        (fourSquareResidueShell r₀ r₁ r₂ r₃ n).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr
      (pairPairSplitEquivFourSquareResidue r₀ r₁ r₂ r₃ n)
  exact_mod_cast hcard

/-! ## The Hopf residue polynomial opened back into its occurrence population -/

/-- The folded residue `0,1,2` returned as a legal quarter-residue address. -/
def foldAsQuarterResidue (r : QuarterResidue) : QuarterResidue :=
  ⟨(foldQuarterResidue r).val, by
    have := (foldQuarterResidue r).isLt
    omega⟩

def foldedQuarterVariable {R : Type*} [CommRing R]
    (a b c : R) (r : QuarterResidue) : R :=
  if foldQuarterResidue r = 0 then a
  else if foldQuarterResidue r = 1 then b
  else c

def foldedCoordinateProduct {R : Type*} [CommRing R]
    (a b c : R) (q : ResidueQuaternion) : R :=
  foldedQuarterVariable a b c q.1 *
    foldedQuarterVariable a b c q.2.1 *
    foldedQuarterVariable a b c q.2.2.1 *
    foldedQuarterVariable a b c q.2.2.2

private def foldCount (i : FoldedQuarterResidue)
    (q : ResidueQuaternion) : ℕ :=
  (if foldQuarterResidue q.1 = i then 1 else 0) +
    (if foldQuarterResidue q.2.1 = i then 1 else 0) +
    (if foldQuarterResidue q.2.2.1 = i then 1 else 0) +
    (if foldQuarterResidue q.2.2.2 = i then 1 else 0)

private theorem foldCount_eq_foldedMultiplicity
    (i : FoldedQuarterResidue) (q : ResidueQuaternion) :
    foldCount i q = (foldedMultiplicity i q).val := by
  rfl

private theorem one_folded_coordinate_monomial {R : Type*} [CommRing R]
    (a b c : R) (r : QuarterResidue) :
    a ^ (if foldQuarterResidue r = 0 then 1 else 0) *
        b ^ (if foldQuarterResidue r = 1 then 1 else 0) *
        c ^ (if foldQuarterResidue r = 2 then 1 else 0) =
      foldedQuarterVariable a b c r := by
  fin_cases r <;>
    simp [foldQuarterResidue, foldedQuarterVariable]

/-- The exponent-count chart and the ordered coordinate chart are the same
monomial.  This is the algebraic reordering used when the residue polynomial
is reopened into its four addressed coordinates. -/
theorem foldedMonomial_eq_coordinateProduct {R : Type*} [CommRing R]
    (a b c : R) (q : ResidueQuaternion) :
    a ^ (foldedMultiplicity 0 q).val *
        b ^ (foldedMultiplicity 1 q).val *
        c ^ (foldedMultiplicity 2 q).val =
      foldedCoordinateProduct a b c q := by
  rw [← foldCount_eq_foldedMultiplicity,
    ← foldCount_eq_foldedMultiplicity,
    ← foldCount_eq_foldedMultiplicity]
  unfold foldCount foldedCoordinateProduct
  simp only [pow_add]
  have h₀ := one_folded_coordinate_monomial a b c q.1
  have h₁ := one_folded_coordinate_monomial a b c q.2.1
  have h₂ := one_folded_coordinate_monomial a b c q.2.2.1
  have h₃ := one_folded_coordinate_monomial a b c q.2.2.2
  calc
    _ =
        (a ^ (if foldQuarterResidue q.1 = 0 then 1 else 0) *
          b ^ (if foldQuarterResidue q.1 = 1 then 1 else 0) *
          c ^ (if foldQuarterResidue q.1 = 2 then 1 else 0)) *
        (a ^ (if foldQuarterResidue q.2.1 = 0 then 1 else 0) *
          b ^ (if foldQuarterResidue q.2.1 = 1 then 1 else 0) *
          c ^ (if foldQuarterResidue q.2.1 = 2 then 1 else 0)) *
        (a ^ (if foldQuarterResidue q.2.2.1 = 0 then 1 else 0) *
          b ^ (if foldQuarterResidue q.2.2.1 = 1 then 1 else 0) *
          c ^ (if foldQuarterResidue q.2.2.1 = 2 then 1 else 0)) *
        (a ^ (if foldQuarterResidue q.2.2.2 = 0 then 1 else 0) *
          b ^ (if foldQuarterResidue q.2.2.2 = 1 then 1 else 0) *
          c ^ (if foldQuarterResidue q.2.2.2 = 2 then 1 else 0)) := by ring
    _ = _ := by rw [h₀, h₁, h₂, h₃]

/-- Exact finite residue addresses admitted by the Hopf winding seam. -/
def admissibleHopfResidues : Finset ResidueQuaternion :=
  Finset.univ.filter fun q => residueNormOdd q ∧ residueWindingCloses q

/-- The four square streams carried by one admitted residue address. -/
def foldedResidueThetaTerm (q : ResidueQuaternion) : PowerSeries ℤ :=
  (quarterSquareTheta (foldAsQuarterResidue q.1) *
      quarterSquareTheta (foldAsQuarterResidue q.2.1)) *
    (quarterSquareTheta (foldAsQuarterResidue q.2.2.1) *
      quarterSquareTheta (foldAsQuarterResidue q.2.2.2))

private theorem quarterSquareTheta_foldAsQuarterResidue
    (r : QuarterResidue) :
    quarterSquareTheta (foldAsQuarterResidue r) =
      foldedQuarterVariable (quarterSquareTheta 0)
        (quarterSquareTheta 1) (quarterSquareTheta 2) r := by
  fin_cases r <;>
    simp [foldAsQuarterResidue, foldQuarterResidue, foldedQuarterVariable]

theorem foldedResidueThetaTerm_eq_coordinateProduct
    (q : ResidueQuaternion) :
    foldedResidueThetaTerm q =
      foldedCoordinateProduct (quarterSquareTheta 0)
        (quarterSquareTheta 1) (quarterSquareTheta 2) q := by
  unfold foldedResidueThetaTerm foldedCoordinateProduct
  rw [quarterSquareTheta_foldAsQuarterResidue,
    quarterSquareTheta_foldAsQuarterResidue,
    quarterSquareTheta_foldAsQuarterResidue,
    quarterSquareTheta_foldAsQuarterResidue]
  ring

private theorem residueEvaluate_hopfSource_eq_univ_sum
    {R : Type*} [CommRing R] (a b c : R) :
    residueEvaluate a b c hopfSourceResiduePolynomial =
      ∑ q : ResidueQuaternion,
        if residueNormOdd q ∧ residueWindingCloses q then
          foldedCoordinateProduct a b c q else 0 := by
  unfold residueEvaluate hopfSourceResiduePolynomial
  calc
    (∑ e : ResidueExponent,
        ((∑ q : ResidueQuaternion,
          if residueNormOdd q ∧ residueWindingCloses q ∧
              foldedResidueExponent q = e then 1 else 0) : ℤ) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val) =
      ∑ e : ResidueExponent, ∑ q : ResidueQuaternion,
        ((if residueNormOdd q ∧ residueWindingCloses q ∧
              foldedResidueExponent q = e then 1 else 0 : ℤ) : R) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val := by
            apply Finset.sum_congr rfl
            intro e he
            push_cast
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ q : ResidueQuaternion, ∑ e : ResidueExponent,
        ((if residueNormOdd q ∧ residueWindingCloses q ∧
              foldedResidueExponent q = e then 1 else 0 : ℤ) : R) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val := by
            rw [Finset.sum_comm]
    _ = ∑ q : ResidueQuaternion,
        if residueNormOdd q ∧ residueWindingCloses q then
          foldedCoordinateProduct a b c q else 0 := by
      apply Finset.sum_congr rfl
      intro q hqUniv
      by_cases hq : residueNormOdd q ∧ residueWindingCloses q
      · rw [if_pos hq]
        rw [Finset.sum_eq_single (foldedResidueExponent q)]
        · simp only [hq, true_and, if_pos, Int.cast_one, one_mul]
          exact foldedMonomial_eq_coordinateProduct a b c q
        · intro e he hne
          have hnot : ¬(foldedResidueExponent q = e) := by
            exact fun h => hne h.symm
          simp [hnot]
        · simp
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro e he
        have hcondition :
            ¬(residueNormOdd q ∧ residueWindingCloses q ∧
              foldedResidueExponent q = e) := by
          intro h
          exact hq ⟨h.1, h.2.1⟩
        simp [hcondition]

/-- **THE RESIDUE POLYNOMIAL REOPENS INTO ITS COMPLETE HOPF RESIDUE
POPULATION.**  No coefficient multiplicity is left anonymous: each summand is
one addressed four-coordinate residue cell. -/
theorem hopfResidueTheta_eq_sum_admissibleResidueTerms :
    hopfResidueTheta =
      ∑ q ∈ admissibleHopfResidues, foldedResidueThetaTerm q := by
  unfold hopfResidueTheta
  rw [residueEvaluate_hopfSource_eq_univ_sum]
  rw [admissibleHopfResidues, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hadmitted : residueNormOdd q ∧ residueWindingCloses q
  · rw [if_pos hadmitted, if_pos hadmitted,
      foldedResidueThetaTerm_eq_coordinateProduct]
  · rw [if_neg hadmitted, if_neg hadmitted]

/-- Every Hopf residue-theta coefficient is the sum of the complete lattice
populations in its admitted residue cells. -/
theorem coeff_hopfResidueTheta_eq_sum_residueShell_card (n : ℕ) :
    PowerSeries.coeff n hopfResidueTheta =
      ∑ q ∈ admissibleHopfResidues,
        ((fourSquareResidueShell
          (foldAsQuarterResidue q.1)
          (foldAsQuarterResidue q.2.1)
          (foldAsQuarterResidue q.2.2.1)
          (foldAsQuarterResidue q.2.2.2) n).card : ℤ) := by
  rw [hopfResidueTheta_eq_sum_admissibleResidueTerms, map_sum]
  apply Finset.sum_congr rfl
  intro q hq
  unfold foldedResidueThetaTerm
  exact coeff_fourQuarterSquareTheta_eq_residueShell_card
    (foldAsQuarterResidue q.1)
    (foldAsQuarterResidue q.2.1)
    (foldAsQuarterResidue q.2.2.1)
    (foldAsQuarterResidue q.2.2.2) n

/-! ## Reopening the folded `1/3` orientation -/

/-- A residue-`3` coordinate was represented by the residue-`1` square stream.
Negation returns its deleted orientation; the other residues are unchanged. -/
def unfoldQuarterCoordinate (r : QuarterResidue) (x : ℤ) : ℤ :=
  if r = 3 then -x else x

theorem unfoldQuarterCoordinate_involutive (r : QuarterResidue) :
    Function.Involutive (unfoldQuarterCoordinate r) := by
  intro x
  by_cases hr : r = 3 <;> simp [unfoldQuarterCoordinate, hr]

theorem unfoldQuarterCoordinate_sq (r : QuarterResidue) (x : ℤ) :
    unfoldQuarterCoordinate r x ^ 2 = x ^ 2 := by
  by_cases hr : r = 3 <;> simp [unfoldQuarterCoordinate, hr]

private theorem unfoldQuarterCoordinate_mem_box
    (r : QuarterResidue) {n : ℕ} {x : ℤ}
    (hx : x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ)) :
    unfoldQuarterCoordinate r x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  by_cases hr : r = 3
  · simp only [unfoldQuarterCoordinate, hr, if_pos, Finset.mem_Icc] at hx ⊢
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · simpa [unfoldQuarterCoordinate, hr] using hx

/-- The orientation return converts the folded stream address back to the
original residue, including the `1 ↔ 3` negation. -/
theorem unfoldQuarterCoordinate_residue
    (r : QuarterResidue) {x : ℤ}
    (hx : (x : ZMod 4) = (foldAsQuarterResidue r).val) :
    (unfoldQuarterCoordinate r x : ZMod 4) = r.val := by
  by_cases hr : r = 3
  · subst r
    simp only [unfoldQuarterCoordinate, if_pos, foldAsQuarterResidue,
      foldQuarterResidue, Fin.isValue, Int.cast_neg]
    calc
      -(x : ZMod 4) = -(1 : ZMod 4) := congrArg Neg.neg hx
      _ = (3 : ZMod 4) := by decide
  · have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by
      fin_cases r <;> simp_all
    rcases hcases with rfl | rfl | rfl <;>
      simpa [unfoldQuarterCoordinate, foldAsQuarterResidue,
        foldQuarterResidue] using hx

private theorem unfoldQuarterCoordinate_folded_residue
    (r : QuarterResidue) {x : ℤ}
    (hx : (x : ZMod 4) = r.val) :
    (unfoldQuarterCoordinate r x : ZMod 4) =
      (foldAsQuarterResidue r).val := by
  by_cases hr : r = 3
  · subst r
    simp only [unfoldQuarterCoordinate, if_pos, foldAsQuarterResidue,
      foldQuarterResidue, Fin.isValue, Int.cast_neg]
    calc
      -(x : ZMod 4) = -(3 : ZMod 4) := congrArg Neg.neg hx
      _ = (1 : ZMod 4) := by decide
  · have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by
      fin_cases r <;> simp_all
    rcases hcases with rfl | rfl | rfl <;>
      simpa [unfoldQuarterCoordinate, foldAsQuarterResidue,
        foldQuarterResidue] using hx

def unfoldResidueQuad (r : ResidueQuaternion)
    (q : IntegerQuadruple) : IntegerQuadruple :=
  ((unfoldQuarterCoordinate r.1 q.1.1,
      unfoldQuarterCoordinate r.2.1 q.1.2),
    (unfoldQuarterCoordinate r.2.2.1 q.2.1,
      unfoldQuarterCoordinate r.2.2.2 q.2.2))

theorem unfoldResidueQuad_involutive (r : ResidueQuaternion) :
    Function.Involutive (unfoldResidueQuad r) := by
  intro q
  apply Prod.ext
  · apply Prod.ext
    · exact unfoldQuarterCoordinate_involutive r.1 q.1.1
    · exact unfoldQuarterCoordinate_involutive r.2.1 q.1.2
  · apply Prod.ext
    · exact unfoldQuarterCoordinate_involutive r.2.2.1 q.2.1
    · exact unfoldQuarterCoordinate_involutive r.2.2.2 q.2.2

private theorem unfoldResidueQuad_mem_exactShell
    {r : ResidueQuaternion} {n : ℕ} {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell
      (foldAsQuarterResidue r.1)
      (foldAsQuarterResidue r.2.1)
      (foldAsQuarterResidue r.2.2.1)
      (foldAsQuarterResidue r.2.2.2) n) :
    unfoldResidueQuad r q ∈
      fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  rcases Finset.mem_product.mp hqBox with ⟨hleftBox, hrightBox⟩
  rcases Finset.mem_product.mp hleftBox with ⟨haBox, hbBox⟩
  rcases Finset.mem_product.mp hrightBox with ⟨hcBox, hdBox⟩
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_product]
    exact ⟨⟨unfoldQuarterCoordinate_mem_box r.1 haBox,
        unfoldQuarterCoordinate_mem_box r.2.1 hbBox⟩,
      ⟨unfoldQuarterCoordinate_mem_box r.2.2.1 hcBox,
        unfoldQuarterCoordinate_mem_box r.2.2.2 hdBox⟩⟩
  · unfold unfoldResidueQuad
    simp only [unfoldQuarterCoordinate_sq]
    exact hnorm
  · exact unfoldQuarterCoordinate_residue r.1 hq₀
  · exact unfoldQuarterCoordinate_residue r.2.1 hq₁
  · exact unfoldQuarterCoordinate_residue r.2.2.1 hq₂
  · exact unfoldQuarterCoordinate_residue r.2.2.2 hq₃

private theorem unfoldResidueQuad_mem_foldedShell
    {r : ResidueQuaternion} {n : ℕ} {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n) :
    unfoldResidueQuad r q ∈ fourSquareResidueShell
      (foldAsQuarterResidue r.1)
      (foldAsQuarterResidue r.2.1)
      (foldAsQuarterResidue r.2.2.1)
      (foldAsQuarterResidue r.2.2.2) n := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  rcases Finset.mem_product.mp hqBox with ⟨hleftBox, hrightBox⟩
  rcases Finset.mem_product.mp hleftBox with ⟨haBox, hbBox⟩
  rcases Finset.mem_product.mp hrightBox with ⟨hcBox, hdBox⟩
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_product]
    exact ⟨⟨unfoldQuarterCoordinate_mem_box r.1 haBox,
        unfoldQuarterCoordinate_mem_box r.2.1 hbBox⟩,
      ⟨unfoldQuarterCoordinate_mem_box r.2.2.1 hcBox,
        unfoldQuarterCoordinate_mem_box r.2.2.2 hdBox⟩⟩
  · unfold unfoldResidueQuad
    simp only [unfoldQuarterCoordinate_sq]
    exact hnorm
  · exact unfoldQuarterCoordinate_folded_residue r.1 hq₀
  · exact unfoldQuarterCoordinate_folded_residue r.2.1 hq₁
  · exact unfoldQuarterCoordinate_folded_residue r.2.2.1 hq₂
  · exact unfoldQuarterCoordinate_folded_residue r.2.2.2 hq₃

/-- Every folded residue shell is equivalent to the original oriented shell;
the complete reconstruction fibre is the coordinatewise `1/3` negation. -/
def foldedResidueShellEquivExact (r : ResidueQuaternion) (n : ℕ) :
    {q // q ∈ fourSquareResidueShell
      (foldAsQuarterResidue r.1)
      (foldAsQuarterResidue r.2.1)
      (foldAsQuarterResidue r.2.2.1)
      (foldAsQuarterResidue r.2.2.2) n} ≃
    {q // q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n} where
  toFun q := ⟨unfoldResidueQuad r q.1,
    unfoldResidueQuad_mem_exactShell q.2⟩
  invFun q := ⟨unfoldResidueQuad r q.1,
    unfoldResidueQuad_mem_foldedShell q.2⟩
  left_inv q := by
    apply Subtype.ext
    exact unfoldResidueQuad_involutive r q.1
  right_inv q := by
    apply Subtype.ext
    exact unfoldResidueQuad_involutive r q.1

theorem foldedResidueShell_card_eq_exact
    (r : ResidueQuaternion) (n : ℕ) :
    (fourSquareResidueShell
      (foldAsQuarterResidue r.1)
      (foldAsQuarterResidue r.2.1)
      (foldAsQuarterResidue r.2.2.1)
      (foldAsQuarterResidue r.2.2.2) n).card =
    (fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n).card := by
  simpa only [Fintype.card_coe] using Fintype.card_congr
    (foldedResidueShellEquivExact r n)

/-- The Hopf coefficient can therefore be written using the original four
residue orientations, with no folded coordinate left in the terminal carrier. -/
theorem coeff_hopfResidueTheta_eq_sum_exactResidueShell_card (n : ℕ) :
    PowerSeries.coeff n hopfResidueTheta =
      ∑ r ∈ admissibleHopfResidues,
        ((fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ) := by
  rw [coeff_hopfResidueTheta_eq_sum_residueShell_card]
  apply Finset.sum_congr rfl
  intro r hr
  exact_mod_cast foldedResidueShell_card_eq_exact r n

/-- The exact tagged population behind the Hopf coefficient.  The residue tag
is retained because it is the reconstruction address of every coordinate. -/
def exactHopfResidueCarrier (n : ℕ) :
    Finset (Σ r : ResidueQuaternion, IntegerQuadruple) :=
  admissibleHopfResidues.sigma fun r =>
    fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n

theorem coeff_hopfResidueTheta_eq_exactCarrier_card (n : ℕ) :
    PowerSeries.coeff n hopfResidueTheta =
      ((exactHopfResidueCarrier n).card : ℤ) := by
  rw [coeff_hopfResidueTheta_eq_sum_exactResidueShell_card,
    exactHopfResidueCarrier, Finset.card_sigma]
  push_cast
  rfl

/-! ## The tagged residue carrier is the finite Hamilton source -/

/-- The canonical residue address of one integer coordinate. -/
def quarterResidueOfInt (x : ℤ) : QuarterResidue :=
  ⟨(x : ZMod 4).val, ZMod.val_lt (x : ZMod 4)⟩

@[simp] theorem quarterResidueOfInt_cast (x : ℤ) :
    ((quarterResidueOfInt x).val : ZMod 4) = (x : ZMod 4) := by
  exact ZMod.natCast_zmod_val (x : ZMod 4)

def residueAddressOfHamilton (q : HamiltonInt) : ResidueQuaternion :=
  (quarterResidueOfInt q.re, quarterResidueOfInt q.imI,
    quarterResidueOfInt q.imJ, quarterResidueOfInt q.imK)

def coordinatesOfHamilton (q : HamiltonInt) : IntegerQuadruple :=
  ((q.re, q.imI), (q.imJ, q.imK))

@[simp] theorem coordinatesToHamilton_coordinatesOfHamilton (q : HamiltonInt) :
    coordinatesToHamilton (coordinatesOfHamilton q) = q := by
  apply Quaternion.ext <;> rfl

@[simp] theorem coordinatesOfHamilton_coordinatesToHamilton
    (q : IntegerQuadruple) :
    coordinatesOfHamilton (coordinatesToHamilton q) = q := by
  rfl

private def modFourToTwo : ZMod 4 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 4) (ZMod 2)

theorem residueNormOdd_of_exactShell
    {r : ResidueQuaternion} {n : ℕ} (hn : Odd n)
    {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n) :
    residueNormOdd r := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  have hq₀two := congrArg modFourToTwo hq₀
  have hq₁two := congrArg modFourToTwo hq₁
  have hq₂two := congrArg modFourToTwo hq₂
  have hq₃two := congrArg modFourToTwo hq₃
  have hq₀two' : (q.1.1 : ZMod 2) = (r.1.val : ZMod 2) := by
    simpa [modFourToTwo, ZMod.castHom_apply] using hq₀two
  have hq₁two' : (q.1.2 : ZMod 2) = (r.2.1.val : ZMod 2) := by
    simpa [modFourToTwo, ZMod.castHom_apply] using hq₁two
  have hq₂two' : (q.2.1 : ZMod 2) = (r.2.2.1.val : ZMod 2) := by
    simpa [modFourToTwo, ZMod.castHom_apply] using hq₂two
  have hq₃two' : (q.2.2 : ZMod 2) = (r.2.2.2.val : ZMod 2) := by
    simpa [modFourToTwo, ZMod.castHom_apply] using hq₃two
  have hnormTwo := congrArg (fun z : ℤ => (z : ZMod 2)) hnorm
  push_cast at hnormTwo
  rw [hq₀two', hq₁two', hq₂two', hq₃two'] at hnormTwo
  rcases hn with ⟨k, rfl⟩
  have hresidue :
      (r.1.val : ZMod 2) ^ 2 + (r.2.1.val : ZMod 2) ^ 2 +
          (r.2.2.1.val : ZMod 2) ^ 2 + (r.2.2.2.val : ZMod 2) ^ 2 = 1 := by
    simpa [show (2 : ZMod 2) = 0 by decide, add_assoc] using hnormTwo
  have hresidueNatCast :
      (((r.1.val ^ 2 + r.2.1.val ^ 2 + r.2.2.1.val ^ 2 +
        r.2.2.2.val ^ 2 : ℕ) : ZMod 2)) = 1 := by
    push_cast
    exact hresidue
  unfold residueNormOdd
  have hval := congrArg ZMod.val hresidueNatCast
  change (r.1.val ^ 2 + r.2.1.val ^ 2 + r.2.2.1.val ^ 2 +
    r.2.2.2.val ^ 2) % 2 = 1
  rw [← ZMod.val_natCast]
  simpa only [ZMod.val_one] using hval

private theorem residueWindingCloses_of_source
    {q : HamiltonInt}
    (hdiv : (4 : ℤ) ∣ hopfWindingDifference q) :
    residueWindingCloses (residueAddressOfHamilton q) := by
  unfold residueWindingCloses residueWindingDifference
  simp only [residueAddressOfHamilton, quarterResidueOfInt_cast]
  have hzero : (hopfWindingDifference q : ZMod 4) = 0 := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (hopfWindingDifference q) 4).2 hdiv
  simpa [hopfWindingDifference, hopfTransverseJ,
    hopfTransverseK] using hzero

private theorem sourceCoordinates_mem_exactShell
    {p : ℕ} (hp : 0 < p) {q : HamiltonInt}
    (hq : q ∈ firstHopfSourcePopulation p) :
    coordinatesOfHamilton q ∈ fourSquareResidueShell
      (residueAddressOfHamilton q).1
      (residueAddressOfHamilton q).2.1
      (residueAddressOfHamilton q).2.2.1
      (residueAddressOfHamilton q).2.2.2 p := by
  have hsource := (mem_firstHopfSourcePopulation_iff hp q).mp hq
  have hbox := mem_hamiltonBox_of_norm hp q hsource.1
  have hcoordinates := (mem_hamiltonBox_iff p q).mp hbox
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [coordinatesOfHamilton, Finset.mem_product]
    exact ⟨⟨hcoordinates.1, hcoordinates.2.1⟩,
      ⟨hcoordinates.2.2.1, hcoordinates.2.2.2⟩⟩
  · rw [Quaternion.normSq_def'] at hsource
    exact hsource.1
  · exact (quarterResidueOfInt_cast q.re).symm
  · exact (quarterResidueOfInt_cast q.imI).symm
  · exact (quarterResidueOfInt_cast q.imJ).symm
  · exact (quarterResidueOfInt_cast q.imK).symm

private theorem residueAddress_mem_admissible
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : HamiltonInt}
    (hq : q ∈ firstHopfSourcePopulation p) :
    residueAddressOfHamilton q ∈ admissibleHopfResidues := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hsource := (mem_firstHopfSourcePopulation_iff hp q).mp hq
  rw [admissibleHopfResidues, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, residueWindingCloses_of_source hsource.2⟩
  exact residueNormOdd_of_exactShell
    ((Fact.out : p.Prime).odd_of_ne_two hp2)
    (sourceCoordinates_mem_exactShell hp hq)

private theorem exactShell_winding_divides
    {r : ResidueQuaternion} {p : ℕ} {q : IntegerQuadruple}
    (hr : residueWindingCloses r)
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 p) :
    (4 : ℤ) ∣ hopfWindingDifference (coordinatesToHamilton q) := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  have hzeroResidue :
      (hopfWindingDifference (coordinatesToHamilton q) : ZMod 4) = 0 := by
    unfold residueWindingCloses residueWindingDifference at hr
    unfold hopfWindingDifference hopfTransverseJ hopfTransverseK
    simp only [coordinatesToHamilton]
    push_cast
    rw [hq₀, hq₁, hq₂, hq₃]
    exact hr
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd
    (hopfWindingDifference (coordinatesToHamilton q)) 4).mp hzeroResidue

private theorem exactCarrierCoordinates_mem_source
    {p : ℕ} [Fact p.Prime]
    {r : ResidueQuaternion} {q : IntegerQuadruple}
    (hr : r ∈ admissibleHopfResidues)
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 p) :
    coordinatesToHamilton q ∈ firstHopfSourcePopulation p := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  rw [mem_firstHopfSourcePopulation_iff hp]
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  constructor
  · rw [Quaternion.normSq_def']
    exact hnorm
  · exact exactShell_winding_divides
      (Finset.mem_filter.mp hr).2.2 hq

private theorem quarterResidueOfInt_eq_of_cast
    {x : ℤ} {r : QuarterResidue}
    (h : (x : ZMod 4) = r.val) : quarterResidueOfInt x = r := by
  apply Fin.ext
  have hval := congrArg ZMod.val h
  simpa [quarterResidueOfInt, ZMod.val_natCast_of_lt r.isLt] using hval

theorem residueAddress_coordinatesToHamilton
    {r : ResidueQuaternion} {p : ℕ} {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 p) :
    residueAddressOfHamilton (coordinatesToHamilton q) = r := by
  rcases Finset.mem_filter.mp hq with
    ⟨hqBox, hnorm, hq₀, hq₁, hq₂, hq₃⟩
  apply Prod.ext
  · exact quarterResidueOfInt_eq_of_cast hq₀
  · apply Prod.ext
    · exact quarterResidueOfInt_eq_of_cast hq₁
    · apply Prod.ext
      · exact quarterResidueOfInt_eq_of_cast hq₂
      · exact quarterResidueOfInt_eq_of_cast hq₃

/-- **THE HOPF THETA COEFFICIENT CARRIER IS THE ACTUAL FINITE HAMILTON
SOURCE.**  The forward map records the four residue addresses.  The inverse
reconstructs the quaternion, and both composites are identities because the
residue tag is determined by the integer coordinates. -/
def firstHopfSourceEquivExactResidueCarrier
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    {q // q ∈ firstHopfSourcePopulation p} ≃
      {q // q ∈ exactHopfResidueCarrier p} where
  toFun q := ⟨Sigma.mk (residueAddressOfHamilton q.1)
      (coordinatesOfHamilton q.1), by
    rw [exactHopfResidueCarrier, Finset.mem_sigma]
    exact ⟨residueAddress_mem_admissible hp2 q.2,
      sourceCoordinates_mem_exactShell (Fact.out : p.Prime).pos q.2⟩⟩
  invFun q := ⟨coordinatesToHamilton q.1.2, by
    rcases Finset.mem_sigma.mp q.2 with ⟨hr, hcoordinates⟩
    exact exactCarrierCoordinates_mem_source hr hcoordinates⟩
  left_inv q := by
    apply Subtype.ext
    exact coordinatesToHamilton_coordinatesOfHamilton q.1
  right_inv q := by
    apply Subtype.ext
    rcases Finset.mem_sigma.mp q.2 with ⟨hr, hcoordinates⟩
    apply Sigma.ext
    · exact residueAddress_coordinatesToHamilton hcoordinates
    · simp

/-- At every odd prime the Hopf residue-theta coefficient is exactly the
cardinality of the complete integral norm-`p` source population. -/
theorem coeff_hopfResidueTheta_eq_firstHopfSourcePopulation_card
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    PowerSeries.coeff p hopfResidueTheta =
      ((firstHopfSourcePopulation p).card : ℤ) := by
  rw [coeff_hopfResidueTheta_eq_exactCarrier_card]
  have hcard :
      (firstHopfSourcePopulation p).card =
        (exactHopfResidueCarrier p).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr
      (firstHopfSourceEquivExactResidueCarrier p hp2)
  exact_mod_cast hcard.symm


#print axioms coeff_quarterPairTheta
#print axioms pairPairSplitEquivFourSquareResidue
#print axioms coeff_fourQuarterSquareTheta_eq_residueShell_card
#print axioms foldedMonomial_eq_coordinateProduct
#print axioms hopfResidueTheta_eq_sum_admissibleResidueTerms
#print axioms coeff_hopfResidueTheta_eq_sum_residueShell_card
#print axioms firstHopfSourceEquivExactResidueCarrier
#print axioms coeff_hopfResidueTheta_eq_firstHopfSourcePopulation_card

end Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver

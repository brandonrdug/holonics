import ElementaryHolonics.Mathematics.JacobiUnitSpecialization
import ElementaryHolonics.Mathematics.JacobiFiniteDiagonalReceiver
import ElementaryHolonics.Millennium.FamilyTunnellHopfThetaLift

/-!
# The Jacobi unit receiver returns the addressed square populations

This is the finite occurrence bridge between the bivariate Jacobi source and
the modulo-four theta streams used by the Tunnell passage.  The Laurent unit
receiver is reopened into its complete integral square-root population before
any residue fold is made.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver

open Finset
open PowerSeries
open Soma.Holonics.Mathematics.JacobiTripleProductKernel
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Mathematics.JacobiFiniteDiagonalReceiver
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift

/-- Complete integral orientations whose square reaches one coefficient. -/
def squareRootPopulation (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ)).filter fun m =>
    n = m.natAbs ^ 2

private theorem squareRoot_mem_box {n : ℕ} {m : ℤ}
    (hroot : n = m.natAbs ^ 2) :
    m ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  have hcast : (n : ℤ) = m ^ 2 := by
    rw [hroot]
    simp
  rw [Finset.mem_Icc]
  constructor
  · by_cases hm : 0 ≤ m
    · omega
    · have hm' : m ≤ -1 := by omega
      have hprod : 0 ≤ (-m) * (-m - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
  · by_cases hm : m ≤ 0
    · have hn : 0 ≤ (n : ℤ) := by positivity
      exact hm.trans hn
    · have hm' : 1 ≤ m := by omega
      have hprod : 0 ≤ m * (m - 1) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

/-- The finite support of one Jacobi source coefficient is exactly its
integral square-root carrier. -/
theorem support_coeff_rhs_eq_squareRootPopulation (n : ℕ) :
    (PowerSeries.coeff n rhs).support = squareRootPopulation n := by
  ext m
  simp only [Finsupp.mem_support_iff, squareRootPopulation,
    Finset.mem_filter]
  rw [coeff_coeff_rhs]
  by_cases hroot : n = m.natAbs ^ 2
  · rw [if_pos hroot]
    exact ⟨fun _ => ⟨squareRoot_mem_box hroot, hroot⟩,
      fun _ => one_ne_zero⟩
  · rw [if_neg hroot]
    simp [hroot]

/-- Every unit-specialized Jacobi coefficient is the exact signed current of
its complete square-root occurrence population. -/
theorem coeff_unitSquareTheta_eq_squareRootCurrent
    (ε : ℤˣ) (n : ℕ) :
    PowerSeries.coeff n (unitSquareTheta ε) =
      ∑ m ∈ squareRootPopulation n, (ε ^ m).val := by
  rw [coeff_unitSquareTheta, laurentUnitReceiver_eq_finsuppSum]
  unfold Finsupp.sum
  rw [support_coeff_rhs_eq_squareRootPopulation]
  apply Finset.sum_congr rfl
  intro m hm
  have hroot := (Finset.mem_filter.mp hm).2
  rw [coeff_coeff_rhs, if_pos hroot]
  simp

/-- The positive unit forgets no occurrence and returns the ordinary square
root cardinality. -/
theorem coeff_unitSquareTheta_one (n : ℕ) :
    PowerSeries.coeff n (unitSquareTheta (1 : ℤˣ)) =
      ((squareRootPopulation n).card : ℤ) := by
  rw [coeff_unitSquareTheta_eq_squareRootCurrent]
  simp

/-- The four residue sheets with their residue address retained. -/
def taggedQuarterSquarePopulation (n : ℕ) :
    Finset (Σ _r : QuarterResidue, ℤ) :=
  Finset.univ.sigma fun r => quarterSquarePopulation r n

/-- The canonical modulo-four address of an integral occurrence. -/
def quarterResidueAddress (x : ℤ) : QuarterResidue :=
  ⟨(x : ZMod 4).val, (x : ZMod 4).val_lt⟩

@[simp] theorem quarterResidueAddress_returns (x : ℤ) :
    (x : ZMod 4) = (quarterResidueAddress x).val := by
  change (x : ZMod 4) = ((x : ZMod 4).val : ZMod 4)
  exact (ZMod.natCast_zmod_val _).symm

private theorem quarterResidueAddress_eq_of_returns
    (x : ℤ) (r : QuarterResidue)
    (h : (x : ZMod 4) = r.val) :
    quarterResidueAddress x = r := by
  apply Fin.ext
  change (x : ZMod 4).val = r.val
  calc
    (x : ZMod 4).val = ((r.val : ℕ) : ZMod 4).val :=
      congrArg ZMod.val h
    _ = r.val := ZMod.val_natCast_of_lt r.isLt

/-- A square root and its uniquely reconstructed modulo-four address carry
exactly the same information as the tagged residue occurrence. -/
def squareRootEquivTaggedQuarter (n : ℕ) :
    {x // x ∈ squareRootPopulation n} ≃
      {q // q ∈ taggedQuarterSquarePopulation n} where
  toFun x := ⟨⟨quarterResidueAddress x.1, x.1⟩, by
    rcases Finset.mem_filter.mp x.2 with ⟨hbox, hroot⟩
    rw [taggedQuarterSquarePopulation, Finset.mem_sigma]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [quarterSquarePopulation, Finset.mem_filter]
    refine ⟨hbox, ?_, quarterResidueAddress_returns x.1⟩
    have hcast : (n : ℤ) = x.1 ^ 2 := by
      calc
        (n : ℤ) = ((x.1.natAbs ^ 2 : ℕ) : ℤ) :=
          congrArg (fun k : ℕ => (k : ℤ)) hroot
        _ = x.1 ^ 2 := by simp
    exact hcast.symm⟩
  invFun q := ⟨q.1.2, by
    rcases Finset.mem_sigma.mp q.2 with ⟨_hr, hx⟩
    rcases Finset.mem_filter.mp hx with ⟨hbox, hsquare, _hresidue⟩
    rw [squareRootPopulation, Finset.mem_filter]
    refine ⟨hbox, ?_⟩
    have hrootZ :
        (n : ℤ) = ((q.1.2.natAbs ^ 2 : ℕ) : ℤ) := by
      calc
        (n : ℤ) = q.1.2 ^ 2 := hsquare.symm
        _ = ((q.1.2.natAbs ^ 2 : ℕ) : ℤ) := by simp
    exact_mod_cast hrootZ⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv q := by
    rcases q with ⟨⟨r, x⟩, hq⟩
    apply Subtype.ext
    apply Sigma.ext
    · rcases Finset.mem_sigma.mp hq with ⟨_hr, hx⟩
      have hreturns := (Finset.mem_filter.mp hx).2.2
      exact quarterResidueAddress_eq_of_returns x r hreturns
    · rfl

/-- The complete square-root count is the sum of its four addressed residue
sheets; this is a bijection theorem, not an arithmetic coincidence. -/
theorem squareRootPopulation_card_eq_sum_quarterSquarePopulation (n : ℕ) :
    (squareRootPopulation n).card =
      ∑ r : QuarterResidue, (quarterSquarePopulation r n).card := by
  have hcard :
      (squareRootPopulation n).card =
        (taggedQuarterSquarePopulation n).card := by
    simpa only [Fintype.card_coe] using
      Fintype.card_congr (squareRootEquivTaggedQuarter n)
  rw [hcard, taggedQuarterSquarePopulation, Finset.card_sigma]

/-- The positive Jacobi unit specialization is exactly the sum of the four
modulo-four square theta streams. -/
theorem unitSquareTheta_one_eq_sum_quarterSquareTheta :
    unitSquareTheta (1 : ℤˣ) =
      ∑ r : QuarterResidue, quarterSquareTheta r := by
  apply PowerSeries.ext
  intro n
  rw [coeff_unitSquareTheta_one, map_sum]
  simp only [coeff_quarterSquareTheta]
  push_cast
  exact_mod_cast squareRootPopulation_card_eq_sum_quarterSquarePopulation n

/-- After the explicit odd-orientation fold, the ordinary square theta is the
three-stream face `A + 2B + C`. -/
theorem unitSquareTheta_one_eq_foldedQuarterSquareTheta :
    unitSquareTheta (1 : ℤˣ) =
      quarterSquareTheta 0 + 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2 := by
  rw [unitSquareTheta_one_eq_sum_quarterSquareTheta]
  simp only [Fin.sum_univ_four]
  rw [← quarterSquareTheta_one_eq_three]
  ring

/-! ## The negative unit retains the orientation sign -/

/-- The sign carried by one modulo-four orientation.  It is a receiver face
of the addressed residue, not an independently assigned coefficient. -/
def quarterSign (r : QuarterResidue) : ℤ :=
  if r.val % 2 = 0 then 1 else -1

private theorem negOnePow_eq_quarterSign {x : ℤ} {r : QuarterResidue}
    (h : (x : ZMod 4) = r.val) :
    (((-1 : ℤˣ) ^ x).val : ℤ) = quarterSign r := by
  have h4 : (x : ZMod 4) = ((r.val : ℤ) : ZMod 4) := by
    simpa using h
  have hdiv : (4 : ℤ) ∣ (r.val : ℤ) - x :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub x (r.val : ℤ) 4).mp h4
  rcases hdiv with ⟨k, hk⟩
  change x.negOnePow.val = quarterSign r
  fin_cases r <;> norm_num [quarterSign] at hk ⊢
  · rw [Int.negOnePow_even x ⟨-2 * k, by omega⟩]
  · rw [Int.negOnePow_odd x ⟨-2 * k, by omega⟩]
  · rw [Int.negOnePow_even x ⟨1 - 2 * k, by omega⟩]
  · rw [Int.negOnePow_odd x ⟨1 - 2 * k, by omega⟩]

private theorem squareRootNegCurrent_eq_taggedQuarterCurrent (n : ℕ) :
    (∑ m ∈ squareRootPopulation n, (((-1 : ℤˣ) ^ m).val : ℤ)) =
      ∑ q ∈ taggedQuarterSquarePopulation n,
        (((-1 : ℤˣ) ^ q.2).val : ℤ) := by
  calc
    (∑ m ∈ squareRootPopulation n, (((-1 : ℤˣ) ^ m).val : ℤ)) =
        ∑ x : {m // m ∈ squareRootPopulation n},
          (((-1 : ℤˣ) ^ x.1).val : ℤ) := by
            rw [← Finset.sum_attach, Finset.attach_eq_univ]
    _ = ∑ q : {q // q ∈ taggedQuarterSquarePopulation n},
          (((-1 : ℤˣ) ^ q.1.2).val : ℤ) :=
      Fintype.sum_equiv (squareRootEquivTaggedQuarter n)
        (fun x => (((-1 : ℤˣ) ^ x.1).val : ℤ))
        (fun q => (((-1 : ℤˣ) ^ q.1.2).val : ℤ)) (fun _ => rfl)
    _ = ∑ q ∈ taggedQuarterSquarePopulation n,
          (((-1 : ℤˣ) ^ q.2).val : ℤ) := by
            have h := Finset.sum_attach (taggedQuarterSquarePopulation n)
              (fun q => (((-1 : ℤˣ) ^ q.2).val : ℤ))
            rw [Finset.attach_eq_univ] at h
            exact h

private theorem taggedQuarterCurrent_eq_signCards (n : ℕ) :
    (∑ q ∈ taggedQuarterSquarePopulation n,
        (((-1 : ℤˣ) ^ q.2).val : ℤ)) =
      ∑ r : QuarterResidue,
        quarterSign r * ((quarterSquarePopulation r n).card : ℤ) := by
  rw [taggedQuarterSquarePopulation, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _hr
  calc
    (∑ x ∈ quarterSquarePopulation r n,
        (((-1 : ℤˣ) ^ x).val : ℤ)) =
        ∑ _x ∈ quarterSquarePopulation r n, quarterSign r := by
          apply Finset.sum_congr rfl
          intro x hx
          exact negOnePow_eq_quarterSign (Finset.mem_filter.mp hx).2.2
    _ = quarterSign r * ((quarterSquarePopulation r n).card : ℤ) := by
      simp [mul_comm]

/-- The negative Jacobi unit reads the exact signed cardinality of the four
addressed residue sheets. -/
theorem coeff_unitSquareTheta_neg_one (n : ℕ) :
    PowerSeries.coeff n (unitSquareTheta (-1 : ℤˣ)) =
      ∑ r : QuarterResidue,
        quarterSign r * ((quarterSquarePopulation r n).card : ℤ) := by
  rw [coeff_unitSquareTheta, laurentUnitReceiver_eq_finsuppSum]
  unfold Finsupp.sum
  rw [support_coeff_rhs_eq_squareRootPopulation]
  calc
    (∑ a ∈ squareRootPopulation n,
        (fun m c => c * (((-1 : ℤˣ) ^ m).val : ℤ)) a
          (PowerSeries.coeff n rhs a)) =
        ∑ m ∈ squareRootPopulation n,
          (((-1 : ℤˣ) ^ m).val : ℤ) := by
            apply Finset.sum_congr rfl
            intro m hm
            have hroot := (Finset.mem_filter.mp hm).2
            rw [coeff_coeff_rhs, if_pos hroot]
            simp
    _ = _ := (squareRootNegCurrent_eq_taggedQuarterCurrent n).trans
      (taggedQuarterCurrent_eq_signCards n)

/-- The negative unit specialization is the orientation-sensitive square
theta face `A - 2B + C`. -/
theorem unitSquareTheta_neg_one_eq_foldedQuarterSquareTheta :
    unitSquareTheta (-1 : ℤˣ) =
      quarterSquareTheta 0 - 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_unitSquareTheta_neg_one]
  change (∑ r : QuarterResidue,
      quarterSign r * ((quarterSquarePopulation r n).card : ℤ)) =
    PowerSeries.coeff n
      (quarterSquareTheta 0 - PowerSeries.C 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2)
  simp only [Fin.sum_univ_four, map_add, map_sub, PowerSeries.coeff_C_mul,
    coeff_quarterSquareTheta]
  simp [quarterSign, quarterSquarePopulation_one_card_eq_three]
  ring

/-! ## Product faces returned by the two unit orientations -/

/-- The positive unit Jacobi product is the ordinary square theta stream
`A + 2B + C`, with all infinite-product transport already discharged. -/
theorem jacobiPositiveUnitProduct_eq_foldedQuarterSquareTheta :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 2) *
        qPochhammerInf (-PowerSeries.X) (PowerSeries.X ^ 2) ^ 2 =
      quarterSquareTheta 0 + 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2 := by
  rw [← unitSquareTheta_one_eq_foldedQuarterSquareTheta,
    ← jacobi_unit_product_eq_unitSquareTheta (1 : ℤˣ)]
  norm_num
  ring

/-- The negative unit Jacobi product is the signed square theta stream
`A - 2B + C`. -/
theorem jacobiNegativeUnitProduct_eq_foldedQuarterSquareTheta :
    letI : TopologicalSpace (PowerSeries ℤ) := integerSeriesPiTop
    qPochhammerInf (PowerSeries.X ^ 2) (PowerSeries.X ^ 2) *
        qPochhammerInf PowerSeries.X (PowerSeries.X ^ 2) ^ 2 =
      quarterSquareTheta 0 - 2 * quarterSquareTheta 1 +
        quarterSquareTheta 2 := by
  rw [← unitSquareTheta_neg_one_eq_foldedQuarterSquareTheta,
    ← jacobi_unit_product_eq_unitSquareTheta (-1 : ℤˣ)]
  norm_num
  ring

#print axioms support_coeff_rhs_eq_squareRootPopulation
#print axioms coeff_unitSquareTheta_eq_squareRootCurrent
#print axioms coeff_unitSquareTheta_one
#print axioms coeff_unitSquareTheta_neg_one
#print axioms squareRootPopulation_card_eq_sum_quarterSquarePopulation
#print axioms unitSquareTheta_one_eq_foldedQuarterSquareTheta
#print axioms unitSquareTheta_neg_one_eq_foldedQuarterSquareTheta
#print axioms jacobiPositiveUnitProduct_eq_foldedQuarterSquareTheta
#print axioms jacobiNegativeUnitProduct_eq_foldedQuarterSquareTheta

end Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver

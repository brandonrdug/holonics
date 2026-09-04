import ElementaryHolonics.Millennium.FamilyTunnellFourSquareThetaReceiver

/-!
# The ambient odd four-square theta coefficient is the integral norm shell

The residue polynomial used in the Hopf subtraction is first opened into its
complete modulo-four population and then glued back to the integral Hamilton
source.  Thus the ambient term is no longer an anonymous theta coefficient:
at every odd positive address it is exactly the cardinality of the complete
ordered four-square shell.

This file deliberately stops before evaluating that cardinality.  The next
arithmetic theorem is Jacobi's exact four-square count; it is a theorem about
this carrier, not a replacement definition of it.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellFourSquarePrimeCensus

open Finset
open PowerSeries
open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus
open Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver

/-- All residue addresses whose four-square norm is odd. -/
def ambientOddResidues : Finset ResidueQuaternion :=
  Finset.univ.filter residueNormOdd

private theorem residueEvaluate_ambient_eq_univ_sum
    {R : Type*} [CommRing R] (a b c : R) :
    residueEvaluate a b c oddFourSquareResiduePolynomial =
      ∑ q : ResidueQuaternion,
        if residueNormOdd q then foldedCoordinateProduct a b c q else 0 := by
  unfold residueEvaluate oddFourSquareResiduePolynomial
  calc
    (∑ e : ResidueExponent,
        ((∑ q : ResidueQuaternion,
          if residueNormOdd q ∧ foldedResidueExponent q = e then 1 else 0) : ℤ) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val) =
      ∑ e : ResidueExponent, ∑ q : ResidueQuaternion,
        ((if residueNormOdd q ∧ foldedResidueExponent q = e then 1 else 0 : ℤ) : R) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val := by
            apply Finset.sum_congr rfl
            intro e _he
            push_cast
            rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    _ = ∑ q : ResidueQuaternion, ∑ e : ResidueExponent,
        ((if residueNormOdd q ∧ foldedResidueExponent q = e then 1 else 0 : ℤ) : R) *
          a ^ e.1.val * b ^ e.2.1.val * c ^ e.2.2.val := by
            rw [Finset.sum_comm]
    _ = ∑ q : ResidueQuaternion,
        if residueNormOdd q then foldedCoordinateProduct a b c q else 0 := by
      apply Finset.sum_congr rfl
      intro q _hqUniv
      by_cases hq : residueNormOdd q
      · rw [if_pos hq]
        rw [Finset.sum_eq_single (foldedResidueExponent q)]
        · simp only [hq, true_and, if_pos, Int.cast_one, one_mul]
          exact foldedMonomial_eq_coordinateProduct a b c q
        · intro e _he hne
          have hnot : ¬ foldedResidueExponent q = e := fun h => hne h.symm
          simp [hnot]
        · simp
      · rw [if_neg hq]
        apply Finset.sum_eq_zero
        intro e _he
        simp [hq]

/-- The ambient residue polynomial reopens into one four-square theta term for
every admitted residue address. -/
theorem ambientOddFourSquareTheta_eq_sum_residueTerms :
    ambientOddFourSquareTheta =
      ∑ r ∈ ambientOddResidues, foldedResidueThetaTerm r := by
  unfold ambientOddFourSquareTheta
  rw [residueEvaluate_ambient_eq_univ_sum]
  rw [ambientOddResidues, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hodd : residueNormOdd r
  · rw [if_pos hodd, if_pos hodd,
      foldedResidueThetaTerm_eq_coordinateProduct]
  · rw [if_neg hodd, if_neg hodd]

/-- The ambient coefficient as a sum of exact, unfolded residue shells. -/
theorem coeff_ambientOddFourSquareTheta_eq_sum_exactShell_card (n : ℕ) :
    PowerSeries.coeff n ambientOddFourSquareTheta =
      ∑ r ∈ ambientOddResidues,
        ((fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ) := by
  rw [ambientOddFourSquareTheta_eq_sum_residueTerms, map_sum]
  apply Finset.sum_congr rfl
  intro r _hr
  unfold foldedResidueThetaTerm
  rw [coeff_fourQuarterSquareTheta_eq_residueShell_card]
  exact_mod_cast foldedResidueShell_card_eq_exact r n

/-- The tagged exact residue carrier behind the ambient coefficient. -/
def exactAmbientOddResidueCarrier (n : ℕ) :
    Finset (Σ r : ResidueQuaternion, IntegerQuadruple) :=
  ambientOddResidues.sigma fun r =>
    fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n

theorem coeff_ambientOddFourSquareTheta_eq_exactCarrier_card (n : ℕ) :
    PowerSeries.coeff n ambientOddFourSquareTheta =
      ((exactAmbientOddResidueCarrier n).card : ℤ) := by
  rw [coeff_ambientOddFourSquareTheta_eq_sum_exactShell_card,
    exactAmbientOddResidueCarrier, Finset.card_sigma]
  push_cast
  rfl

/-- The complete finite Hamilton norm shell, before imposing the Hopf winding
seam. -/
def ambientHamiltonPopulation (n : ℕ) : Finset HamiltonInt :=
  (hamiltonBox n).filter fun q => Quaternion.normSq q = (n : ℤ)

theorem mem_ambientHamiltonPopulation_iff {n : ℕ} (hn : 0 < n)
    (q : HamiltonInt) :
    q ∈ ambientHamiltonPopulation n ↔ Quaternion.normSq q = (n : ℤ) := by
  rw [ambientHamiltonPopulation, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨mem_hamiltonBox_of_norm hn q h, h⟩

private theorem ambientCoordinates_mem_exactShell
    {n : ℕ} (hn : 0 < n) {q : HamiltonInt}
    (hq : q ∈ ambientHamiltonPopulation n) :
    coordinatesOfHamilton q ∈ fourSquareResidueShell
      (residueAddressOfHamilton q).1
      (residueAddressOfHamilton q).2.1
      (residueAddressOfHamilton q).2.2.1
      (residueAddressOfHamilton q).2.2.2 n := by
  have hnorm := (mem_ambientHamiltonPopulation_iff hn q).mp hq
  have hbox := mem_hamiltonBox_of_norm hn q hnorm
  have hcoordinates := (mem_hamiltonBox_iff n q).mp hbox
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [coordinatesOfHamilton, Finset.mem_product]
    exact ⟨⟨hcoordinates.1, hcoordinates.2.1⟩,
      ⟨hcoordinates.2.2.1, hcoordinates.2.2.2⟩⟩
  · rw [Quaternion.normSq_def'] at hnorm
    exact hnorm
  · exact (quarterResidueOfInt_cast q.re).symm
  · exact (quarterResidueOfInt_cast q.imI).symm
  · exact (quarterResidueOfInt_cast q.imJ).symm
  · exact (quarterResidueOfInt_cast q.imK).symm

private theorem exactAmbientCoordinates_mem_population
    {n : ℕ} (hn : 0 < n)
    {r : ResidueQuaternion} {q : IntegerQuadruple}
    (hq : q ∈ fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n) :
    coordinatesToHamilton q ∈ ambientHamiltonPopulation n := by
  rw [mem_ambientHamiltonPopulation_iff hn, Quaternion.normSq_def']
  exact (Finset.mem_filter.mp hq).2.1

/-- Oddness places the canonical residue address of every norm occurrence in
the ambient residue aperture. -/
private theorem residueAddress_mem_ambient
    {n : ℕ} (hn : 0 < n) (hodd : Odd n) {q : HamiltonInt}
    (hq : q ∈ ambientHamiltonPopulation n) :
    residueAddressOfHamilton q ∈ ambientOddResidues := by
  rw [ambientOddResidues, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    residueNormOdd_of_exactShell hodd (ambientCoordinates_mem_exactShell hn hq)⟩

/-- The ambient tagged residue body and the actual Hamilton norm shell are the
same finite population at every odd positive address. -/
def ambientHamiltonEquivExactResidueCarrier
    (n : ℕ) (hn : 0 < n) (hodd : Odd n) :
    {q // q ∈ ambientHamiltonPopulation n} ≃
      {q // q ∈ exactAmbientOddResidueCarrier n} where
  toFun q := ⟨Sigma.mk (residueAddressOfHamilton q.1)
      (coordinatesOfHamilton q.1), by
    rw [exactAmbientOddResidueCarrier, Finset.mem_sigma]
    exact ⟨residueAddress_mem_ambient hn hodd q.2,
      ambientCoordinates_mem_exactShell hn q.2⟩⟩
  invFun q := ⟨coordinatesToHamilton q.1.2, by
    rcases Finset.mem_sigma.mp q.2 with ⟨_hr, hcoordinates⟩
    exact exactAmbientCoordinates_mem_population hn hcoordinates⟩
  left_inv q := by
    apply Subtype.ext
    exact coordinatesToHamilton_coordinatesOfHamilton q.1
  right_inv q := by
    apply Subtype.ext
    rcases Finset.mem_sigma.mp q.2 with ⟨_hr, hcoordinates⟩
    apply Sigma.ext
    · exact residueAddress_coordinatesToHamilton hcoordinates
    · simp

/-- **THE AMBIENT THETA COEFFICIENT IS THE COMPLETE FOUR-SQUARE NORM
SHELL.** -/
theorem coeff_ambientOddFourSquareTheta_eq_ambientHamiltonPopulation_card
    {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    PowerSeries.coeff n ambientOddFourSquareTheta =
      ((ambientHamiltonPopulation n).card : ℤ) := by
  rw [coeff_ambientOddFourSquareTheta_eq_exactCarrier_card]
  have hcard :
      (ambientHamiltonPopulation n).card =
        (exactAmbientOddResidueCarrier n).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr
      (ambientHamiltonEquivExactResidueCarrier n hn hodd)
  exact_mod_cast hcard.symm

#print axioms ambientOddFourSquareTheta_eq_sum_residueTerms
#print axioms coeff_ambientOddFourSquareTheta_eq_exactCarrier_card
#print axioms ambientHamiltonEquivExactResidueCarrier
#print axioms coeff_ambientOddFourSquareTheta_eq_ambientHamiltonPopulation_card

end Soma.Holonics.Millennium.FamilyTunnellFourSquarePrimeCensus

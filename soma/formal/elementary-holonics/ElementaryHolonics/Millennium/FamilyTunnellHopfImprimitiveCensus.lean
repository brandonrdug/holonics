import ElementaryHolonics.Millennium.FamilyTunnellTwoSquarePrimeCensus

/-!
# The complete imprimitive Hopf boundary is two Gaussian prime shells

The Hopf source is imprimitive precisely when its returned first-Brandt point
is one of the two axis endpoints `(0, ±p, 0)`.  At the positive endpoint the
last two Hamilton coordinates vanish; at the negative endpoint the first two
vanish.  Consequently the complete deleted source is two disjoint copies of
the ordered Gaussian norm-`p` carrier.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHopfImprimitiveCensus

open Finset
open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellQuaternionHopf
open Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus
open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellHeckeIncidence
open Soma.Holonics.Millennium.FamilyTunnellTwoSquarePrimeCensus

variable {p : ℕ} [Fact p.Prime]

noncomputable local instance : DecidableEq HamiltonInt := Classical.decEq _

/-- The complement of the primitive Hopf source inside the complete source. -/
def imprimitiveFirstHopfSourcePopulation : Finset HamiltonInt :=
  (firstHopfSourcePopulation p).filter fun q =>
    reduceTriple (p := p) (hopfReturnedTriple q) = (0, 0, 0)

def upperGaussianSource (q : ℤ × ℤ) : HamiltonInt :=
  ⟨q.1, q.2, 0, 0⟩

def lowerGaussianSource (q : ℤ × ℤ) : HamiltonInt :=
  ⟨0, 0, q.1, q.2⟩

private theorem upperGaussianSource_injective :
    Function.Injective upperGaussianSource := by
  intro q r h
  apply Prod.ext
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h

private theorem lowerGaussianSource_injective :
    Function.Injective lowerGaussianSource := by
  intro q r h
  apply Prod.ext
  · exact congrArg QuaternionAlgebra.imJ h
  · exact congrArg QuaternionAlgebra.imK h

def upperGaussianSources : Finset HamiltonInt :=
  (twoSquarePrimePopulation p).map
    ⟨upperGaussianSource, upperGaussianSource_injective⟩

def lowerGaussianSources : Finset HamiltonInt :=
  (twoSquarePrimePopulation p).map
    ⟨lowerGaussianSource, lowerGaussianSource_injective⟩

private theorem upperGaussianSource_mem_imprimitive
    {q : ℤ × ℤ} (hq : q ∈ twoSquarePrimePopulation p) :
    upperGaussianSource q ∈ imprimitiveFirstHopfSourcePopulation (p := p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hnorm := (mem_twoSquarePrimePopulation_iff hp q).mp hq
  rw [imprimitiveFirstHopfSourcePopulation, Finset.mem_filter]
  constructor
  · rw [mem_firstHopfSourcePopulation_iff hp]
    constructor
    · simpa [upperGaussianSource, Quaternion.normSq_def'] using hnorm
    · refine ⟨0, ?_⟩
      simp [hopfWindingDifference, hopfTransverseJ, hopfTransverseK,
        upperGaussianSource]
  · simp [reduceTriple, hopfReturnedTriple, hopfTransverseJ,
      hopfTransverseK, hopfWindingDifference, hopfLongitudinal,
      upperGaussianSource, hnorm]

private theorem lowerGaussianSource_mem_imprimitive
    {q : ℤ × ℤ} (hq : q ∈ twoSquarePrimePopulation p) :
    lowerGaussianSource q ∈ imprimitiveFirstHopfSourcePopulation (p := p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hnorm := (mem_twoSquarePrimePopulation_iff hp q).mp hq
  rw [imprimitiveFirstHopfSourcePopulation, Finset.mem_filter]
  constructor
  · rw [mem_firstHopfSourcePopulation_iff hp]
    constructor
    · simpa [lowerGaussianSource, Quaternion.normSq_def'] using hnorm
    · refine ⟨0, ?_⟩
      simp [hopfWindingDifference, hopfTransverseJ, hopfTransverseK,
        lowerGaussianSource]
  · apply Prod.ext
    · simp [reduceTriple, hopfReturnedTriple, hopfTransverseJ,
        hopfTransverseK, lowerGaussianSource]
    · apply Prod.ext
      · have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hnorm
        have hcast' :
            (q.1 : ZMod p) ^ 2 + (q.2 : ZMod p) ^ 2 = 0 := by
          simpa using hcast
        have hneg := congrArg Neg.neg hcast'
        simpa [reduceTriple, hopfReturnedTriple, hopfTransverseJ,
          hopfTransverseK, hopfLongitudinal, lowerGaussianSource,
          sub_eq_add_neg, add_comm] using hneg
      · simp [reduceTriple, hopfReturnedTriple, hopfTransverseJ,
          hopfTransverseK, hopfWindingDifference, lowerGaussianSource]

private theorem source_eq_upper_of_positive_endpoint
    {q : HamiltonInt}
    (hnorm : Quaternion.normSq q = (p : ℤ))
    (hreturn : hopfReturnedTriple q = (0, (p : ℤ), 0)) :
    q = upperGaussianSource (q.re, q.imI) := by
  have hlong := congrArg (fun m : IntTriple => m.2.1) hreturn
  change hopfLongitudinal q = (p : ℤ) at hlong
  unfold hopfLongitudinal at hlong
  rw [Quaternion.normSq_def'] at hnorm
  have hc : q.imJ = 0 := by
    have hc2 : q.imJ ^ 2 = 0 := by
      nlinarith [sq_nonneg q.imJ, sq_nonneg q.imK]
    exact eq_zero_of_pow_eq_zero hc2
  have hd : q.imK = 0 := by
    have hd2 : q.imK ^ 2 = 0 := by
      nlinarith [sq_nonneg q.imJ, sq_nonneg q.imK]
    exact eq_zero_of_pow_eq_zero hd2
  apply Quaternion.ext <;> simp [upperGaussianSource, hc, hd]

private theorem source_eq_lower_of_negative_endpoint
    {q : HamiltonInt}
    (hnorm : Quaternion.normSq q = (p : ℤ))
    (hreturn : hopfReturnedTriple q = (0, -(p : ℤ), 0)) :
    q = lowerGaussianSource (q.imJ, q.imK) := by
  have hlong := congrArg (fun m : IntTriple => m.2.1) hreturn
  change hopfLongitudinal q = -(p : ℤ) at hlong
  unfold hopfLongitudinal at hlong
  rw [Quaternion.normSq_def'] at hnorm
  have ha : q.re = 0 := by
    have ha2 : q.re ^ 2 = 0 := by
      nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
    exact eq_zero_of_pow_eq_zero ha2
  have hb : q.imI = 0 := by
    have hb2 : q.imI ^ 2 = 0 := by
      nlinarith [sq_nonneg q.re, sq_nonneg q.imI]
    exact eq_zero_of_pow_eq_zero hb2
  apply Quaternion.ext <;> simp [lowerGaussianSource, ha, hb]

/-- **THE DELETED HOPF SOURCE IS EXACTLY THE TWO GAUSSIAN ENDPOINT
SHEETS.** -/
theorem imprimitiveFirstHopfSourcePopulation_eq_gaussian_union :
    imprimitiveFirstHopfSourcePopulation (p := p) =
      upperGaussianSources (p := p) ∪ lowerGaussianSources (p := p) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqSource, hzero⟩
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hnorm := (mem_firstHopfSourcePopulation_iff hp q).mp hqSource |>.1
    have hreturnedSource := hopfReturnedTriple_mem_firstPrimeSquarePopulation hqSource
    have hreturnedImp :
        hopfReturnedTriple q ∈
          imprimitiveFirstPrimeSquarePopulation (p := p) :=
      Finset.mem_filter.mpr ⟨hreturnedSource, hzero⟩
    rw [imprimitiveFirstPrimeSquarePopulation_eq_pair] at hreturnedImp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hreturnedImp
    rw [Finset.mem_union]
    rcases hreturnedImp with hpos | hneg
    · left
      have hsource := source_eq_upper_of_positive_endpoint hnorm hpos
      rw [upperGaussianSources, Finset.mem_map]
      refine ⟨(q.re, q.imI), ?_, hsource.symm⟩
      apply (mem_twoSquarePrimePopulation_iff hp _).mpr
      rw [Quaternion.normSq_def'] at hnorm
      have hc := congrArg QuaternionAlgebra.imJ hsource
      have hd := congrArg QuaternionAlgebra.imK hsource
      simp [upperGaussianSource] at hc hd
      simp [hc, hd] at hnorm
      exact hnorm
    · right
      have hsource := source_eq_lower_of_negative_endpoint hnorm hneg
      rw [lowerGaussianSources, Finset.mem_map]
      refine ⟨(q.imJ, q.imK), ?_, hsource.symm⟩
      apply (mem_twoSquarePrimePopulation_iff hp _).mpr
      rw [Quaternion.normSq_def'] at hnorm
      have ha := congrArg QuaternionAlgebra.re hsource
      have hb := congrArg QuaternionAlgebra.imI hsource
      simp [lowerGaussianSource] at ha hb
      simp [ha, hb] at hnorm
      exact hnorm
  · intro hq
    rw [Finset.mem_union] at hq
    rcases hq with hq | hq
    · rcases Finset.mem_map.mp hq with ⟨r, hr, rfl⟩
      exact upperGaussianSource_mem_imprimitive hr
    · rcases Finset.mem_map.mp hq with ⟨r, hr, rfl⟩
      exact lowerGaussianSource_mem_imprimitive hr

/-- The primitive and imprimitive receivers are complementary filters of the
same complete Hopf source carrier. -/
theorem firstHopfSourcePopulation_eq_primitive_union_imprimitive :
    firstHopfSourcePopulation p =
      primitiveFirstHopfSourcePopulation p ∪
        imprimitiveFirstHopfSourcePopulation (p := p) := by
  ext q
  simp only [primitiveFirstHopfSourcePopulation,
    imprimitiveFirstHopfSourcePopulation, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hq
    by_cases hzero :
        reduceTriple (p := p) (hopfReturnedTriple q) = (0, 0, 0)
    · exact Or.inr ⟨hq, hzero⟩
    · exact Or.inl ⟨hq, hzero⟩
  · rintro (hq | hq) <;> exact hq.1

/-- The two complementary Hopf source sheets have no common occurrence. -/
theorem primitiveFirstHopfSourcePopulation_disjoint_imprimitive :
    Disjoint (primitiveFirstHopfSourcePopulation p)
      (imprimitiveFirstHopfSourcePopulation (p := p)) := by
  rw [Finset.disjoint_left]
  intro q hprimitive himprimitive
  have hne := (Finset.mem_filter.mp hprimitive).2
  have heq := (Finset.mem_filter.mp himprimitive).2
  exact hne heq

private theorem upper_lower_gaussian_disjoint :
    Disjoint (upperGaussianSources (p := p))
      (lowerGaussianSources (p := p)) := by
  rw [Finset.disjoint_left]
  intro q hupper hlower
  rcases Finset.mem_map.mp hupper with ⟨a, ha, hqa⟩
  rcases Finset.mem_map.mp hlower with ⟨b, hb, hqb⟩
  have hzero : a = (0, 0) := by
    apply Prod.ext
    · have h := congrArg QuaternionAlgebra.re (hqa.trans hqb.symm)
      simpa [upperGaussianSource, lowerGaussianSource] using h
    · have h := congrArg QuaternionAlgebra.imI (hqa.trans hqb.symm)
      simpa [upperGaussianSource, lowerGaussianSource] using h
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hnorm := (mem_twoSquarePrimePopulation_iff hp a).mp ha
  rw [hzero] at hnorm
  simp at hnorm
  omega

/-- The complete imprimitive source count is twice the Gaussian prime count. -/
theorem imprimitiveFirstHopfSourcePopulation_card :
    (imprimitiveFirstHopfSourcePopulation (p := p)).card =
      2 * (twoSquarePrimePopulation p).card := by
  rw [imprimitiveFirstHopfSourcePopulation_eq_gaussian_union,
    Finset.card_union_of_disjoint upper_lower_gaussian_disjoint,
    upperGaussianSources, lowerGaussianSources,
    Finset.card_map, Finset.card_map]
  omega

/-- Exact source decomposition before any coefficient or character receiver is
applied. -/
theorem firstHopfSourcePopulation_card_eq_primitive_add_imprimitive :
    (firstHopfSourcePopulation p).card =
      (primitiveFirstHopfSourcePopulation p).card +
        (imprimitiveFirstHopfSourcePopulation (p := p)).card := by
  rw [firstHopfSourcePopulation_eq_primitive_union_imprimitive,
    Finset.card_union_of_disjoint
      primitiveFirstHopfSourcePopulation_disjoint_imprimitive]

/-- The same source count in its quadratic-character receiver. -/
theorem imprimitiveFirstHopfSourcePopulation_card_character (hp2 : p ≠ 2) :
    ((imprimitiveFirstHopfSourcePopulation (p := p)).card : ℤ) =
      8 * (quadraticChar (ZMod p) (-1) + 1) := by
  rw [imprimitiveFirstHopfSourcePopulation_card]
  push_cast
  rw [twoSquarePrimePopulation_card_character hp2]
  ring

#print axioms imprimitiveFirstHopfSourcePopulation_eq_gaussian_union
#print axioms imprimitiveFirstHopfSourcePopulation_card
#print axioms imprimitiveFirstHopfSourcePopulation_card_character
#print axioms firstHopfSourcePopulation_card_eq_primitive_add_imprimitive

end Soma.Holonics.Millennium.FamilyTunnellHopfImprimitiveCensus

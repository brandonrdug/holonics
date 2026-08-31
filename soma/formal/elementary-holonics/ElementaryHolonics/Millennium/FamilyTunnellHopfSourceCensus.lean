import ElementaryHolonics.Millennium.FamilyTunnellQuaternionHopf
import ElementaryHolonics.Millennium.HeckeEuler

/-!
# The finite integral Hopf-source census

The quaternionic Hopf law is now placed on a complete finite carrier.  A source
is not represented by four unrelated integer coordinates and later guessed to
be finite: its norm equation supplies an exact coordinate box, while the
transverse congruence retains the winding quotient required by the first
Tunnell--Brandt lattice.

The receiver

`source quaternion -> (x,y,z)`

is explicit on the whole carrier.  Right multiplication by the pivot `i`
stays inside, has period four, and preserves the receiver.  Combined with the
primitive fibre theorem in `FamilyTunnellQuaternionHopf`, this is the finite
counting body needed to divide source cardinalities by four without losing the
phase reconstruction fibre.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus

open Finset
open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellQuaternionHopf
open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector

local notation "ℤ[i]" => GaussianInt

noncomputable local instance : DecidableEq HamiltonInt := Classical.decEq _

abbrev HamiltonCoordinates := (ℤ × ℤ) × (ℤ × ℤ)

/-- The coordinate codec is used only to construct the finite source body. -/
def coordinatesToHamilton (c : HamiltonCoordinates) : HamiltonInt :=
  ⟨c.1.1, c.1.2, c.2.1, c.2.2⟩

theorem coordinatesToHamilton_injective :
    Function.Injective coordinatesToHamilton := by
  rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨a', b'⟩, ⟨c', d'⟩⟩ h
  have ha := congrArg QuaternionAlgebra.re h
  have hb := congrArg QuaternionAlgebra.imI h
  have hc := congrArg QuaternionAlgebra.imJ h
  have hd := congrArg QuaternionAlgebra.imK h
  simp [coordinatesToHamilton] at ha hb hc hd
  simp [ha, hb, hc, hd]

def hamiltonCoordinateBox (p : ℕ) : Finset HamiltonCoordinates :=
  ((Finset.Icc (-(p : ℤ)) (p : ℤ)) ×ˢ
      Finset.Icc (-(p : ℤ)) (p : ℤ)) ×ˢ
    ((Finset.Icc (-(p : ℤ)) (p : ℤ)) ×ˢ
      Finset.Icc (-(p : ℤ)) (p : ℤ))

/-- The finite Hamilton body addressed by its four exact coordinate intervals. -/
def hamiltonBox (p : ℕ) : Finset HamiltonInt :=
  (hamiltonCoordinateBox p).map
    ⟨coordinatesToHamilton, coordinatesToHamilton_injective⟩

theorem mem_hamiltonBox_iff (p : ℕ) (q : HamiltonInt) :
    q ∈ hamiltonBox p ↔
      q.re ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      q.imI ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      q.imJ ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      q.imK ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) := by
  constructor
  · intro hq
    rcases Finset.mem_map.mp hq with ⟨c, hc, rfl⟩
    change c ∈ hamiltonCoordinateBox p at hc
    simp only [hamiltonCoordinateBox, Finset.mem_product] at hc
    rcases hc with ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    change c.1.1 ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      c.1.2 ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      c.2.1 ∈ Finset.Icc (-(p : ℤ)) (p : ℤ) ∧
      c.2.2 ∈ Finset.Icc (-(p : ℤ)) (p : ℤ)
    exact ⟨ha, hb, hc, hd⟩
  · intro hq
    apply Finset.mem_map.mpr
    refine ⟨((q.re, q.imI), (q.imJ, q.imK)), ?_, ?_⟩
    · rcases hq with ⟨ha, hb, hc, hd⟩
      simp only [hamiltonCoordinateBox, Finset.mem_product]
      exact ⟨⟨ha, hb⟩, ⟨hc, hd⟩⟩
    · apply Quaternion.ext <;> simp [coordinatesToHamilton]

/-- A positive integral norm equation itself places every coordinate inside the
declared finite box. -/
theorem mem_hamiltonBox_of_norm {p : ℕ} (hp : 0 < p) (q : HamiltonInt)
    (hnorm : Quaternion.normSq q = (p : ℤ)) : q ∈ hamiltonBox p := by
  rw [mem_hamiltonBox_iff]
  rw [Quaternion.normSq_def'] at hnorm
  have hpZ : (1 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp
  have hreLower : -(p : ℤ) ≤ q.re := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hreUpper : q.re ≤ (p : ℤ) := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hiLower : -(p : ℤ) ≤ q.imI := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hiUpper : q.imI ≤ (p : ℤ) := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hjLower : -(p : ℤ) ≤ q.imJ := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hjUpper : q.imJ ≤ (p : ℤ) := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hkLower : -(p : ℤ) ≤ q.imK := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  have hkUpper : q.imK ≤ (p : ℤ) := by
    nlinarith [sq_nonneg q.re, sq_nonneg q.imI,
      sq_nonneg q.imJ, sq_nonneg q.imK]
  simp only [Finset.mem_Icc]
  exact ⟨⟨hreLower, hreUpper⟩, ⟨hiLower, hiUpper⟩,
    ⟨hjLower, hjUpper⟩, ⟨hkLower, hkUpper⟩⟩

/-- The exact transverse difference whose quotient is the first-lattice winding. -/
def hopfWindingDifference (q : HamiltonInt) : ℤ :=
  hopfTransverseJ q - hopfTransverseK q

/-- Complete norm-`p` sources admitted by the first Brandt winding chart. -/
def firstHopfSourcePopulation (p : ℕ) : Finset HamiltonInt :=
  (hamiltonBox p).filter fun q =>
    Quaternion.normSq q = (p : ℤ) ∧ (4 : ℤ) ∣ hopfWindingDifference q

theorem mem_firstHopfSourcePopulation_iff
    {p : ℕ} (hp : 0 < p) (q : HamiltonInt) :
    q ∈ firstHopfSourcePopulation p ↔
      Quaternion.normSq q = (p : ℤ) ∧
        (4 : ℤ) ∣ hopfWindingDifference q := by
  rw [firstHopfSourcePopulation, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨mem_hamiltonBox_of_norm hp q h.1, h⟩

/-- The receiver is total on all quaternions; the source filter is what proves
that its last coordinate is an exact winding quotient. -/
def hopfReturnedTriple (q : HamiltonInt) : IntTriple :=
  (hopfTransverseJ q + hopfTransverseK q,
    (hopfLongitudinal q, hopfWindingDifference q / 4))

/-- Reconstruct the addressed occurrence from a member of the finite carrier. -/
def occurrenceOfSource {p : ℕ} (hp : 0 < p) {q : HamiltonInt}
    (hq : q ∈ firstHopfSourcePopulation p) : FirstHopfOccurrence p where
  source := q
  winding := hopfWindingDifference q / 4
  sourceNorm := (mem_firstHopfSourcePopulation_iff hp q).mp hq |>.1
  windingCloses := by
    have hdiv := (mem_firstHopfSourcePopulation_iff hp q).mp hq |>.2
    unfold hopfWindingDifference
    simpa [mul_comm] using (Int.ediv_mul_cancel hdiv).symm

@[simp] theorem occurrenceOfSource_source {p : ℕ} (hp : 0 < p)
    {q : HamiltonInt} (hq : q ∈ firstHopfSourcePopulation p) :
    (occurrenceOfSource hp hq).source = q := rfl

@[simp] theorem occurrenceOfSource_returnedTriple {p : ℕ} (hp : 0 < p)
    {q : HamiltonInt} (hq : q ∈ firstHopfSourcePopulation p) :
    (occurrenceOfSource hp hq).returnedTriple = hopfReturnedTriple q := by
  rfl

/-- The phase swing remains in the exact finite source population. -/
theorem phaseTurn_mem_firstHopfSourcePopulation
    {p : ℕ} (hp : 0 < p) {q : HamiltonInt}
    (hq : q ∈ firstHopfSourcePopulation p) :
    hopfPhaseTurnSource q ∈ firstHopfSourcePopulation p := by
  rw [mem_firstHopfSourcePopulation_iff hp]
  rw [normSq_hopfPhaseTurnSource]
  constructor
  · exact (mem_firstHopfSourcePopulation_iff hp q).mp hq |>.1
  · rw [hopfWindingDifference, hopfTransverseDifference_phaseTurn]
    exact (mem_firstHopfSourcePopulation_iff hp q).mp hq |>.2

/-- The finite receiver is invariant under the phase swing. -/
theorem hopfReturnedTriple_phaseTurn (q : HamiltonInt) :
    hopfReturnedTriple (hopfPhaseTurnSource q) = hopfReturnedTriple q := by
  apply Prod.ext
  · simp [hopfReturnedTriple, hopfPhaseTurnSource,
      hopfTransverseJ, hopfTransverseK]
    ring
  · apply Prod.ext
    · simp [hopfReturnedTriple, hopfPhaseTurnSource, hopfLongitudinal]
      ring
    · simp [hopfReturnedTriple, hopfWindingDifference,
        hopfTransverseDifference_phaseTurn]

/-- Every admitted finite source returns an actual prime-square point. -/
theorem hopfReturnedTriple_mem_firstPrimeSquarePopulation
    {p : ℕ} [Fact p.Prime] {q : HamiltonInt}
    (hq : q ∈ firstHopfSourcePopulation p) :
    hopfReturnedTriple q ∈ firstPrimeSquarePopulation (p := p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  simpa using returnedTriple_mem_firstPrimeSquarePopulation
    (occurrenceOfSource hp hq)

/-! ## The complete primitive receiver fibre -/

/-- Sources whose returned projective address survives modulo `p`. -/
def primitiveFirstHopfSourcePopulation (p : ℕ) [Fact p.Prime] : Finset HamiltonInt :=
  (firstHopfSourcePopulation p).filter fun q =>
    reduceTriple (p := p) (hopfReturnedTriple q) ≠ (0, 0, 0)

/-- The complete finite source fibre above one returned ternary point. -/
def primitiveHopfSourceFibre (p : ℕ) [Fact p.Prime]
    (m : IntTriple) : Finset HamiltonInt :=
  (primitiveFirstHopfSourcePopulation p).filter fun q =>
    hopfReturnedTriple q = m

/-- Four explicit phase representatives, with none of their source information
collapsed into a cardinal. -/
def hopfPhaseOrbit (q : HamiltonInt) : Finset HamiltonInt :=
  {q, hopfPhaseTurnSource q, -q, -hopfPhaseTurnSource q}

theorem phaseTurn_mem_primitiveFirstHopfSourcePopulation
    {p : ℕ} [Fact p.Prime] (hp : 0 < p) {q : HamiltonInt}
    (hq : q ∈ primitiveFirstHopfSourcePopulation p) :
    hopfPhaseTurnSource q ∈ primitiveFirstHopfSourcePopulation p := by
  rcases Finset.mem_filter.mp hq with ⟨hqSource, hprimitive⟩
  apply Finset.mem_filter.mpr
  exact ⟨phaseTurn_mem_firstHopfSourcePopulation hp hqSource, by
    rw [hopfReturnedTriple_phaseTurn]
    exact hprimitive⟩

theorem hopfPhaseTurnSource_thrice (q : HamiltonInt) :
    hopfPhaseTurnSource (hopfPhaseTurnSource (hopfPhaseTurnSource q)) =
      -hopfPhaseTurnSource q := by
  rw [hopfPhaseTurnSource_twice]

/-- **THE COMPLETE PRIMITIVE SOURCE FIBRE IS THE FOUR-POINT PHASE ORBIT.**

This is a finite-set equality, not merely a statement that four constructed
sources have the same return.  The forward direction uses the exhaustive
relative-phase theorem; the reverse direction transports membership and the
primitive receiver reading through the four exact turns. -/
theorem primitiveHopfSourceFibre_eq_phaseOrbit
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : HamiltonInt}
    (hq : q ∈ primitiveFirstHopfSourcePopulation p) :
    primitiveHopfSourceFibre p (hopfReturnedTriple q) = hopfPhaseOrbit q := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  ext r
  constructor
  · intro hr
    rcases Finset.mem_filter.mp hr with ⟨hrPrimitive, hrReturned⟩
    rcases Finset.mem_filter.mp hq with ⟨hqSource, hqPrimitive⟩
    rcases Finset.mem_filter.mp hrPrimitive with ⟨hrSource, _⟩
    let left := occurrenceOfSource hp hqSource
    let right := occurrenceOfSource hp hrSource
    have hreturned : left.returnedTriple = right.returnedTriple := by
      change hopfReturnedTriple q = hopfReturnedTriple r
      exact hrReturned.symm
    have hprimitive :
        reduceTriple (p := p) left.returnedTriple ≠ (0, 0, 0) := by
      change reduceTriple (p := p) (hopfReturnedTriple q) ≠ (0, 0, 0)
      exact hqPrimitive
    rcases source_eq_phase_of_same_primitive_return hp2 left right
        hreturned hprimitive with h | h | h | h
    · simp only [hopfPhaseOrbit, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl h
    · simp only [hopfPhaseOrbit, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inl h)
    · simp only [hopfPhaseOrbit, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inl h))
    · simp only [hopfPhaseOrbit, Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Or.inr (Or.inr h))
  · intro hr
    simp only [hopfPhaseOrbit, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨hq, rfl⟩
    · refine Finset.mem_filter.mpr
        ⟨phaseTurn_mem_primitiveFirstHopfSourcePopulation hp hq, ?_⟩
      exact hopfReturnedTriple_phaseTurn q
    · have hq2 := phaseTurn_mem_primitiveFirstHopfSourcePopulation hp
        (phaseTurn_mem_primitiveFirstHopfSourcePopulation hp hq)
      rw [hopfPhaseTurnSource_twice] at hq2
      refine Finset.mem_filter.mpr ⟨hq2, ?_⟩
      calc
        hopfReturnedTriple (-q) =
            hopfReturnedTriple
              (hopfPhaseTurnSource (hopfPhaseTurnSource q)) := by
                rw [hopfPhaseTurnSource_twice]
        _ = hopfReturnedTriple (hopfPhaseTurnSource q) :=
          hopfReturnedTriple_phaseTurn _
        _ = hopfReturnedTriple q := hopfReturnedTriple_phaseTurn q
    · have hq3 := phaseTurn_mem_primitiveFirstHopfSourcePopulation hp
        (phaseTurn_mem_primitiveFirstHopfSourcePopulation hp
          (phaseTurn_mem_primitiveFirstHopfSourcePopulation hp hq))
      rw [hopfPhaseTurnSource_thrice] at hq3
      refine Finset.mem_filter.mpr ⟨hq3, ?_⟩
      calc
        hopfReturnedTriple (-hopfPhaseTurnSource q) =
            hopfReturnedTriple
              (hopfPhaseTurnSource
                (hopfPhaseTurnSource (hopfPhaseTurnSource q))) := by
                  rw [hopfPhaseTurnSource_thrice]
        _ = hopfReturnedTriple
              (hopfPhaseTurnSource (hopfPhaseTurnSource q)) :=
          hopfReturnedTriple_phaseTurn _
        _ = hopfReturnedTriple (hopfPhaseTurnSource q) :=
          hopfReturnedTriple_phaseTurn _
        _ = hopfReturnedTriple q := hopfReturnedTriple_phaseTurn q

private theorem hamilton_ne_neg_self_of_ne_zero {q : HamiltonInt} (hq : q ≠ 0) :
    q ≠ -q := by
  intro h
  apply hq
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  apply Quaternion.ext <;> simp at hre hi hj hk ⊢ <;> omega

private theorem hamilton_ne_phase_of_ne_zero {q : HamiltonInt} (hq : q ≠ 0) :
    q ≠ hopfPhaseTurnSource q := by
  intro h
  apply hq
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  apply Quaternion.ext <;>
    simp [hopfPhaseTurnSource] at hre hi hj hk ⊢ <;> omega

private theorem hamilton_ne_neg_phase_of_ne_zero {q : HamiltonInt} (hq : q ≠ 0) :
    q ≠ -hopfPhaseTurnSource q := by
  intro h
  apply hq
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  apply Quaternion.ext <;>
    simp [hopfPhaseTurnSource] at hre hi hj hk ⊢ <;> omega

private theorem phase_ne_neg_source_of_ne_zero {q : HamiltonInt} (hq : q ≠ 0) :
    hopfPhaseTurnSource q ≠ -q := by
  intro h
  apply hq
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  apply Quaternion.ext <;>
    simp [hopfPhaseTurnSource] at hre hi hj hk ⊢ <;> omega

/-- The four retained phase points are pairwise distinct at every positive norm. -/
theorem hopfPhaseOrbit_card_of_norm_pos {p : ℕ} (hp : 0 < p)
    {q : HamiltonInt} (hnorm : Quaternion.normSq q = (p : ℤ)) :
    (hopfPhaseOrbit q).card = 4 := by
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero] at hnorm
    simp at hnorm
    exact (Nat.ne_of_gt hp) (by exact_mod_cast hnorm.symm)
  have ht0 : hopfPhaseTurnSource q ≠ 0 := by
    intro hzero
    have hnormTurn := normSq_hopfPhaseTurnSource q
    rw [hzero, hnorm] at hnormTurn
    simp at hnormTurn
    exact (Nat.ne_of_gt hp) (by exact_mod_cast hnormTurn.symm)
  have hqTurn : q ≠ hopfPhaseTurnSource q :=
    hamilton_ne_phase_of_ne_zero hq0
  have hqNeg : q ≠ -q := hamilton_ne_neg_self_of_ne_zero hq0
  have hqNegTurn : q ≠ -hopfPhaseTurnSource q :=
    hamilton_ne_neg_phase_of_ne_zero hq0
  have hturnNeg : hopfPhaseTurnSource q ≠ -q :=
    phase_ne_neg_source_of_ne_zero hq0
  have hturnNegTurn : hopfPhaseTurnSource q ≠ -hopfPhaseTurnSource q :=
    hamilton_ne_neg_self_of_ne_zero ht0
  have hnegNegTurn : -q ≠ -hopfPhaseTurnSource q := by
    intro h
    exact hqTurn (neg_injective h)
  have hfirst :
      q ∉ ({hopfPhaseTurnSource q, -q, -hopfPhaseTurnSource q} :
        Finset HamiltonInt) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqTurn, hqNeg, hqNegTurn⟩
  have hsecond :
      hopfPhaseTurnSource q ∉ ({-q, -hopfPhaseTurnSource q} :
        Finset HamiltonInt) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hturnNeg, hturnNegTurn⟩
  have hthird : -q ∉ ({-hopfPhaseTurnSource q} : Finset HamiltonInt) := by
    simpa only [Finset.mem_singleton] using hnegNegTurn
  unfold hopfPhaseOrbit
  rw [Finset.card_insert_of_notMem hfirst,
    Finset.card_insert_of_notMem hsecond,
    Finset.card_insert_of_notMem hthird]
  simp

/-- Every inhabited primitive return fibre contains exactly four sources. -/
theorem primitiveHopfSourceFibre_card
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {q : HamiltonInt}
    (hq : q ∈ primitiveFirstHopfSourcePopulation p) :
    (primitiveHopfSourceFibre p (hopfReturnedTriple q)).card = 4 := by
  rw [primitiveHopfSourceFibre_eq_phaseOrbit hp2 hq]
  apply hopfPhaseOrbit_card_of_norm_pos (Fact.out : p.Prime).pos
  have hsource : q ∈ firstHopfSourcePopulation p :=
    (Finset.mem_filter.mp hq).1
  exact ((mem_firstHopfSourcePopulation_iff
    (Fact.out : p.Prime).pos q).mp hsource).1

/-! ## Fibrewise source/image cardinality -/

/-- The finite image actually reached by primitive norm-`p` Hopf sources. -/
def primitiveHopfReturnPopulation (p : ℕ) [Fact p.Prime] : Finset IntTriple :=
  (primitiveFirstHopfSourcePopulation p).image hopfReturnedTriple

theorem primitiveHopfSourceFibre_card_of_mem_return
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hm : m ∈ primitiveHopfReturnPopulation p) :
    (primitiveHopfSourceFibre p m).card = 4 := by
  rcases Finset.mem_image.mp hm with ⟨q, hq, hqm⟩
  rw [← hqm]
  exact primitiveHopfSourceFibre_card hp2 hq

/-- The complete primitive source population is four copies of its exact
receiver image.  This is the global cardinal consequence of the local
four-phase fibre theorem. -/
theorem primitiveHopfSourcePopulation_card_eq_four_mul_return_card
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (primitiveFirstHopfSourcePopulation p).card =
      4 * (primitiveHopfReturnPopulation p).card := by
  have hfibre := Finset.card_eq_sum_card_image hopfReturnedTriple
    (primitiveFirstHopfSourcePopulation p)
  change (primitiveFirstHopfSourcePopulation p).card =
      ∑ m ∈ primitiveHopfReturnPopulation p,
        (primitiveHopfSourceFibre p m).card at hfibre
  calc
    (primitiveFirstHopfSourcePopulation p).card =
        ∑ m ∈ primitiveHopfReturnPopulation p,
          (primitiveHopfSourceFibre p m).card := hfibre
    _ = ∑ _m ∈ primitiveHopfReturnPopulation p, 4 := by
      apply Finset.sum_congr rfl
      intro m hm
      exact primitiveHopfSourceFibre_card_of_mem_return hp2 hm
    _ = 4 * (primitiveHopfReturnPopulation p).card := by
      simp [mul_comm]

/-- Every returned source point is a primitive point of the complete first
Brandt prime-square carrier. -/
theorem primitiveHopfReturnPopulation_subset_primeSquare
    {p : ℕ} [Fact p.Prime] :
    primitiveHopfReturnPopulation p ⊆
      primitiveFirstPrimeSquarePopulation (p := p) := by
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨q, hq, rfl⟩
  rcases Finset.mem_filter.mp hq with ⟨hqSource, hprimitive⟩
  apply Finset.mem_filter.mpr
  exact ⟨hopfReturnedTriple_mem_firstPrimeSquarePopulation hqSource,
    hprimitive⟩

/-- The remaining reconstruction edge is now an exact equality of finite
populations: every primitive first-Brandt point must be reached by an integral
norm-`p` Hopf source. -/
def HopfReconstructionCompleteAt (p : ℕ) [Fact p.Prime] : Prop :=
  primitiveHopfReturnPopulation p =
    primitiveFirstPrimeSquarePopulation (p := p)

theorem primitiveHopfSourcePopulation_card_of_reconstruction
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hcomplete : HopfReconstructionCompleteAt p) :
    (primitiveFirstHopfSourcePopulation p).card =
      4 * (primitiveFirstPrimeSquarePopulation (p := p)).card := by
  rw [primitiveHopfSourcePopulation_card_eq_four_mul_return_card hp2,
    hcomplete]

/-! ## The exact Gaussian normalization data of a primitive sphere point -/

def spinorNorthWeight (p : ℕ) (m : IntTriple) : ℤ :=
  ((p : ℤ) + m.2.1) / 2

def spinorSouthWeight (p : ℕ) (m : IntTriple) : ℤ :=
  ((p : ℤ) - m.2.1) / 2

def spinorTransverseJ (m : IntTriple) : ℤ :=
  (m.1 + 4 * m.2.2) / 2

def spinorTransverseK (m : IntTriple) : ℤ :=
  (m.1 - 4 * m.2.2) / 2

private theorem odd_int_square_eight (n : ℤ) (hn : Odd n) :
    ∃ k : ℤ, n ^ 2 = 8 * k + 1 := by
  rcases hn with ⟨t, rfl⟩
  rcases t.even_or_odd with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · refine ⟨2 * u ^ 2 + u, ?_⟩
    ring
  · refine ⟨2 * u ^ 2 + 3 * u + 1, ?_⟩
    ring

/-- At an odd prime-square point, the longitudinal Brandt coordinate is odd. -/
theorem primeSquare_longitudinal_odd
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) : Odd m.2.1 := by
  have hpOddNat : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  rw [← Int.not_even_iff_odd]
  intro hyEven
  rcases hpOdd with ⟨a, ha⟩
  rcases hyEven with ⟨b, hb⟩
  unfold brandtFirstQuadratic at hnorm
  rw [ha, hb] at hnorm
  ring_nf at hnorm
  omega

/-- The first Brandt coordinate is even.  This is the exact mod-eight content
of the prime-square equation; it is what makes both transverse Hopf halves
integral. -/
theorem primeSquare_first_even
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) : Even m.1 := by
  have hpOddNat : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  have hyOdd := primeSquare_longitudinal_odd hp2 hnorm
  rw [← Int.not_odd_iff_even]
  intro hxOdd
  rcases odd_int_square_eight (p : ℤ) hpOdd with ⟨P, hP⟩
  rcases odd_int_square_eight m.2.1 hyOdd with ⟨Y, hY⟩
  rcases odd_int_square_eight m.1 hxOdd with ⟨X, hX⟩
  unfold brandtFirstQuadratic at hnorm
  omega

/-- The four half-coordinates really reconstruct their four unsliced values. -/
theorem spinor_half_coordinates
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) :
    2 * spinorNorthWeight p m = (p : ℤ) + m.2.1 ∧
    2 * spinorSouthWeight p m = (p : ℤ) - m.2.1 ∧
    2 * spinorTransverseJ m = m.1 + 4 * m.2.2 ∧
    2 * spinorTransverseK m = m.1 - 4 * m.2.2 := by
  have hpOddNat : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpOdd : Odd (p : ℤ) := by exact_mod_cast hpOddNat
  have hyOdd := primeSquare_longitudinal_odd hp2 hnorm
  have hxEven := primeSquare_first_even hp2 hnorm
  rcases hpOdd with ⟨P, hP⟩
  rcases hyOdd with ⟨Y, hY⟩
  rcases hxEven with ⟨X, hX⟩
  have hnDiv : (2 : ℤ) ∣ (p : ℤ) + m.2.1 := by
    refine ⟨P + Y + 1, ?_⟩
    omega
  have hsDiv : (2 : ℤ) ∣ (p : ℤ) - m.2.1 := by
    refine ⟨P - Y, ?_⟩
    omega
  have hjDiv : (2 : ℤ) ∣ m.1 + 4 * m.2.2 := by
    refine ⟨X + 2 * m.2.2, ?_⟩
    omega
  have hkDiv : (2 : ℤ) ∣ m.1 - 4 * m.2.2 := by
    refine ⟨X - 2 * m.2.2, ?_⟩
    omega
  constructor
  · simpa [spinorNorthWeight, mul_comm] using Int.ediv_mul_cancel hnDiv
  constructor
  · simpa [spinorSouthWeight, mul_comm] using Int.ediv_mul_cancel hsDiv
  constructor
  · simpa [spinorTransverseJ, mul_comm] using Int.ediv_mul_cancel hjDiv
  · simpa [spinorTransverseK, mul_comm] using Int.ediv_mul_cancel hkDiv

/-- A primitive point cannot be either pole of the sphere. -/
theorem primitive_longitudinal_strict
    {p : ℕ} [Fact p.Prime] {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2)
    (hprimitive : reduceTriple (p := p) m ≠ (0, 0, 0)) :
    -(p : ℤ) < m.2.1 ∧ m.2.1 < (p : ℤ) := by
  have hpZ : (0 : ℤ) < (p : ℤ) := by
    exact_mod_cast (Fact.out : p.Prime).pos
  have hyLower : -(p : ℤ) ≤ m.2.1 := by
    unfold brandtFirstQuadratic at hnorm
    nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
  have hyUpper : m.2.1 ≤ (p : ℤ) := by
    unfold brandtFirstQuadratic at hnorm
    nlinarith [sq_nonneg m.1, sq_nonneg m.2.1, sq_nonneg m.2.2]
  have hyNeLower : m.2.1 ≠ -(p : ℤ) := by
    intro hy
    have hx : m.1 = 0 := by
      unfold brandtFirstQuadratic at hnorm
      nlinarith [sq_nonneg m.1, sq_nonneg m.2.2]
    have hz : m.2.2 = 0 := by
      unfold brandtFirstQuadratic at hnorm
      nlinarith [sq_nonneg m.1, sq_nonneg m.2.2]
    apply hprimitive
    apply Prod.ext
    · simp [reduceTriple, hx]
    · apply Prod.ext
      · simp [reduceTriple, hy]
      · simp [reduceTriple, hz]
  have hyNeUpper : m.2.1 ≠ (p : ℤ) := by
    intro hy
    have hx : m.1 = 0 := by
      unfold brandtFirstQuadratic at hnorm
      nlinarith [sq_nonneg m.1, sq_nonneg m.2.2]
    have hz : m.2.2 = 0 := by
      unfold brandtFirstQuadratic at hnorm
      nlinarith [sq_nonneg m.1, sq_nonneg m.2.2]
    apply hprimitive
    apply Prod.ext
    · simp [reduceTriple, hx]
    · apply Prod.ext
      · simp [reduceTriple, hy]
      · simp [reduceTriple, hz]
  omega

/-- **THE PRIMITIVE SPHERE POINT RETURNS COPRIME-GRAIN NORMALIZATION DATA.**

The north and south weights are positive, add to the prime aperture, and their
product is exactly the Gaussian norm of the two transverse half-coordinates.
This is the integral rank-one Hermitian factorization problem that remains to
construct the normalized spinor; all parity, division, and endpoint issues have
been removed. -/
theorem primitive_spinor_normalization_data
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2)
    (hprimitive : reduceTriple (p := p) m ≠ (0, 0, 0)) :
    0 < spinorNorthWeight p m ∧
    0 < spinorSouthWeight p m ∧
    spinorNorthWeight p m + spinorSouthWeight p m = (p : ℤ) ∧
    spinorTransverseJ m ^ 2 + spinorTransverseK m ^ 2 =
      spinorNorthWeight p m * spinorSouthWeight p m := by
  rcases spinor_half_coordinates hp2 hnorm with ⟨hn, hs, hj, hk⟩
  rcases primitive_longitudinal_strict hnorm hprimitive with ⟨hyLower, hyUpper⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · unfold brandtFirstQuadratic at hnorm
    have hscaled :
        4 * (spinorTransverseJ m ^ 2 + spinorTransverseK m ^ 2) =
          4 * (spinorNorthWeight p m * spinorSouthWeight p m) := by
      calc
        4 * (spinorTransverseJ m ^ 2 + spinorTransverseK m ^ 2) =
            (2 * spinorTransverseJ m) ^ 2 +
              (2 * spinorTransverseK m) ^ 2 := by ring
        _ = (m.1 + 4 * m.2.2) ^ 2 + (m.1 - 4 * m.2.2) ^ 2 := by
          rw [hj, hk]
        _ = 2 * m.1 ^ 2 + 32 * m.2.2 ^ 2 := by ring
        _ = (p : ℤ) ^ 2 - m.2.1 ^ 2 := by linarith
        _ = ((p : ℤ) + m.2.1) * ((p : ℤ) - m.2.1) := by ring
        _ = (2 * spinorNorthWeight p m) *
              (2 * spinorSouthWeight p m) := by rw [hn, hs]
        _ = 4 * (spinorNorthWeight p m * spinorSouthWeight p m) := by ring
    linarith

private theorem natAbs_coprime_of_pos_add_prime
    {p : ℕ} (hp : p.Prime) {A C : ℤ}
    (hA : 0 < A) (hC : 0 < C) (hsum : A + C = (p : ℤ)) :
    Nat.Coprime A.natAbs C.natAbs := by
  rw [Nat.coprime_iff_gcd_eq_one]
  have hAcast : (A.natAbs : ℤ) = A := by
    rw [Int.natCast_natAbs, abs_of_pos hA]
  have hCcast : (C.natAbs : ℤ) = C := by
    rw [Int.natCast_natAbs, abs_of_pos hC]
  have hsumNat : A.natAbs + C.natAbs = p := by
    have hsumCast :
        (A.natAbs : ℤ) + (C.natAbs : ℤ) = (p : ℤ) := by
      rw [hAcast, hCcast, hsum]
    exact_mod_cast hsumCast
  let g := Nat.gcd A.natAbs C.natAbs
  have hgA : g ∣ A.natAbs := Nat.gcd_dvd_left _ _
  have hgC : g ∣ C.natAbs := Nat.gcd_dvd_right _ _
  have hgp : g ∣ p := by
    rw [← hsumNat]
    exact Nat.dvd_add hgA hgC
  rcases hp.eq_one_or_self_of_dvd g hgp with hg | hg
  · exact hg
  · have hCpos : 0 < C.natAbs := Int.natAbs_pos.mpr (ne_of_gt hC)
    have hAlt : A.natAbs < p := by omega
    have hgLeA : g ≤ A.natAbs := Nat.le_of_dvd
      (Int.natAbs_pos.mpr (ne_of_gt hA)) hgA
    omega

/-- The two positive normalization weights are coprime.  Their only possible
common divisor divides their prime sum, while neither weight reaches the sum. -/
theorem primitive_spinor_weights_coprime
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2)
    (hprimitive : reduceTriple (p := p) m ≠ (0, 0, 0)) :
    Nat.Coprime (spinorNorthWeight p m).natAbs
      (spinorSouthWeight p m).natAbs := by
  rcases primitive_spinor_normalization_data hp2 hnorm hprimitive with
    ⟨hN, hS, hsum, _⟩
  exact natAbs_coprime_of_pos_add_prime (Fact.out : p.Prime) hN hS hsum

/-- An addressed factorization of a Gaussian norm product into its two
coprime norm grains.  The four coordinates are retained because they are the
spinor which reconstructs the quaternionic Hopf source. -/
@[ext] structure GaussianSpinorFactorization (A C U V : ℤ) where
  northReal : ℤ
  northImag : ℤ
  southReal : ℤ
  southImag : ℤ
  northNorm : northReal ^ 2 + northImag ^ 2 = A
  southNorm : southReal ^ 2 + southImag ^ 2 = C
  transverseJ : northReal * southImag + northImag * southReal = U
  transverseK : northImag * southImag - northReal * southReal = V

def GaussianSpinorFactorization.source
    {A C U V : ℤ} (split : GaussianSpinorFactorization A C U V) : HamiltonInt :=
  ⟨split.northReal, split.northImag, split.southReal, split.southImag⟩

/-- The normalized factorization reconstructs the exact original primitive
Brandt point, including its winding coordinate. -/
theorem gaussianSpinorFactorization_returns
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2)
    (split : GaussianSpinorFactorization
      (spinorNorthWeight p m) (spinorSouthWeight p m)
      (spinorTransverseJ m) (spinorTransverseK m)) :
    ∃ occurrence : FirstHopfOccurrence p,
      occurrence.source = split.source ∧ occurrence.returnedTriple = m := by
  rcases spinor_half_coordinates hp2 hnorm with ⟨hn, hs, hj, hk⟩
  have hsum : spinorNorthWeight p m + spinorSouthWeight p m = (p : ℤ) := by
    omega
  have hlong :
      hopfLongitudinal split.source = m.2.1 := by
    calc
      hopfLongitudinal split.source =
          (split.northReal ^ 2 + split.northImag ^ 2) -
            (split.southReal ^ 2 + split.southImag ^ 2) := by
              simp [GaussianSpinorFactorization.source, hopfLongitudinal]
              ring
      _ = spinorNorthWeight p m - spinorSouthWeight p m := by
        rw [split.northNorm, split.southNorm]
      _ = m.2.1 := by omega
  have hJ : hopfTransverseJ split.source = spinorTransverseJ m := by
    simpa [GaussianSpinorFactorization.source, hopfTransverseJ] using
      split.transverseJ
  have hK : hopfTransverseK split.source = spinorTransverseK m := by
    simpa [GaussianSpinorFactorization.source, hopfTransverseK] using
      split.transverseK
  have hx : spinorTransverseJ m + spinorTransverseK m = m.1 := by omega
  have hz : spinorTransverseJ m - spinorTransverseK m = 4 * m.2.2 := by omega
  have hsourceNorm : Quaternion.normSq split.source = (p : ℤ) := by
    calc
      Quaternion.normSq split.source =
          (split.northReal ^ 2 + split.northImag ^ 2) +
            (split.southReal ^ 2 + split.southImag ^ 2) := by
              rw [Quaternion.normSq_def']
              simp [GaussianSpinorFactorization.source]
              ring
      _ = spinorNorthWeight p m + spinorSouthWeight p m := by
        rw [split.northNorm, split.southNorm]
      _ = (p : ℤ) := hsum
  let occurrence : FirstHopfOccurrence p :=
    { source := split.source
      winding := m.2.2
      sourceNorm := hsourceNorm
      windingCloses := by rw [hJ, hK, hz] }
  refine ⟨occurrence, rfl, ?_⟩
  apply Prod.ext
  · change hopfTransverseJ split.source + hopfTransverseK split.source = m.1
    rw [hJ, hK, hx]
  · apply Prod.ext
    · exact hlong
    · rfl

/-- A factorization for every primitive point closes the exact finite
reconstruction equality. -/
theorem hopfReconstructionComplete_of_factorizations
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (factor : ∀ m ∈ primitiveFirstPrimeSquarePopulation (p := p),
      GaussianSpinorFactorization
        (spinorNorthWeight p m) (spinorSouthWeight p m)
        (spinorTransverseJ m) (spinorTransverseK m)) :
    HopfReconstructionCompleteAt p := by
  apply Finset.Subset.antisymm primitiveHopfReturnPopulation_subset_primeSquare
  intro m hm
  have hnorm := (mem_firstPrimeSquarePopulation_iff (p := p) m).mp
    (Finset.mem_filter.mp hm).1
  have hprimitive := (Finset.mem_filter.mp hm).2
  rcases gaussianSpinorFactorization_returns hp2 hnorm (factor m hm) with
    ⟨occurrence, hsource, hreturn⟩
  have hsourceMem : occurrence.source ∈ firstHopfSourcePopulation p := by
    rw [mem_firstHopfSourcePopulation_iff (Fact.out : p.Prime).pos]
    exact ⟨occurrence.sourceNorm, ⟨occurrence.winding, by
      unfold hopfWindingDifference
      exact occurrence.windingCloses⟩⟩
  have hreturned : hopfReturnedTriple occurrence.source = m := by
    rw [← hreturn]
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · change
          (hopfTransverseJ occurrence.source -
              hopfTransverseK occurrence.source) / 4 = occurrence.winding
        rw [occurrence.windingCloses]
        simp
  apply Finset.mem_image.mpr
  refine ⟨occurrence.source, Finset.mem_filter.mpr ⟨hsourceMem, ?_⟩, hreturned⟩
  rw [hreturned]
  exact hprimitive

/-- **Coprime Gaussian descent.**  A rank-one integral Hermitian matrix

`[[A, -V + iU], [-V - iU, C]]`

with positive coprime diagonal entries is the outer product of an integral
Gaussian spinor.  The construction is explicit: take the Gaussian gcd of
`-V + iU` with `A`; Bézout's identity forces the gcd norm to be exactly `A`,
and the complementary quotient then has norm exactly `C`.

This is the missing normalization theorem, proved here as an integral
factorization rather than postulated as a representation hypothesis. -/
theorem gaussianSpinorFactorization_nonempty_of_coprime
    {A C U V : ℤ} (hA : 0 < A) (hC : 0 < C)
    (hcoprime : Nat.Coprime A.natAbs C.natAbs)
    (hnorm : U ^ 2 + V ^ 2 = A * C) :
    Nonempty (GaussianSpinorFactorization A C U V) := by
  let z : ℤ[i] := ⟨-V, U⟩
  let north : ℤ[i] :=
    EuclideanDomain.gcd z ((A.natAbs : ℕ) : ℤ[i])
  have hAcast : (A.natAbs : ℤ) = A := by
    rw [Int.natCast_natAbs, abs_of_pos hA]
  have hCcast : (C.natAbs : ℤ) = C := by
    rw [Int.natCast_natAbs, abs_of_pos hC]
  have hznorm : z.norm = (A.natAbs : ℤ) * C.natAbs := by
    rw [Zsqrtd.norm_def]
    dsimp [z]
    rw [hAcast, hCcast]
    nlinarith
  have hnorthNorm : north.norm = A := by
    change (EuclideanDomain.gcd z ((A.natAbs : ℕ) : ℤ[i])).norm = A
    rw [← hAcast]
    exact HeckeEuler.norm_gcd_eq hcoprime hznorm
  have hnorthDvd : north ∣ z := by
    exact EuclideanDomain.gcd_dvd_left _ _
  obtain ⟨south, hsouth⟩ := hnorthDvd
  have hproduct : north * south = z := hsouth.symm
  have hAne : A ≠ 0 := ne_of_gt hA
  have hsouthNorm : south.norm = C := by
    have h := congrArg Zsqrtd.norm hproduct
    rw [Zsqrtd.norm_mul, hnorthNorm, hznorm, hAcast, hCcast] at h
    exact mul_left_cancel₀ hAne h
  have hreal := congrArg Zsqrtd.re hproduct
  have himag := congrArg Zsqrtd.im hproduct
  rw [Zsqrtd.re_mul] at hreal
  rw [Zsqrtd.im_mul] at himag
  have hreal' : north.re * south.re - north.im * south.im = -V := by
    simpa [z, sub_eq_add_neg] using hreal
  have himag' : north.re * south.im + north.im * south.re = U := by
    simpa [z] using himag
  refine ⟨
    { northReal := north.re
      northImag := north.im
      southReal := south.re
      southImag := south.im
      northNorm := ?_
      southNorm := ?_
      transverseJ := ?_
      transverseK := ?_ }⟩
  · rw [← hnorthNorm, Zsqrtd.norm_def]
    ring
  · rw [← hsouthNorm, Zsqrtd.norm_def]
    ring
  · exact himag'
  · linarith

/-- Every primitive point of the first prime-square Brandt shell has an
integral Hopf-spinor antecedent.  Positivity and coprimality come from the
prime longitudinal split; Gaussian descent supplies the antecedent. -/
theorem primitive_gaussianSpinorFactorization_nonempty
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : IntTriple}
    (hm : m ∈ primitiveFirstPrimeSquarePopulation (p := p)) :
    Nonempty (GaussianSpinorFactorization
      (spinorNorthWeight p m) (spinorSouthWeight p m)
      (spinorTransverseJ m) (spinorTransverseK m)) := by
  have hnorm := (mem_firstPrimeSquarePopulation_iff (p := p) m).mp
    (Finset.mem_filter.mp hm).1
  have hprimitive := (Finset.mem_filter.mp hm).2
  rcases primitive_spinor_normalization_data hp2 hnorm hprimitive with
    ⟨hN, hS, _, hdet⟩
  exact gaussianSpinorFactorization_nonempty_of_coprime hN hS
    (primitive_spinor_weights_coprime hp2 hnorm hprimitive) hdet

/-- **Exact reconstruction closure.**  For every odd prime, the finite
quaternionic Hopf receiver returns precisely the complete primitive first
Brandt prime-square population.  No representation hypothesis remains. -/
theorem hopfReconstructionComplete
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    HopfReconstructionCompleteAt p := by
  apply hopfReconstructionComplete_of_factorizations hp2
  intro m hm
  exact Classical.choice
    (primitive_gaussianSpinorFactorization_nonempty hp2 hm)

#print axioms mem_hamiltonBox_of_norm
#print axioms mem_firstHopfSourcePopulation_iff
#print axioms phaseTurn_mem_firstHopfSourcePopulation
#print axioms hopfReturnedTriple_phaseTurn
#print axioms hopfReturnedTriple_mem_firstPrimeSquarePopulation
#print axioms primitiveHopfSourceFibre_eq_phaseOrbit
#print axioms hopfPhaseOrbit_card_of_norm_pos
#print axioms primitiveHopfSourceFibre_card
#print axioms primitiveHopfSourcePopulation_card_eq_four_mul_return_card
#print axioms primitiveHopfReturnPopulation_subset_primeSquare
#print axioms primitiveHopfSourcePopulation_card_of_reconstruction
#print axioms primeSquare_longitudinal_odd
#print axioms primeSquare_first_even
#print axioms spinor_half_coordinates
#print axioms primitive_longitudinal_strict
#print axioms primitive_spinor_normalization_data
#print axioms primitive_spinor_weights_coprime
#print axioms gaussianSpinorFactorization_returns
#print axioms hopfReconstructionComplete_of_factorizations
#print axioms gaussianSpinorFactorization_nonempty_of_coprime
#print axioms primitive_gaussianSpinorFactorization_nonempty
#print axioms hopfReconstructionComplete

end Soma.Holonics.Millennium.FamilyTunnellHopfSourceCensus

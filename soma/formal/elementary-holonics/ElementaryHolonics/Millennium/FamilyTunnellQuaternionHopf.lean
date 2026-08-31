import ElementaryHolonics.Millennium.FamilyTunnellQuaternionicBridge
import ElementaryHolonics.Millennium.FamilyTunnellPrimeSquareCensus

/-!
# The integral Hopf source of the first Tunnell--Brandt prime-square fibre

The first Brandt equation

`2x² + y² + 32z² = p²`

is not introduced here as an isolated ternary coincidence.  For an integral
Hamilton quaternion `α = a + bi + cj + dk`, conjugation of the fixed pivot `i`
returns the pure quaternion

`α i ᾱ = (a²+b²-c²-d²)i + 2(ad+bc)j + 2(bd-ac)k`.

Its norm is exactly `N(α)²`.  The first Brandt lattice is the addressed slice
on which the difference of the two transverse half-coordinates is a multiple
of four.  Retaining that quotient as `z` gives

`x = (ad+bc) + (bd-ac)`,
`y = a²+b²-c²-d²`,
`z = ((ad+bc)-(bd-ac))/4`.

This file constructs that source occurrence and proves that it lands in the
complete prime-square population.  It also constructs the four-phase source
turn given by right multiplication by `i`; the complete ternary return is
invariant under that turn.  Thus the familiar fourfold Hopf fibre is already
an actual causal symmetry of the source carrier, not a cardinality heuristic.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellQuaternionHopf

open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellPrimeSquareCensus

/-! ## The integral Hopf swing -/

/-- The longitudinal coefficient returned by conjugating the pivot `i`. -/
def hopfLongitudinal (α : HamiltonInt) : ℤ :=
  α.re ^ 2 + α.imI ^ 2 - α.imJ ^ 2 - α.imK ^ 2

/-- First transverse half-coefficient of the Hopf return. -/
def hopfTransverseJ (α : HamiltonInt) : ℤ :=
  α.re * α.imK + α.imI * α.imJ

/-- Second transverse half-coefficient of the Hopf return. -/
def hopfTransverseK (α : HamiltonInt) : ℤ :=
  α.imI * α.imK - α.re * α.imJ

/-- The integral Hopf return `α i ᾱ`, retained in pure quaternion coordinates. -/
def hopfPivotReturn (α : HamiltonInt) : HamiltonInt :=
  ⟨0, hopfLongitudinal α, 2 * hopfTransverseJ α,
    2 * hopfTransverseK α⟩

/-- The fixed quaternionic pivot. -/
def hopfPivot : HamiltonInt := ⟨0, 1, 0, 0⟩

/-- The coordinate return really is quaternionic conjugation of the pivot. -/
theorem hopfPivotReturn_eq_mul (α : HamiltonInt) :
    hopfPivotReturn α = α * hopfPivot * star α := by
  apply Quaternion.ext <;>
    simp [hopfPivotReturn, hopfPivot, hopfLongitudinal,
      hopfTransverseJ, hopfTransverseK] <;> ring

@[simp] theorem hopfPivotReturn_re (α : HamiltonInt) :
    (hopfPivotReturn α).re = 0 := rfl

/-- **THE HOPF SWING SQUARES THE SOURCE NORM.** -/
theorem normSq_hopfPivotReturn (α : HamiltonInt) :
    Quaternion.normSq (hopfPivotReturn α) =
      Quaternion.normSq α ^ 2 := by
  rw [Quaternion.normSq_def', Quaternion.normSq_def']
  simp [hopfPivotReturn, hopfLongitudinal, hopfTransverseJ,
    hopfTransverseK]
  ring

/-! ## The addressed first-lattice slice -/

/-- A source quaternion together with the retained transverse winding quotient.
The equality, rather than bare divisibility, preserves the reconstruction
coordinate deleted by writing `/ 4`. -/
@[ext] structure FirstHopfOccurrence (p : ℕ) where
  source : HamiltonInt
  winding : ℤ
  sourceNorm : Quaternion.normSq source = (p : ℤ)
  windingCloses :
    hopfTransverseJ source - hopfTransverseK source = 4 * winding

/-- The first Brandt coordinates returned by one Hopf source occurrence. -/
def FirstHopfOccurrence.returnedTriple {p : ℕ}
    (occurrence : FirstHopfOccurrence p) : IntTriple :=
  (hopfTransverseJ occurrence.source + hopfTransverseK occurrence.source,
    (hopfLongitudinal occurrence.source, occurrence.winding))

/-- The retained winding equation places the Hopf return in the first Brandt
quaternion lattice exactly. -/
theorem firstBrandtQuaternion_returnedTriple {p : ℕ}
    (occurrence : FirstHopfOccurrence p) :
    firstBrandtQuaternion occurrence.returnedTriple =
      hopfPivotReturn occurrence.source := by
  apply Quaternion.ext
  · rfl
  · simp [FirstHopfOccurrence.returnedTriple, firstBrandtQuaternion,
      hopfPivotReturn]
  · simp [FirstHopfOccurrence.returnedTriple, firstBrandtQuaternion,
      hopfPivotReturn]
    linarith [occurrence.windingCloses]
  · simp [FirstHopfOccurrence.returnedTriple, firstBrandtQuaternion,
      hopfPivotReturn]
    linarith [occurrence.windingCloses]

/-- Every norm-`p` Hopf occurrence returns an exact first-lattice point of norm
`p²`. -/
theorem brandtFirstQuadratic_returnedTriple {p : ℕ}
    (occurrence : FirstHopfOccurrence p) :
    brandtFirstQuadratic occurrence.returnedTriple = (p : ℤ) ^ 2 := by
  rw [← normSq_firstBrandtQuaternion,
    firstBrandtQuaternion_returnedTriple, normSq_hopfPivotReturn,
    occurrence.sourceNorm]

/-- At a prime, the returned triple is an actual member of the already-owned
complete prime-square population. -/
theorem returnedTriple_mem_firstPrimeSquarePopulation
    {p : ℕ} [Fact p.Prime] (occurrence : FirstHopfOccurrence p) :
    occurrence.returnedTriple ∈ firstPrimeSquarePopulation (p := p) := by
  rw [mem_firstPrimeSquarePopulation_iff]
  exact brandtFirstQuadratic_returnedTriple occurrence

/-! ## The four-phase stabilizer of the pivot -/

/-- Right multiplication by `i` in coordinates. -/
def hopfPhaseTurnSource (α : HamiltonInt) : HamiltonInt :=
  ⟨-α.imI, α.re, α.imK, -α.imJ⟩

/-- The phase turn is exactly the quaternion product `α i`. -/
theorem hopfPhaseTurnSource_eq_mul (α : HamiltonInt) :
    hopfPhaseTurnSource α = α * hopfPivot := by
  apply Quaternion.ext <;>
    simp [hopfPhaseTurnSource, hopfPivot]

/-- Conjugating the pivot is invariant under one phase turn. -/
theorem hopfPivotReturn_phaseTurn (α : HamiltonInt) :
    hopfPivotReturn (hopfPhaseTurnSource α) = hopfPivotReturn α := by
  apply Quaternion.ext <;>
    simp [hopfPivotReturn, hopfPhaseTurnSource, hopfLongitudinal,
      hopfTransverseJ, hopfTransverseK] <;> ring

theorem normSq_hopfPhaseTurnSource (α : HamiltonInt) :
    Quaternion.normSq (hopfPhaseTurnSource α) = Quaternion.normSq α := by
  rw [Quaternion.normSq_def', Quaternion.normSq_def']
  simp [hopfPhaseTurnSource]
  ring

theorem hopfTransverseDifference_phaseTurn (α : HamiltonInt) :
    hopfTransverseJ (hopfPhaseTurnSource α) -
        hopfTransverseK (hopfPhaseTurnSource α) =
      hopfTransverseJ α - hopfTransverseK α := by
  simp [hopfPhaseTurnSource, hopfTransverseJ, hopfTransverseK]
  ring

/-- The phase turn acts on the complete addressed source occurrence without
changing its winding coordinate. -/
def FirstHopfOccurrence.phaseTurn {p : ℕ}
    (occurrence : FirstHopfOccurrence p) : FirstHopfOccurrence p where
  source := hopfPhaseTurnSource occurrence.source
  winding := occurrence.winding
  sourceNorm := by
    rw [normSq_hopfPhaseTurnSource, occurrence.sourceNorm]
  windingCloses := by
    rw [hopfTransverseDifference_phaseTurn]
    exact occurrence.windingCloses

/-- One phase turn is invisible to the complete first-lattice receiver. -/
theorem FirstHopfOccurrence.returnedTriple_phaseTurn {p : ℕ}
    (occurrence : FirstHopfOccurrence p) :
    occurrence.phaseTurn.returnedTriple = occurrence.returnedTriple := by
  apply Prod.ext
  · simp [FirstHopfOccurrence.returnedTriple, FirstHopfOccurrence.phaseTurn,
      hopfPhaseTurnSource, hopfTransverseJ, hopfTransverseK]
    ring
  · apply Prod.ext
    · simp [FirstHopfOccurrence.returnedTriple, FirstHopfOccurrence.phaseTurn,
        hopfPhaseTurnSource, hopfLongitudinal]
      ring
    · rfl

/-- Two phase turns negate the source quaternion. -/
theorem hopfPhaseTurnSource_twice (α : HamiltonInt) :
    hopfPhaseTurnSource (hopfPhaseTurnSource α) = -α := by
  apply Quaternion.ext <;> simp [hopfPhaseTurnSource]

/-- Four phase turns return the exact source occurrence. -/
theorem FirstHopfOccurrence.phaseTurn_four {p : ℕ}
    (occurrence : FirstHopfOccurrence p) :
    occurrence.phaseTurn.phaseTurn.phaseTurn.phaseTurn = occurrence := by
  cases occurrence with
  | mk source winding sourceNorm windingCloses =>
      apply FirstHopfOccurrence.ext <;>
        simp [FirstHopfOccurrence.phaseTurn, hopfPhaseTurnSource]

/-- At positive norm, the phase swing has no fixed source. -/
theorem FirstHopfOccurrence.phaseTurn_ne_self
    {p : ℕ} (hp : 0 < p) (occurrence : FirstHopfOccurrence p) :
    occurrence.phaseTurn ≠ occurrence := by
  intro h
  have hs : hopfPhaseTurnSource occurrence.source = occurrence.source :=
    congrArg FirstHopfOccurrence.source h
  have hre := congrArg QuaternionAlgebra.re hs
  have hi := congrArg QuaternionAlgebra.imI hs
  have hj := congrArg QuaternionAlgebra.imJ hs
  have hk := congrArg QuaternionAlgebra.imK hs
  simp [hopfPhaseTurnSource] at hre hi hj hk
  have hz : occurrence.source = 0 := by
    apply Quaternion.ext <;> simp <;> omega
  have hnorm := occurrence.sourceNorm
  rw [hz] at hnorm
  simp at hnorm
  exact (Nat.ne_of_gt hp) (by exact_mod_cast hnorm.symm)

/-! ## Exact north/south reconstruction before norm condensation -/

/-- The north-chart integral rotor of a first-lattice point.  In coordinates it
is the standard spinor `(p+y,0,-K,J)` for the pure sphere point `(y,J,K)`. -/
def northHopfSource (p : ℕ) (m : IntTriple) : HamiltonInt :=
  let q := firstBrandtQuaternion m
  ⟨(p : ℤ) + q.imI, 0, -q.imK, q.imJ⟩

def northHopfScale (p : ℕ) (m : IntTriple) : ℤ :=
  2 * ((p : ℤ) + (firstBrandtQuaternion m).imI)

/-- The south chart covers the north pole's missing antipode. -/
def southHopfSource (p : ℕ) (m : IntTriple) : HamiltonInt :=
  let q := firstBrandtQuaternion m
  ⟨0, (p : ℤ) - q.imI, -q.imJ, -q.imK⟩

def southHopfScale (p : ℕ) (m : IntTriple) : ℤ :=
  -2 * ((p : ℤ) - (firstBrandtQuaternion m).imI)

/-- Coordinate scaling in the integral Hamilton chart.  This avoids collapsing
the source scale into an ambient module inference. -/
def scaleHamilton (s : ℤ) (q : HamiltonInt) : HamiltonInt :=
  ⟨s * q.re, s * q.imI, s * q.imJ, s * q.imK⟩

/-- The north rotor sends the pivot to the original sphere point multiplied by
the exact chart scale. -/
theorem hopfPivotReturn_northHopfSource {p : ℕ} {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) :
    hopfPivotReturn (northHopfSource p m) =
      scaleHamilton (northHopfScale p m) (firstBrandtQuaternion m) := by
  have hsphere :
      (firstBrandtQuaternion m).imI ^ 2 +
          (firstBrandtQuaternion m).imJ ^ 2 +
          (firstBrandtQuaternion m).imK ^ 2 = (p : ℤ) ^ 2 := by
    calc
      _ = Quaternion.normSq (firstBrandtQuaternion m) := by
        rw [Quaternion.normSq_def']
        simp
      _ = brandtFirstQuadratic m := normSq_firstBrandtQuaternion m
      _ = (p : ℤ) ^ 2 := hnorm
  apply Quaternion.ext <;>
    simp [northHopfSource, northHopfScale, hopfPivotReturn,
      scaleHamilton, hopfLongitudinal, hopfTransverseJ, hopfTransverseK] <;>
    nlinarith

/-- The south rotor gives the complementary exact chart. -/
theorem hopfPivotReturn_southHopfSource {p : ℕ} {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) :
    hopfPivotReturn (southHopfSource p m) =
      scaleHamilton (southHopfScale p m) (firstBrandtQuaternion m) := by
  have hsphere :
      (firstBrandtQuaternion m).imI ^ 2 +
          (firstBrandtQuaternion m).imJ ^ 2 +
          (firstBrandtQuaternion m).imK ^ 2 = (p : ℤ) ^ 2 := by
    calc
      _ = Quaternion.normSq (firstBrandtQuaternion m) := by
        rw [Quaternion.normSq_def']
        simp
      _ = brandtFirstQuadratic m := normSq_firstBrandtQuaternion m
      _ = (p : ℤ) ^ 2 := hnorm
  apply Quaternion.ext <;>
    simp [southHopfSource, southHopfScale, hopfPivotReturn,
      scaleHamilton, hopfLongitudinal, hopfTransverseJ, hopfTransverseK] <;>
    nlinarith

/-- The north rotor norm records the complete scale needed to normalize it to a
norm-`p` spinor. -/
theorem normSq_northHopfSource {p : ℕ} {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) :
    Quaternion.normSq (northHopfSource p m) =
      (p : ℤ) * northHopfScale p m := by
  have hsphere :
      (firstBrandtQuaternion m).imI ^ 2 +
          (firstBrandtQuaternion m).imJ ^ 2 +
          (firstBrandtQuaternion m).imK ^ 2 = (p : ℤ) ^ 2 := by
    calc
      _ = Quaternion.normSq (firstBrandtQuaternion m) := by
        rw [Quaternion.normSq_def']
        simp
      _ = brandtFirstQuadratic m := normSq_firstBrandtQuaternion m
      _ = (p : ℤ) ^ 2 := hnorm
  rw [Quaternion.normSq_def']
  simp [northHopfSource, northHopfScale]
  nlinarith

/-- Select the chart whose scale is nonzero. -/
def projectiveHopfSource (p : ℕ) (m : IntTriple) : HamiltonInt :=
  if (p : ℤ) + (firstBrandtQuaternion m).imI ≠ 0 then
    northHopfSource p m
  else
    southHopfSource p m

def projectiveHopfScale (p : ℕ) (m : IntTriple) : ℤ :=
  if (p : ℤ) + (firstBrandtQuaternion m).imI ≠ 0 then
    northHopfScale p m
  else
    southHopfScale p m

/-- Every first-lattice prime-square occurrence has an explicit integral Hopf
predecessor after retaining one nonzero scalar chart coordinate. -/
theorem hopfPivotReturn_projectiveHopfSource {p : ℕ} {m : IntTriple}
    (hnorm : brandtFirstQuadratic m = (p : ℤ) ^ 2) :
    hopfPivotReturn (projectiveHopfSource p m) =
      scaleHamilton (projectiveHopfScale p m) (firstBrandtQuaternion m) := by
  by_cases hchart : (p : ℤ) + (firstBrandtQuaternion m).imI ≠ 0
  · simp [projectiveHopfSource, projectiveHopfScale, hchart,
      hopfPivotReturn_northHopfSource hnorm]
  · simp [projectiveHopfSource, projectiveHopfScale, hchart,
      hopfPivotReturn_southHopfSource hnorm]

/-- For positive radius, the selected projective Hopf scale cannot vanish. -/
theorem projectiveHopfScale_ne_zero {p : ℕ} (hp : 0 < p) (m : IntTriple) :
    projectiveHopfScale p m ≠ 0 := by
  by_cases hchart : (p : ℤ) + (firstBrandtQuaternion m).imI ≠ 0
  · simp [projectiveHopfScale, hchart, northHopfScale, hchart]
  · have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
    have hchart' : (p : ℤ) + (firstBrandtQuaternion m).imI = 0 :=
      not_ne_iff.mp hchart
    simp only [projectiveHopfScale, if_neg hchart, southHopfScale]
    intro hzero
    have hy : (firstBrandtQuaternion m).imI = -(p : ℤ) := by
      linarith [hchart']
    rw [hy] at hzero
    nlinarith

/-! ## Exact phase-fibre separation -/

/-- Relative transport between two quaternionic source occurrences. -/
def hopfRelative (α β : HamiltonInt) : HamiltonInt := star α * β

/-- Equal Hopf returns force the relative transport to commute with the pivot.
The proof keeps the norm factor `p` until its nonzero coordinate cancellation. -/
theorem hopfRelative_commutes_with_pivot {p : ℕ} (hp : 0 < p)
    {α β : HamiltonInt}
    (hα : Quaternion.normSq α = (p : ℤ))
    (hβ : Quaternion.normSq β = (p : ℤ))
    (hreturn : hopfPivotReturn α = hopfPivotReturn β) :
    hopfPivot * hopfRelative α β = hopfRelative α β * hopfPivot := by
  have hmul := congrArg (fun q : HamiltonInt => star α * q * β) hreturn
  rw [hopfPivotReturn_eq_mul, hopfPivotReturn_eq_mul] at hmul
  have hscaled :
      ((p : ℤ) : HamiltonInt) * (hopfPivot * hopfRelative α β) =
        ((p : ℤ) : HamiltonInt) * (hopfRelative α β * hopfPivot) := by
    calc
      ((p : ℤ) : HamiltonInt) * (hopfPivot * hopfRelative α β) =
          (star α * α) * (hopfPivot * (star α * β)) := by
            rw [Quaternion.star_mul_self, hα]
            rfl
      _ = star α * (α * hopfPivot * star α) * β := by
            noncomm_ring
      _ = star α * (β * hopfPivot * star β) * β := hmul
      _ = (star α * β) * hopfPivot * (star β * β) := by
            noncomm_ring
      _ = ((p : ℤ) : HamiltonInt) * (hopfRelative α β * hopfPivot) := by
            rw [Quaternion.star_mul_self, hβ]
            rw [← Quaternion.coe_commutes]
            rfl
  have hpQ : ((p : ℤ) : HamiltonInt) ≠ 0 := by
    intro hzero
    have hre := congrArg QuaternionAlgebra.re hzero
    simp at hre
    exact (Nat.ne_of_gt hp) (by exact_mod_cast hre)
  exact mul_left_cancel₀ hpQ hscaled

/-- Therefore the relative transport has no `j` or `k` component. -/
theorem hopfRelative_transverse_eq_zero {p : ℕ} (hp : 0 < p)
    {α β : HamiltonInt}
    (hα : Quaternion.normSq α = (p : ℤ))
    (hβ : Quaternion.normSq β = (p : ℤ))
    (hreturn : hopfPivotReturn α = hopfPivotReturn β) :
    (hopfRelative α β).imJ = 0 ∧ (hopfRelative α β).imK = 0 := by
  have hcomm := hopfRelative_commutes_with_pivot hp hα hβ hreturn
  constructor
  · have h := congrArg QuaternionAlgebra.imK hcomm
    simp [hopfPivot] at h
    omega
  · have h := congrArg QuaternionAlgebra.imJ hcomm
    simp [hopfPivot] at h
    omega

/-- Multiplying back by the source recovers the target with the source norm as
the retained scalar. -/
theorem source_mul_hopfRelative (α β : HamiltonInt) :
    α * hopfRelative α β =
      ((Quaternion.normSq α : ℤ) : HamiltonInt) * β := by
  rw [hopfRelative]
  rw [← mul_assoc, Quaternion.self_mul_star]
  rfl

/-- The norm of the relative transport is the product of the two source norms. -/
theorem normSq_hopfRelative (α β : HamiltonInt) :
    Quaternion.normSq (hopfRelative α β) =
      Quaternion.normSq α * Quaternion.normSq β := by
  rw [hopfRelative, map_mul, Quaternion.normSq_star]

private theorem two_zmod_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) ≠ 0 := by
  apply Ring.two_ne_zero
  rw [ZMod.ringChar_zmod_n]
  exact hp2

private theorem eight_zmod_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    (8 : ZMod p) ≠ 0 := by
  rw [show (8 : ZMod p) = 2 ^ 3 by norm_num]
  exact pow_ne_zero 3 (two_zmod_ne_zero hp2)

/-- If every pure coordinate of a first Brandt quaternion vanishes modulo `p`,
then the complete ternary address vanishes.  The factors `2` and `8` are
cancelled explicitly at the odd-prime aperture. -/
theorem reduceTriple_eq_zero_of_firstBrandtQuaternion
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (m : IntTriple)
    (hi : ((firstBrandtQuaternion m).imI : ZMod p) = 0)
    (hj : ((firstBrandtQuaternion m).imJ : ZMod p) = 0)
    (hk : ((firstBrandtQuaternion m).imK : ZMod p) = 0) :
    reduceTriple (p := p) m = (0, 0, 0) := by
  have hy : (m.2.1 : ZMod p) = 0 := by
    simpa [firstBrandtQuaternion] using hi
  have hx2 : (2 : ZMod p) * (m.1 : ZMod p) = 0 := by
    have hsum :
        ((firstBrandtQuaternion m).imJ : ZMod p) +
            ((firstBrandtQuaternion m).imK : ZMod p) = 0 := by
      rw [hj, hk]
      ring
    convert hsum using 1 <;> simp [firstBrandtQuaternion] <;> ring
  have hx : (m.1 : ZMod p) = 0 :=
    (mul_eq_zero.mp hx2).resolve_left (two_zmod_ne_zero hp2)
  have hz8 : (8 : ZMod p) * (m.2.2 : ZMod p) = 0 := by
    have hsub :
        ((firstBrandtQuaternion m).imJ : ZMod p) -
            ((firstBrandtQuaternion m).imK : ZMod p) = 0 := by
      rw [hj, hk]
      ring
    convert hsub using 1 <;> simp [firstBrandtQuaternion] <;> ring
  have hz : (m.2.2 : ZMod p) = 0 :=
    (mul_eq_zero.mp hz8).resolve_left (eight_zmod_ne_zero hp2)
  apply Prod.ext
  · simpa [reduceTriple] using hx
  · apply Prod.ext
    · simpa [reduceTriple] using hy
    · simpa [reduceTriple] using hz

/-- On a primitive returned point, equal norm-`p` Hopf sources can differ only
by a relative phase whose two coordinates are both divisible by `p`.  If a
nonzero relative phase survived modulo `p`, the four product incidences would
force every coordinate of the returned pure quaternion to vanish modulo `p`,
contradicting the retained primitive address. -/
theorem hopfRelative_longitudinal_dvd_of_primitive
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (left right : FirstHopfOccurrence p)
    (hreturned : left.returnedTriple = right.returnedTriple)
    (hprimitive : reduceTriple (p := p) left.returnedTriple ≠ (0, 0, 0)) :
    (p : ℤ) ∣ (hopfRelative left.source right.source).re ∧
      (p : ℤ) ∣ (hopfRelative left.source right.source).imI := by
  let u := hopfRelative left.source right.source
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hhopf : hopfPivotReturn left.source = hopfPivotReturn right.source := by
    calc
      hopfPivotReturn left.source = firstBrandtQuaternion left.returnedTriple :=
        (firstBrandtQuaternion_returnedTriple left).symm
      _ = firstBrandtQuaternion right.returnedTriple := by rw [hreturned]
      _ = hopfPivotReturn right.source := firstBrandtQuaternion_returnedTriple right
  obtain ⟨huJ, huK⟩ := hopfRelative_transverse_eq_zero hp
    left.sourceNorm right.sourceNorm hhopf
  change u.imJ = 0 at huJ
  change u.imK = 0 at huK
  have hunorm : Quaternion.normSq u = (p : ℤ) ^ 2 := by
    change Quaternion.normSq (hopfRelative left.source right.source) = _
    rw [normSq_hopfRelative, left.sourceNorm, right.sourceNorm]
    ring
  have hcircleZ : u.re ^ 2 + u.imI ^ 2 = (p : ℤ) ^ 2 := by
    rw [Quaternion.normSq_def'] at hunorm
    simpa [huJ, huK] using hunorm
  by_contra hnot
  change ¬((p : ℤ) ∣ u.re ∧ (p : ℤ) ∣ u.imI) at hnot
  have hcircle : (u.re : ZMod p) ^ 2 + (u.imI : ZMod p) ^ 2 = 0 := by
    have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hcircleZ
    push_cast at hcast
    simpa using hcast
  have hur : (u.re : ZMod p) ≠ 0 := by
    intro hur0
    have hui0 : (u.imI : ZMod p) = 0 := by
      rw [hur0] at hcircle
      simp at hcircle
      exact hcircle
    apply hnot
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd u.re p).mp hur0,
      (ZMod.intCast_zmod_eq_zero_iff_dvd u.imI p).mp hui0⟩
  have hprod :
      left.source * u = ((p : ℤ) : HamiltonInt) * right.source := by
    change left.source * hopfRelative left.source right.source = _
    rw [source_mul_hopfRelative, left.sourceNorm]
  have hprodReZ := congrArg QuaternionAlgebra.re hprod
  have hprodIZ := congrArg QuaternionAlgebra.imI hprod
  have hprodJZ := congrArg QuaternionAlgebra.imJ hprod
  have hprodKZ := congrArg QuaternionAlgebra.imK hprod
  have hprodRe := congrArg (fun z : ℤ => (z : ZMod p)) hprodReZ
  have hprodI := congrArg (fun z : ℤ => (z : ZMod p)) hprodIZ
  have hprodJ := congrArg (fun z : ℤ => (z : ZMod p)) hprodJZ
  have hprodK := congrArg (fun z : ℤ => (z : ZMod p)) hprodKZ
  simp [huJ, huK] at hprodRe hprodI hprodJ hprodK
  have hReEq :
      (left.source.re : ZMod p) * (u.re : ZMod p) =
        (left.source.imI : ZMod p) * (u.imI : ZMod p) := by
    linear_combination hprodRe
  have hIEq :
      (left.source.imI : ZMod p) * (u.re : ZMod p) +
        (left.source.re : ZMod p) * (u.imI : ZMod p) = 0 := by
    linear_combination hprodI
  have hJEq :
      (left.source.imJ : ZMod p) * (u.re : ZMod p) =
        -(left.source.imK : ZMod p) * (u.imI : ZMod p) := by
    linear_combination hprodJ
  have hJEqZero :
      (left.source.imJ : ZMod p) * (u.re : ZMod p) +
        (left.source.imK : ZMod p) * (u.imI : ZMod p) = 0 := hprodJ
  have hcircle' : (u.imI : ZMod p) ^ 2 + (u.re : ZMod p) ^ 2 = 0 := by
    linear_combination hcircle
  have hlongScaled :
      (u.re : ZMod p) ^ 2 *
          (hopfLongitudinal left.source : ZMod p) = 0 := by
    calc
      (u.re : ZMod p) ^ 2 *
          (hopfLongitudinal left.source : ZMod p) =
          ((left.source.re : ZMod p) * (u.re : ZMod p)) ^ 2 +
            ((left.source.imI : ZMod p) * (u.re : ZMod p)) ^ 2 -
            ((left.source.imJ : ZMod p) * (u.re : ZMod p)) ^ 2 -
            ((left.source.imK : ZMod p) * (u.re : ZMod p)) ^ 2 := by
              simp [hopfLongitudinal]
              ring
      _ = ((left.source.imI : ZMod p) * (u.imI : ZMod p)) ^ 2 +
            ((left.source.imI : ZMod p) * (u.re : ZMod p)) ^ 2 -
            (-(left.source.imK : ZMod p) * (u.imI : ZMod p)) ^ 2 -
            ((left.source.imK : ZMod p) * (u.re : ZMod p)) ^ 2 := by
              rw [hReEq, hJEq]
      _ = 0 := by
            calc
              _ = (left.source.imI : ZMod p) ^ 2 *
                    ((u.imI : ZMod p) ^ 2 + (u.re : ZMod p) ^ 2) -
                  (left.source.imK : ZMod p) ^ 2 *
                    ((u.imI : ZMod p) ^ 2 + (u.re : ZMod p) ^ 2) := by ring
              _ = 0 := by rw [hcircle']; ring
  have hlong : (hopfLongitudinal left.source : ZMod p) = 0 := by
    exact (mul_eq_zero.mp hlongScaled).resolve_left (pow_ne_zero 2 hur)
  have hJScaled :
      (u.re : ZMod p) * (hopfTransverseJ left.source : ZMod p) = 0 := by
    calc
      _ = (left.source.imK : ZMod p) *
              ((left.source.re : ZMod p) * (u.re : ZMod p) -
                (left.source.imI : ZMod p) * (u.imI : ZMod p)) +
            (left.source.imI : ZMod p) *
              ((left.source.imJ : ZMod p) * (u.re : ZMod p) +
                (left.source.imK : ZMod p) * (u.imI : ZMod p)) := by
            simp [hopfTransverseJ]
            ring
      _ = 0 := by rw [hprodRe, hprodJ]; ring
  have hKScaled :
      (u.re : ZMod p) * (hopfTransverseK left.source : ZMod p) = 0 := by
    calc
      _ = (left.source.imK : ZMod p) *
              ((left.source.imI : ZMod p) * (u.re : ZMod p) +
                (left.source.re : ZMod p) * (u.imI : ZMod p)) -
            (left.source.re : ZMod p) *
              ((left.source.imJ : ZMod p) * (u.re : ZMod p) +
                (left.source.imK : ZMod p) * (u.imI : ZMod p)) := by
            simp [hopfTransverseK]
            ring
      _ = 0 := by rw [hIEq, hJEqZero]; ring
  have hJ : (hopfTransverseJ left.source : ZMod p) = 0 :=
    (mul_eq_zero.mp hJScaled).resolve_left hur
  have hK : (hopfTransverseK left.source : ZMod p) = 0 :=
    (mul_eq_zero.mp hKScaled).resolve_left hur
  have hi : ((firstBrandtQuaternion left.returnedTriple).imI : ZMod p) = 0 := by
    rw [firstBrandtQuaternion_returnedTriple]
    simpa [hopfPivotReturn] using hlong
  have hj : ((firstBrandtQuaternion left.returnedTriple).imJ : ZMod p) = 0 := by
    rw [firstBrandtQuaternion_returnedTriple]
    simp [hopfPivotReturn, hJ]
  have hk : ((firstBrandtQuaternion left.returnedTriple).imK : ZMod p) = 0 := by
    rw [firstBrandtQuaternion_returnedTriple]
    simp [hopfPivotReturn, hK]
  exact hprimitive
    (reduceTriple_eq_zero_of_firstBrandtQuaternion hp2 left.returnedTriple hi hj hk)

private theorem int_sq_add_sq_eq_one_cases (r s : ℤ)
    (h : r ^ 2 + s ^ 2 = 1) :
    (r = 1 ∧ s = 0) ∨ (r = 0 ∧ s = 1) ∨
      (r = -1 ∧ s = 0) ∨ (r = 0 ∧ s = -1) := by
  have hrSqNonneg : 0 ≤ r ^ 2 := sq_nonneg r
  have hsSqNonneg : 0 ≤ s ^ 2 := sq_nonneg s
  have hrSqUpper : r ^ 2 ≤ 1 := by nlinarith
  have hrSqCases : r ^ 2 = 0 ∨ r ^ 2 = 1 := by omega
  rcases hrSqCases with hr0 | hr1
  · have hr : r = 0 := by nlinarith
    have hs1 : s ^ 2 = 1 := by nlinarith
    rcases sq_eq_one_iff.mp hs1 with hs | hs
    · exact Or.inr (Or.inl ⟨hr, hs⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨hr, hs⟩))
  · have hs0 : s = 0 := by nlinarith
    rcases sq_eq_one_iff.mp hr1 with hr | hr
    · exact Or.inl ⟨hr, hs0⟩
    · exact Or.inr (Or.inr (Or.inl ⟨hr, hs0⟩))

/-- **THE PRIMITIVE HOPF FIBRE HAS EXACTLY THE FOUR PIVOT PHASES.**

If two addressed norm-`p` sources return the same primitive first-Brandt
point, their retained relative transport has norm `p²`, is longitudinal, and
has both longitudinal coordinates divisible by `p`.  Dividing that exact
common factor leaves the integral unit circle, whose four points are
`1, i, -1, -i`.  Multiplication back into the source therefore returns one of
the four explicit phase turns; no further source lies in the primitive fibre.
-/
theorem source_eq_phase_of_same_primitive_return
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (left right : FirstHopfOccurrence p)
    (hreturned : left.returnedTriple = right.returnedTriple)
    (hprimitive : reduceTriple (p := p) left.returnedTriple ≠ (0, 0, 0)) :
    right.source = left.source ∨
      right.source = hopfPhaseTurnSource left.source ∨
      right.source = -left.source ∨
      right.source = -hopfPhaseTurnSource left.source := by
  let u := hopfRelative left.source right.source
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hhopf : hopfPivotReturn left.source = hopfPivotReturn right.source := by
    calc
      hopfPivotReturn left.source = firstBrandtQuaternion left.returnedTriple :=
        (firstBrandtQuaternion_returnedTriple left).symm
      _ = firstBrandtQuaternion right.returnedTriple := by rw [hreturned]
      _ = hopfPivotReturn right.source := firstBrandtQuaternion_returnedTriple right
  obtain ⟨huJ, huK⟩ := hopfRelative_transverse_eq_zero hp
    left.sourceNorm right.sourceNorm hhopf
  change u.imJ = 0 at huJ
  change u.imK = 0 at huK
  obtain ⟨⟨r, hr⟩, ⟨s, hs⟩⟩ :=
    hopfRelative_longitudinal_dvd_of_primitive hp2 left right hreturned hprimitive
  change u.re = (p : ℤ) * r at hr
  change u.imI = (p : ℤ) * s at hs
  have hunorm : Quaternion.normSq u = (p : ℤ) ^ 2 := by
    change Quaternion.normSq (hopfRelative left.source right.source) = _
    rw [normSq_hopfRelative, left.sourceNorm, right.sourceNorm]
    ring
  have hrs : r ^ 2 + s ^ 2 = 1 := by
    rw [Quaternion.normSq_def'] at hunorm
    simp [huJ, huK, hr, hs] at hunorm
    have hfactor :
        (p : ℤ) ^ 2 * (r ^ 2 + s ^ 2) = (p : ℤ) ^ 2 * 1 := by
      calc
        (p : ℤ) ^ 2 * (r ^ 2 + s ^ 2) =
            ((p : ℤ) * r) ^ 2 + ((p : ℤ) * s) ^ 2 := by ring
        _ = (p : ℤ) ^ 2 := hunorm
        _ = (p : ℤ) ^ 2 * 1 := by ring
    exact mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hpZ)) hfactor
  have hprod :
      left.source * u = ((p : ℤ) : HamiltonInt) * right.source := by
    change left.source * hopfRelative left.source right.source = _
    rw [source_mul_hopfRelative, left.sourceNorm]
  let q : HamiltonInt := ⟨r, s, 0, 0⟩
  have hu : u = ((p : ℤ) : HamiltonInt) * q := by
    apply Quaternion.ext <;> simp [q, hr, hs, huJ, huK]
  have hpQ : ((p : ℤ) : HamiltonInt) ≠ 0 := by
    intro hzero
    have hre := congrArg QuaternionAlgebra.re hzero
    simp at hre
    exact (Nat.ne_of_gt hp) hre
  have hphase : left.source * q = right.source := by
    apply mul_left_cancel₀ hpQ
    calc
      ((p : ℤ) : HamiltonInt) * (left.source * q) =
          left.source * (((p : ℤ) : HamiltonInt) * q) := by
            calc
              ((p : ℤ) : HamiltonInt) * (left.source * q) =
                  (((p : ℤ) : HamiltonInt) * left.source) * q := by
                    rw [mul_assoc]
              _ = (left.source * ((p : ℤ) : HamiltonInt)) * q := by
                    exact congrArg (fun x : HamiltonInt => x * q)
                      (Quaternion.coe_commutes (r := (p : ℤ)) (a := left.source))
              _ = left.source * (((p : ℤ) : HamiltonInt) * q) := by
                    rw [mul_assoc]
      _ = left.source * u := by rw [hu]
      _ = ((p : ℤ) : HamiltonInt) * right.source := hprod
  rcases int_sq_add_sq_eq_one_cases r s hrs with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    rw [← hphase]
    apply Quaternion.ext <;> simp [q]
  · right; left
    rw [← hphase]
    apply Quaternion.ext <;> simp [q, hopfPhaseTurnSource]
  · right; right; left
    rw [← hphase]
    apply Quaternion.ext <;> simp [q]
  · right; right; right
    rw [← hphase]
    apply Quaternion.ext <;> simp [q, hopfPhaseTurnSource]

/-- The same exhaustive fibre theorem at the addressed occurrence level.  The
winding coordinate is recovered from the returned triple, so source equality
already determines equality of the complete occurrence. -/
theorem occurrence_eq_phase_of_same_primitive_return
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (left right : FirstHopfOccurrence p)
    (hreturned : left.returnedTriple = right.returnedTriple)
    (hprimitive : reduceTriple (p := p) left.returnedTriple ≠ (0, 0, 0)) :
    right = left ∨ right = left.phaseTurn ∨
      right = left.phaseTurn.phaseTurn ∨
      right = left.phaseTurn.phaseTurn.phaseTurn := by
  have hwinding : right.winding = left.winding := by
    have h := congrArg (fun m : IntTriple => m.2.2) hreturned
    symm
    simpa [FirstHopfOccurrence.returnedTriple] using h
  rcases source_eq_phase_of_same_primitive_return hp2 left right hreturned hprimitive with
      h | h | h | h
  · left
    apply FirstHopfOccurrence.ext <;> assumption
  · right; left
    apply FirstHopfOccurrence.ext
    · simpa [FirstHopfOccurrence.phaseTurn] using h
    · simpa [FirstHopfOccurrence.phaseTurn] using hwinding
  · right; right; left
    apply FirstHopfOccurrence.ext
    · simpa [FirstHopfOccurrence.phaseTurn, hopfPhaseTurnSource_twice] using h
    · simpa [FirstHopfOccurrence.phaseTurn] using hwinding
  · right; right; right
    apply FirstHopfOccurrence.ext
    · calc
        right.source = -hopfPhaseTurnSource left.source := h
        _ = left.phaseTurn.phaseTurn.phaseTurn.source := by
          apply Quaternion.ext <;>
            simp [FirstHopfOccurrence.phaseTurn, hopfPhaseTurnSource]
    · simpa [FirstHopfOccurrence.phaseTurn] using hwinding
#print axioms hopfPivotReturn_eq_mul
#print axioms normSq_hopfPivotReturn
#print axioms firstBrandtQuaternion_returnedTriple
#print axioms brandtFirstQuadratic_returnedTriple
#print axioms returnedTriple_mem_firstPrimeSquarePopulation
#print axioms FirstHopfOccurrence.returnedTriple_phaseTurn
#print axioms FirstHopfOccurrence.phaseTurn_four
#print axioms FirstHopfOccurrence.phaseTurn_ne_self
#print axioms hopfPivotReturn_northHopfSource
#print axioms hopfPivotReturn_southHopfSource
#print axioms normSq_northHopfSource
#print axioms hopfPivotReturn_projectiveHopfSource
#print axioms projectiveHopfScale_ne_zero
#print axioms hopfRelative_commutes_with_pivot
#print axioms hopfRelative_transverse_eq_zero
#print axioms source_mul_hopfRelative
#print axioms normSq_hopfRelative
#print axioms reduceTriple_eq_zero_of_firstBrandtQuaternion
#print axioms hopfRelative_longitudinal_dvd_of_primitive
#print axioms source_eq_phase_of_same_primitive_return
#print axioms occurrence_eq_phase_of_same_primitive_return

end Soma.Holonics.Millennium.FamilyTunnellQuaternionHopf

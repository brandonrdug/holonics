import ElementaryHolonics.Millennium.HolonicTorusMonodromyReceiver

/-!
# The rank-four period lattice enters four finite winding populations

One polygonal solid-torus carrier exposes a longitude and a meridian chain.  A complex two-torus
has a rank-four integral cycle lattice, so its finite realization uses two addressed copies of that
carrier.  The four lattice coefficients become the longitude/meridian winding pair in each copy.

The returned receiver is not a picture of those windings.  Two exact measurements on each copy—a
cross-section current and an addressed meridian branch linkage—reconstruct all four coefficients.
The induced real receiver pairing agrees with the integer cycle/dual-cycle pairing and therefore
commutes with the order-three, order-four, and unipotent monodromies already checked for the complex
`S^6` torus family.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicRankFourWindingRealization

open Soma.Holonics
open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Millennium.HolonicPolygonalTorusCarrier
open Soma.Holonics.Millennium.HolonicTorusParametronRealization
open Soma.Holonics.Millennium.HolonicTorusMonodromyReceiver

/-- Two addressed polygonal torus copies, each retaining its complete integer branch chain. -/
abbrev DoubledWinding (major minor : ℕ) :=
  Fin 2 → Chain (ParametronBranch major minor)

/-- The four period-lattice coefficients become longitude/meridian winding pairs in the two
addressed torus copies. -/
def rankFourWindingRealization (cycle : Lattice) : DoubledWinding major minor :=
  ![cycle 0 • longitudeWindingChain (0 : MinorIndex minor) +
      cycle 1 • meridianWindingChain (0 : MajorIndex major),
    cycle 2 • longitudeWindingChain (0 : MinorIndex minor) +
      cycle 3 • meridianWindingChain (0 : MajorIndex major)]

/-- The integer longitude cut and one addressed meridian coefficient reconstruct the two winding
coordinates in each copy. -/
def rankFourCoefficientReceiver (winding : DoubledWinding major minor) : Lattice :=
  ![evaluateCochain (dualCrossSectionCut (0 : MajorIndex major)) (winding 0),
    winding 0 (.meridian (0 : MajorIndex major) (0 : MinorIndex minor)),
    evaluateCochain (dualCrossSectionCut (0 : MajorIndex major)) (winding 1),
    winding 1 (.meridian (0 : MajorIndex major) (0 : MinorIndex minor))]

private theorem longitudeWindingChain_meridian_edge_eq_zero
    (j : MinorIndex minor) (i : MajorIndex major) (k : MinorIndex minor) :
    longitudeWindingChain (major := major) j (.meridian i k) = 0 := by
  simp [longitudeWindingChain]

/-- The coefficient receiver is a left inverse of the rank-four winding realization.  Thus all
four period-lattice directions remain independent in the doubled finite carrier. -/
theorem rankFourCoefficientReceiver_realization (cycle : Lattice) :
    rankFourCoefficientReceiver
      (rankFourWindingRealization (major := major) (minor := minor) cycle) = cycle := by
  ext coordinate
  fin_cases coordinate <;>
    simp [rankFourCoefficientReceiver, rankFourWindingRealization,
      dualCrossSectionCut_pairs_longitudeWindingChain,
      dualCrossSectionCut_pairs_meridianWindingChain,
      longitudeWindingChain_meridian_edge_eq_zero,
      meridianWindingChain_edge_eq_one]

/-- The addressed winding realization loses no rank-four lattice occurrence. -/
theorem rankFourWindingRealization_injective :
    Function.Injective (rankFourWindingRealization (major := major) (minor := minor)) :=
  Function.LeftInverse.injective rankFourCoefficientReceiver_realization

/-- The realization is an addressed passage, so its source lattice occurrence remains in the
complete fibre of the doubled winding body. -/
def rankFourWindingPassage :
    AddressedPassage Lattice (DoubledWinding major minor) :=
  AddressedPassage.graph rankFourWindingRealization

/-- Every realized rank-four cycle retains its source occurrence in the addressed passage. -/
theorem rankFourWindingPassage_retains_cycle (cycle : Lattice) :
    Nonempty ((rankFourWindingPassage (major := major) (minor := minor)).Fibre cycle
      (rankFourWindingRealization cycle)) :=
  ⟨AddressedPassage.graphFibre _ cycle⟩

/-- Each torus copy is read by the already checked paired current/flux receiver: longitudinal
cross-section current and linkage against one addressed meridian branch probe. -/
def copyCurrentFluxReceiver
    (winding : Chain (ParametronBranch major minor)) : ℝ × ℝ :=
  (crossSectionCurrent (0 : MajorIndex major) (chainDrive winding),
    fluxLinkage winding
      (branchProbe (.meridian (0 : MajorIndex major) (0 : MinorIndex minor))))

/-- The complete rank-four finite face keeps the two torus-copy receiver pairs distinct. -/
def rankFourCurrentFluxReceiver
    (winding : DoubledWinding major minor) : Fin 2 → ℝ × ℝ :=
  fun copy ↦ copyCurrentFluxReceiver (winding copy)

/-- On an arbitrary doubled winding, the real current/flux face is exactly the cast of the four
integer coefficient receivers. -/
theorem rankFourCurrentFluxReceiver_eq_cast_coefficients
    (winding : DoubledWinding major minor) :
    rankFourCurrentFluxReceiver winding =
      ![(((rankFourCoefficientReceiver winding 0 : ℤ) : ℝ),
          ((rankFourCoefficientReceiver winding 1 : ℤ) : ℝ)),
        (((rankFourCoefficientReceiver winding 2 : ℤ) : ℝ),
          ((rankFourCoefficientReceiver winding 3 : ℤ) : ℝ))] := by
  funext copy
  fin_cases copy <;>
    simp [rankFourCurrentFluxReceiver, copyCurrentFluxReceiver,
      rankFourCoefficientReceiver,
      crossSectionCurrent_chainDrive_eq_cast_evaluateCochain,
      fluxLinkage_branchProbe, chainDrive]

/-- Consequently the paired finite receiver reconstructs the four realized lattice coefficients
exactly, after the declared integer-to-real chart transition. -/
theorem rankFourCurrentFluxReceiver_realization (cycle : Lattice) :
    rankFourCurrentFluxReceiver
      (rankFourWindingRealization (major := major) (minor := minor) cycle) =
      ![(((cycle 0 : ℤ) : ℝ), ((cycle 1 : ℤ) : ℝ)),
        (((cycle 2 : ℤ) : ℝ), ((cycle 3 : ℤ) : ℝ))] := by
  rw [rankFourCurrentFluxReceiver_eq_cast_coefficients,
    rankFourCoefficientReceiver_realization]

/-- A dual rank-four probe consumes the two current/flux pairs without deleting their addresses. -/
def rankFourCurrentFluxPairing (probe : Lattice)
    (winding : DoubledWinding major minor) : ℝ :=
  (probe 0 : ℝ) * (rankFourCurrentFluxReceiver winding 0).1 +
    (probe 1 : ℝ) * (rankFourCurrentFluxReceiver winding 0).2 +
    (probe 2 : ℝ) * (rankFourCurrentFluxReceiver winding 1).1 +
    (probe 3 : ℝ) * (rankFourCurrentFluxReceiver winding 1).2

/-- The finite Parametron current/flux pairing is precisely the real cast of the integral
cycle/dual-cycle receiver. -/
theorem rankFourCurrentFluxPairing_realization (probe cycle : Lattice) :
    rankFourCurrentFluxPairing probe
        (rankFourWindingRealization (major := major) (minor := minor) cycle) =
      ((cyclePairing probe cycle : ℤ) : ℝ) := by
  rw [rankFourCurrentFluxPairing, rankFourCurrentFluxReceiver_realization]
  simp [cyclePairing, dotProduct, Fin.sum_univ_succ]
  ring

/-- The realized finite receiver square commutes with the order-three monodromy. -/
theorem rankFourCurrentFluxPairing_T1_A1 (probe cycle : Lattice) :
    rankFourCurrentFluxPairing (A1.mulVec probe)
        (rankFourWindingRealization (major := major) (minor := minor) (T1.mulVec cycle)) =
      rankFourCurrentFluxPairing probe
        (rankFourWindingRealization (major := major) (minor := minor) cycle) := by
  rw [rankFourCurrentFluxPairing_realization, rankFourCurrentFluxPairing_realization,
    cyclePairing_T1_A1]

/-- The realized finite receiver square commutes with the order-four monodromy. -/
theorem rankFourCurrentFluxPairing_T2_A2 (probe cycle : Lattice) :
    rankFourCurrentFluxPairing (A2.mulVec probe)
        (rankFourWindingRealization (major := major) (minor := minor) (T2.mulVec cycle)) =
      rankFourCurrentFluxPairing probe
        (rankFourWindingRealization (major := major) (minor := minor) cycle) := by
  rw [rankFourCurrentFluxPairing_realization, rankFourCurrentFluxPairing_realization,
    cyclePairing_T2_A2]

/-- The realized finite receiver square commutes with the unipotent cusp monodromy. -/
theorem rankFourCurrentFluxPairing_T0_M0 (probe cycle : Lattice) :
    rankFourCurrentFluxPairing (M0.mulVec probe)
        (rankFourWindingRealization (major := major) (minor := minor) (T0.mulVec cycle)) =
      rankFourCurrentFluxPairing probe
        (rankFourWindingRealization (major := major) (minor := minor) cycle) := by
  rw [rankFourCurrentFluxPairing_realization, rankFourCurrentFluxPairing_realization,
    cyclePairing_T0_M0]

/-! ## The homology receiver reopens the doubled-carrier fibre -/

/-- Two addressed populations of two-cells, one for each solid-torus copy. -/
abbrev DoubledFaceChain (major minor : ℕ) :=
  Fin 2 → Chain (Face major minor)

/-- The two-boundary map acts independently in the two addressed carrier copies. -/
def doubledBoundaryTwo (faces : DoubledFaceChain major minor) : DoubledWinding major minor :=
  fun copy ↦ boundaryTwo (faces copy)

/-- A doubled winding is homologically invisible when it is the boundary of an addressed doubled
two-chain. -/
def IsDoubledTwoBoundary (winding : DoubledWinding major minor) : Prop :=
  ∃ faces, doubledBoundaryTwo faces = winding

/-- The four standard lattice directions before realization. -/
def latticeBasis (coordinate : Fin 4) : Lattice :=
  Pi.single coordinate 1

/-- The second rank-four direction becomes a meridian in the first solid torus and therefore bounds
its filled cross-section disk. -/
theorem rankFour_basis_one_isDoubledTwoBoundary :
    IsDoubledTwoBoundary
      (rankFourWindingRealization (major := major) (minor := minor) (latticeBasis 1)) := by
  refine ⟨![crossSectionDisk (minor := minor) (0 : MajorIndex major), 0], ?_⟩
  funext copy
  fin_cases copy <;>
    simp [doubledBoundaryTwo, rankFourWindingRealization, latticeBasis,
      boundaryTwo_crossSectionDisk_eq_meridian]

/-- The fourth rank-four direction becomes a meridian in the second solid torus and also bounds. -/
theorem rankFour_basis_three_isDoubledTwoBoundary :
    IsDoubledTwoBoundary
      (rankFourWindingRealization (major := major) (minor := minor) (latticeBasis 3)) := by
  refine ⟨![0, crossSectionDisk (minor := minor) (0 : MajorIndex major)], ?_⟩
  funext copy
  fin_cases copy <;>
    simp [doubledBoundaryTwo, rankFourWindingRealization, latticeBasis,
      boundaryTwo_crossSectionDisk_eq_meridian]

/-- The first direction remains a nonboundary longitude in the first solid-torus copy. -/
theorem rankFour_basis_zero_isNotDoubledTwoBoundary :
    ¬ IsDoubledTwoBoundary
      (rankFourWindingRealization (major := major) (minor := minor) (latticeBasis 0)) := by
  rintro ⟨faces, hboundary⟩
  have hcopy := congrFun hboundary (0 : Fin 2)
  simp [doubledBoundaryTwo, rankFourWindingRealization, latticeBasis] at hcopy
  exact longitudeWindingChain_isNot_boundaryTwo
    (0 : MajorIndex major) (0 : MinorIndex minor) ⟨faces 0, hcopy⟩

/-- The third direction remains a nonboundary longitude in the second solid-torus copy. -/
theorem rankFour_basis_two_isNotDoubledTwoBoundary :
    ¬ IsDoubledTwoBoundary
      (rankFourWindingRealization (major := major) (minor := minor) (latticeBasis 2)) := by
  rintro ⟨faces, hboundary⟩
  have hcopy := congrFun hboundary (1 : Fin 2)
  simp [doubledBoundaryTwo, rankFourWindingRealization, latticeBasis] at hcopy
  exact longitudeWindingChain_isNot_boundaryTwo
    (0 : MajorIndex major) (0 : MinorIndex minor) ⟨faces 1, hcopy⟩

/-- Zero and the realized second basis direction have the same two-boundary status but are distinct
chain occurrences.  Hence two disjoint solid tori cannot be identified with the rank-four homology
carrier of one complex two-torus. -/
def doubledBoundaryReceiverInsufficiency :
    ReceiverInsufficiency
      (IsDoubledTwoBoundary (major := major) (minor := minor))
      (fun winding ↦ winding) where
  left := 0
  right := rankFourWindingRealization (latticeBasis 1)
  sameEntering := by
    apply propext
    constructor
    · intro hzero
      exact rankFour_basis_one_isDoubledTwoBoundary
    · intro hright
      refine ⟨0, ?_⟩
      funext copy
      exact map_zero boundaryTwo
  differentReturned := by
    intro heq
    have hcoeff := congrArg rankFourCoefficientReceiver heq
    have hzero : rankFourCoefficientReceiver
        (0 : DoubledWinding major minor) = 0 := by
      ext coordinate
      fin_cases coordinate <;> simp [rankFourCoefficientReceiver]
    rw [hzero, rankFourCoefficientReceiver_realization] at hcoeff
    have hone := congrFun hcoeff (1 : Fin 4)
    simp [latticeBasis] at hone

end Soma.Holonics.Millennium.HolonicRankFourWindingRealization

section Audit
open Soma.Holonics.Millennium.HolonicRankFourWindingRealization
#print axioms rankFourCoefficientReceiver_realization
#print axioms rankFourWindingRealization_injective
#print axioms rankFourWindingPassage_retains_cycle
#print axioms rankFourCurrentFluxReceiver_eq_cast_coefficients
#print axioms rankFourCurrentFluxReceiver_realization
#print axioms rankFourCurrentFluxPairing_realization
#print axioms rankFourCurrentFluxPairing_T1_A1
#print axioms rankFourCurrentFluxPairing_T2_A2
#print axioms rankFourCurrentFluxPairing_T0_M0
#print axioms rankFour_basis_one_isDoubledTwoBoundary
#print axioms rankFour_basis_three_isDoubledTwoBoundary
#print axioms rankFour_basis_zero_isNotDoubledTwoBoundary
#print axioms rankFour_basis_two_isNotDoubledTwoBoundary
#print axioms doubledBoundaryReceiverInsufficiency
end Audit

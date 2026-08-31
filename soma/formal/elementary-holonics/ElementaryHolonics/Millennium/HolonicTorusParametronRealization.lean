import ElementaryHolonics.Millennium.HolonicPolygonalTorusCarrier
import ElementaryHolonics.Millennium.HolonicMeasuredParametron
import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Foundation.TransportLift

/-!
# The polygonal torus realizes an exact Complex Parametron incidence body

Gate L1 produced a finite integer cell complex.  The existing Complex Parametron accepts an
arbitrary finite node and oriented branch population with a real incidence map.  This file supplies
the missing realization: vertices are nodes, edges are branches, and the signed cellular boundary
is cast exactly into the real incidence matrix.

The principal return is discrete integration by parts.  The Parametron drive pairing of a chain
with a nodal potential equals the pairing of that potential with the chain's cellular boundary.
Consequently every closed winding has zero pairing with an exact potential drop, while its
oriented chain remains reconstructible from the branch-drive chart.  This is the finite
current/voltage incidence law; no capacitance, inductance, material response, or continuum field is
derived here.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTorusParametronRealization

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Millennium.HolonicPolygonalTorusCarrier
open Soma.Holonics.Millennium.HolonicComplexParametron

/-- The cell vertices are the finite Parametron node population. -/
abbrev ParametronNode (major minor : ℕ) := Vertex major minor

/-- The oriented cell edges are the finite Parametron branch population. -/
abbrev ParametronBranch (major minor : ℕ) := Edge major minor

/-- The Parametron incidence matrix is the exact signed cellular edge boundary, embedded in the
reals. -/
def cellularIncidence (edge : ParametronBranch major minor)
    (node : ParametronNode major minor) : ℝ :=
  (edgeBoundary edge node : ℤ)

/-- Each Parametron branch drop is exactly the cellular boundary paired with the nodal state. -/
theorem branchDrop_cellularIncidence (state : ParametronNode major minor → ℝ)
    (edge : ParametronBranch major minor) :
    branchDrop cellularIncidence state edge =
      ∑ node, (edgeBoundary edge node : ℤ) * state node := by
  rfl

private theorem sum_single_incidence_mul
    (node : ParametronNode major minor) (state : ParametronNode major minor → ℝ) :
    ∑ x, ((Finsupp.single node (1 : ℤ) x : ℤ) : ℝ) * state x = state node := by
  simp [Finsupp.single_apply]

/-- The four branch species return their terminal-minus-initial potential difference. -/
theorem branchDrop_cellularIncidence_eq_endpointDifference
    (state : ParametronNode major minor → ℝ) (edge : ParametronBranch major minor) :
    branchDrop cellularIncidence state edge =
      match edge with
      | .coreLongitude i => state (.core (majorNext i)) - state (.core i)
      | .longitude i j => state (.boundary (majorNext i) j) - state (.boundary i j)
      | .meridian i j => state (.boundary i (minorNext j)) - state (.boundary i j)
      | .radial i j => state (.boundary i j) - state (.core i) := by
  cases edge <;>
    simp only [branchDrop, cellularIncidence, edgeBoundary, Finsupp.sub_apply, Int.cast_sub,
      sub_mul] <;>
    rw [Finset.sum_sub_distrib] <;>
    rw [sum_single_incidence_mul, sum_single_incidence_mul]

/-- An integer cellular one-chain becomes an exact real branch-drive section. -/
def chainDrive (chain : Chain (ParametronBranch major minor)) :
    ParametronBranch major minor → ℝ :=
  fun edge => chain edge

/-- Casting the integral chain into real branch coordinates loses no occurrence. -/
theorem chainDrive_injective :
    Function.Injective (chainDrive (major := major) (minor := minor)) := by
  intro left right heq
  ext edge
  have hreal : (left edge : ℝ) = (right edge : ℝ) := by
    simpa [chainDrive] using congrFun heq edge
  exact_mod_cast hreal

/-- The addressed realization retains the complete source chain before exposing real branch
coordinates. -/
def chainDrivePassage :
    AddressedPassage (Chain (ParametronBranch major minor))
      (ParametronBranch major minor → ℝ) :=
  AddressedPassage.graph chainDrive

/-- Every chain inhabits the complete fibre of its realized branch-drive section. -/
theorem chainDrivePassage_retains_chain (chain : Chain (ParametronBranch major minor)) :
    Nonempty ((chainDrivePassage (major := major) (minor := minor)).Fibre chain
      (chainDrive chain)) :=
  ⟨AddressedPassage.graphFibre _ chain⟩

/-- The real incidence sum at one node is exactly the cast of the integer cellular boundary. -/
theorem cellularIncidence_sum_eq_boundaryOne
    (chain : Chain (ParametronBranch major minor)) (node : ParametronNode major minor) :
    ∑ edge, chainDrive chain edge * cellularIncidence edge node =
      ((boundaryOne chain node : ℤ) : ℝ) := by
  change (∑ edge, (chain edge : ℝ) * (edgeBoundary edge node : ℤ)) =
    ((boundaryOne chain node : ℤ) : ℝ)
  rw [boundaryOne, Finsupp.linearCombination_apply, Finsupp.sum_apply]
  rw [Finsupp.sum_fintype]
  · norm_cast
  · intro edge
    simp

/-- Discrete integration by parts: the Complex Parametron branch pairing factors exactly through
the cellular boundary of the carried one-chain. -/
theorem driveAction_chainDrive_eq_boundaryPairing
    (chain : Chain (ParametronBranch major minor))
    (state : ParametronNode major minor → ℝ) :
    driveAction (chainDrive chain) cellularIncidence state =
      ∑ node, ((boundaryOne chain node : ℤ) : ℝ) * state node := by
  unfold driveAction branchDrop
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro node hnode
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, cellularIncidence_sum_eq_boundaryOne]

/-- Every cellular cycle pairs to zero with every exact nodal potential drop. -/
theorem driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero
    (chain : Chain (ParametronBranch major minor))
    (hclosed : boundaryOne chain = 0)
    (state : ParametronNode major minor → ℝ) :
    driveAction (chainDrive chain) cellularIncidence state = 0 := by
  rw [driveAction_chainDrive_eq_boundaryPairing, hclosed]
  simp

/-- The longitudinal winding realizes a closed Parametron branch cycle. -/
theorem longitudeDriveAction_exactDrop_eq_zero
    (j : MinorIndex minor) (state : ParametronNode major minor → ℝ) :
    driveAction (chainDrive (longitudeWindingChain j)) cellularIncidence state = 0 :=
  driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero _
    (boundaryOne_longitudeWindingChain_eq_zero j) state

/-- The meridional winding also realizes a closed Parametron branch cycle. -/
theorem meridianDriveAction_exactDrop_eq_zero
    (i : MajorIndex major) (state : ParametronNode major minor → ℝ) :
    driveAction (chainDrive (meridianWindingChain i)) cellularIncidence state = 0 :=
  driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero _
    (boundaryOne_meridianWindingChain_eq_zero i) state

/-- Reorienting the realized cell branches transports their potential drops by the same exact
sign section consumed by the Complex Parametron. -/
theorem branchDrop_reorient_cellularIncidence
    (selected : ParametronBranch major minor → Bool)
    (state : ParametronNode major minor → ℝ)
    (edge : ParametronBranch major minor) :
    branchDrop (reorientIncidence selected cellularIncidence) state edge =
      orientationSign selected edge * branchDrop cellularIncidence state edge :=
  branchDrop_reorient selected cellularIncidence state edge

/-! ## Cross-section current and flux-linkage receivers -/

/-- A real branch section on the finite toroidal carrier.  Whether the section is interpreted as
current, flux, voltage, or another transported quantity is fixed by the receiver which consumes
it, not by this carrier type. -/
abbrev BranchSection (major minor : ℕ) := ParametronBranch major minor → ℝ

/-- The exact current through one declared cross-section cut.  The integer cut cochain is retained
and only its final coefficient pairing is cast to the real receiver. -/
def crossSectionCurrent (cut : MajorIndex major)
    (current : BranchSection major minor) : ℝ :=
  ∑ edge, current edge * (dualCrossSectionCut cut edge : ℝ)

/-- Cross-section current is a real-linear receiver on the complete branch-current population. -/
def crossSectionCurrentLinear (cut : MajorIndex major) :
    BranchSection major minor →ₗ[ℝ] ℝ where
  toFun := crossSectionCurrent cut
  map_add' left right := by
    simp [crossSectionCurrent, add_mul, Finset.sum_add_distrib]
  map_smul' scalar current := by
    simp [crossSectionCurrent, Finset.mul_sum, mul_assoc]

/-- On an integral chain current, the real cut receiver is exactly the cast of the original
integer cochain evaluation. -/
theorem crossSectionCurrent_chainDrive_eq_cast_evaluateCochain
    (cut : MajorIndex major) (chain : Chain (ParametronBranch major minor)) :
    crossSectionCurrent cut (chainDrive chain) =
      (evaluateCochain (dualCrossSectionCut cut) chain : ℝ) := by
  have hinteger :
      evaluateCochain (dualCrossSectionCut cut) chain =
        ∑ edge, chain edge * dualCrossSectionCut cut edge := by
    rw [evaluateCochain, Finsupp.linearCombination_apply]
    simpa using Finsupp.sum_fintype chain
      (fun edge coefficient ↦ coefficient • dualCrossSectionCut cut edge)
      (by intro edge; simp)
  unfold crossSectionCurrent chainDrive
  rw [hinteger]
  norm_cast

/-- Every unit longitudinal chain transports one unit of oriented current through every major
cross-section. -/
theorem crossSectionCurrent_longitudeChain_eq_one
    (cut : MajorIndex major) (j : MinorIndex minor) :
    crossSectionCurrent cut (chainDrive (longitudeWindingChain j)) = 1 := by
  rw [crossSectionCurrent_chainDrive_eq_cast_evaluateCochain,
    dualCrossSectionCut_pairs_longitudeWindingChain]
  norm_num

/-- The same cross-section current receiver is blind to every meridional chain. -/
theorem crossSectionCurrent_meridianChain_eq_zero
    (cut i : MajorIndex major) :
    crossSectionCurrent cut (chainDrive (meridianWindingChain (minor := minor) i)) = 0 := by
  rw [crossSectionCurrent_chainDrive_eq_cast_evaluateCochain,
    dualCrossSectionCut_pairs_meridianWindingChain]
  norm_num

/-- The flux linkage of a winding is the exact pairing of its addressed branch coefficients with
the presented branch-flux section. -/
def fluxLinkage (winding : Chain (ParametronBranch major minor))
    (flux : BranchSection major minor) : ℝ :=
  ∑ edge, flux edge * chainDrive winding edge

/-- Flux linkage is a real-linear receiver in the branch-flux section for every retained winding
chain. -/
def fluxLinkageLinear (winding : Chain (ParametronBranch major minor)) :
    BranchSection major minor →ₗ[ℝ] ℝ where
  toFun := fluxLinkage winding
  map_add' left right := by
    simp [fluxLinkage, add_mul, Finset.sum_add_distrib]
  map_smul' scalar flux := by
    simp [fluxLinkage, Finset.mul_sum, mul_assoc]

/-- Pairing a winding with an exact nodal potential drop is the already checked Parametron drive
action, with only the commutative order of the real factors changed. -/
theorem fluxLinkage_exactDrop_eq_driveAction
    (winding : Chain (ParametronBranch major minor))
    (state : ParametronNode major minor → ℝ) :
    fluxLinkage winding (fun edge ↦ branchDrop cellularIncidence state edge) =
      driveAction (chainDrive winding) cellularIncidence state := by
  unfold fluxLinkage driveAction
  apply Finset.sum_congr rfl
  intro edge hedge
  ring

/-- Every closed cellular winding has zero linkage against an exact nodal drop. -/
theorem fluxLinkage_exactDrop_eq_zero_of_boundaryOne_eq_zero
    (winding : Chain (ParametronBranch major minor))
    (hclosed : boundaryOne winding = 0)
    (state : ParametronNode major minor → ℝ) :
    fluxLinkage winding (fun edge ↦ branchDrop cellularIncidence state edge) = 0 := by
  rw [fluxLinkage_exactDrop_eq_driveAction]
  exact driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero winding hclosed state

/-- Exact drops lie in the complete kernel of the flux-linkage receiver for every closed winding. -/
theorem exactDrop_mem_fluxLinkageLinear_ker_of_boundaryOne_eq_zero
    (winding : Chain (ParametronBranch major minor))
    (hclosed : boundaryOne winding = 0)
    (state : ParametronNode major minor → ℝ) :
    (fun edge ↦ branchDrop cellularIncidence state edge) ∈
      (fluxLinkageLinear winding).ker := by
  rw [LinearMap.mem_ker]
  exact fluxLinkage_exactDrop_eq_zero_of_boundaryOne_eq_zero winding hclosed state

/-- Meridional chain currents inhabit the kernel of the cross-section receiver. -/
theorem meridianChainDrive_mem_crossSectionCurrentLinear_ker
    (cut i : MajorIndex major) :
    chainDrive (meridianWindingChain (minor := minor) i) ∈
      (crossSectionCurrentLinear (minor := minor) cut).ker := by
  rw [LinearMap.mem_ker]
  exact crossSectionCurrent_meridianChain_eq_zero cut i

/-- Longitudinal chain currents do not inhabit that kernel. -/
theorem longitudeChainDrive_not_mem_crossSectionCurrentLinear_ker
    (cut : MajorIndex major) (j : MinorIndex minor) :
    chainDrive (longitudeWindingChain (major := major) j) ∉
      (crossSectionCurrentLinear (minor := minor) cut).ker := by
  rw [LinearMap.mem_ker]
  intro hzero
  change crossSectionCurrent cut
    (chainDrive (longitudeWindingChain (major := major) j)) = 0 at hzero
  have hone := crossSectionCurrent_longitudeChain_eq_one cut j
  rw [hzero] at hone
  norm_num at hone

/-- Additive form of the cross-section receiver, used by the common reconstruction-fibre owner. -/
def crossSectionCurrentAddHom (cut : MajorIndex major) :
    BranchSection major minor →+ ℝ where
  toFun := crossSectionCurrent cut
  map_zero' := by simp [crossSectionCurrent]
  map_add' left right := by
    simp [crossSectionCurrent, add_mul, Finset.sum_add_distrib]

/-- Additive form of the flux-linkage receiver, used by the common reconstruction-fibre owner. -/
def fluxLinkageAddHom (winding : Chain (ParametronBranch major minor)) :
    BranchSection major minor →+ ℝ where
  toFun := fluxLinkage winding
  map_zero' := by simp [fluxLinkage]
  map_add' left right := by
    simp [fluxLinkage, add_mul, Finset.sum_add_distrib]

/-- Once one cross-section-current lift is supplied, its complete reconstruction fibre is exactly
a translate of the receiver kernel.  No inverse current field is selected. -/
def crossSectionCurrentFibreEquivKernel
    (cut : MajorIndex major) (value : ℝ)
    (base : Soma.Holonics.Foundation.Lift.ReconstructionFibre
      (crossSectionCurrentAddHom (minor := minor) cut) value) :
    Soma.Holonics.Foundation.Lift.ReconstructionFibre
        (crossSectionCurrentAddHom (minor := minor) cut) value ≃
      (crossSectionCurrentAddHom (minor := minor) cut).ker :=
  Soma.Holonics.Foundation.Lift.fibreEquivKernel
    (crossSectionCurrentAddHom (minor := minor) cut) base

/-- Once one flux-linkage lift is supplied, its complete reconstruction fibre is exactly a
translate of the linkage kernel. -/
def fluxLinkageFibreEquivKernel
    (winding : Chain (ParametronBranch major minor)) (value : ℝ)
    (base : Soma.Holonics.Foundation.Lift.ReconstructionFibre
      (fluxLinkageAddHom winding) value) :
    Soma.Holonics.Foundation.Lift.ReconstructionFibre
        (fluxLinkageAddHom winding) value ≃
      (fluxLinkageAddHom winding).ker :=
  Soma.Holonics.Foundation.Lift.fibreEquivKernel
    (fluxLinkageAddHom winding) base

/-! ## Paired receivers and exact insufficiency -/

/-- A current/flux occurrence keeps the two branch populations distinct before their receiver
faces are paired. -/
abbrev CurrentFluxOccurrence (major minor : ℕ) :=
  BranchSection major minor × BranchSection major minor

/-- The paired face returns cross-section current and winding flux linkage without identifying
their source fields. -/
def currentFluxReceiver (cut : MajorIndex major)
    (winding : Chain (ParametronBranch major minor))
    (occurrence : CurrentFluxOccurrence major minor) : ℝ × ℝ :=
  (crossSectionCurrent cut occurrence.1, fluxLinkage winding occurrence.2)

/-- The paired current/flux receiver is an addressed passage whose occurrence is the complete pair
of branch sections. -/
def currentFluxPassage (cut : MajorIndex major)
    (winding : Chain (ParametronBranch major minor)) :
    AddressedPassage (CurrentFluxOccurrence major minor) (ℝ × ℝ) :=
  AddressedPassage.graph (currentFluxReceiver cut winding)

/-- Every paired receiver face retains its complete source occurrence in the addressed fibre. -/
theorem currentFluxPassage_retains_occurrence
    (cut : MajorIndex major) (winding : Chain (ParametronBranch major minor))
    (occurrence : CurrentFluxOccurrence major minor) :
    Nonempty ((currentFluxPassage cut winding).Fibre occurrence
      (currentFluxReceiver cut winding occurrence)) :=
  ⟨AddressedPassage.graphFibre _ occurrence⟩

/-- A single addressed branch probe, used below to expose a direction lost by the cut receiver. -/
def branchProbe (probe : ParametronBranch major minor) : BranchSection major minor :=
  fun edge ↦ if edge = probe then 1 else 0

/-- Branch-probe linkage reconstructs exactly the selected winding coefficient. -/
theorem fluxLinkage_branchProbe
    (winding : Chain (ParametronBranch major minor))
    (probe : ParametronBranch major minor) :
    fluxLinkage winding (branchProbe probe) = chainDrive winding probe := by
  simp [fluxLinkage, branchProbe]

/-- Every addressed edge of a meridional winding carries unit integral coefficient. -/
theorem meridianWindingChain_edge_eq_one
    (i : MajorIndex major) (j : MinorIndex minor) :
    meridianWindingChain i (.meridian i j) = 1 := by
  classical
  rw [meridianWindingChain]
  rw [Finsupp.finset_sum_apply]
  calc
    (∑ other : MinorIndex minor,
        (Finsupp.single (Edge.meridian i other) (1 : ℤ)) (Edge.meridian i j)) =
        (Finsupp.single (Edge.meridian i j) (1 : ℤ)) (Edge.meridian i j) := by
      apply Finset.sum_eq_single j
      · intro other hother hne
        simp only [Finsupp.single_apply]
        split
        · rename_i heq
          have : other = j := by injection heq
          exact (hne this).elim
        · rfl
      · simp
    _ = 1 := by simp

/-- The same unit coefficient in the real branch-drive chart. -/
theorem chainDrive_meridianWindingChain_edge_eq_one
    (i : MajorIndex major) (j : MinorIndex minor) :
    chainDrive (meridianWindingChain i) (.meridian i j) = 1 := by
  unfold chainDrive
  exact_mod_cast meridianWindingChain_edge_eq_one i j

/-- A meridional winding is a nonzero occurrence even though the cross-section current receiver
returns zero on it. -/
theorem meridianWindingChain_ne_zero (i : MajorIndex major) :
    meridianWindingChain (minor := minor) i ≠ 0 := by
  intro hzero
  have hedge := congrArg
    (fun chain : Chain (ParametronBranch major minor) ↦
      chain (.meridian i (0 : MinorIndex minor))) hzero
  have hedge' :
      meridianWindingChain i (.meridian i (0 : MinorIndex minor)) = 0 := by
    simpa using hedge
  rw [meridianWindingChain_edge_eq_one] at hedge'
  norm_num at hedge'

/-- The cross-section current face alone is insufficient to reconstruct the carried chain: zero
and a nonzero meridional winding occupy the same receiver fibre. -/
def crossSectionCurrentInsufficiency
    (cut i : MajorIndex major) :
    Soma.Holonics.ReceiverInsufficiency
      (fun chain : Chain (ParametronBranch major minor) ↦
        crossSectionCurrent cut (chainDrive chain))
      (fun chain ↦ chain) where
  left := 0
  right := meridianWindingChain i
  sameEntering := by
    calc
      crossSectionCurrent cut (chainDrive (0 : Chain (ParametronBranch major minor))) = 0 := by
        simp [crossSectionCurrent, chainDrive]
      _ = crossSectionCurrent cut (chainDrive (meridianWindingChain i)) :=
        (crossSectionCurrent_meridianChain_eq_zero cut i).symm
  differentReturned := (meridianWindingChain_ne_zero i).symm

/-- Adding one addressed meridian branch probe separates the two occurrences which the current cut
alone identifies. -/
theorem cutAndProbeReceiver_separates_zero_meridian
    (cut i : MajorIndex major) (j : MinorIndex minor) :
    (crossSectionCurrent cut
        (chainDrive (0 : Chain (ParametronBranch major minor))),
      fluxLinkage 0 (branchProbe (.meridian i j))) ≠
    (crossSectionCurrent cut
        (chainDrive (meridianWindingChain (minor := minor) i)),
      fluxLinkage (meridianWindingChain (minor := minor) i)
        (branchProbe (.meridian i j))) := by
  have hzeroCurrent :
      crossSectionCurrent cut
        (chainDrive (0 : Chain (ParametronBranch major minor))) = 0 := by
    simp [crossSectionCurrent, chainDrive]
  rw [hzeroCurrent, crossSectionCurrent_meridianChain_eq_zero (minor := minor)]
  rw [fluxLinkage_branchProbe, fluxLinkage_branchProbe,
    chainDrive_meridianWindingChain_edge_eq_one]
  simp [chainDrive]

end Soma.Holonics.Millennium.HolonicTorusParametronRealization

section Audit
open Soma.Holonics.Millennium.HolonicTorusParametronRealization
#print axioms branchDrop_cellularIncidence_eq_endpointDifference
#print axioms chainDrive_injective
#print axioms chainDrivePassage_retains_chain
#print axioms cellularIncidence_sum_eq_boundaryOne
#print axioms driveAction_chainDrive_eq_boundaryPairing
#print axioms driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero
#print axioms longitudeDriveAction_exactDrop_eq_zero
#print axioms meridianDriveAction_exactDrop_eq_zero
#print axioms branchDrop_reorient_cellularIncidence
#print axioms crossSectionCurrent_chainDrive_eq_cast_evaluateCochain
#print axioms crossSectionCurrent_longitudeChain_eq_one
#print axioms crossSectionCurrent_meridianChain_eq_zero
#print axioms fluxLinkage_exactDrop_eq_driveAction
#print axioms fluxLinkage_exactDrop_eq_zero_of_boundaryOne_eq_zero
#print axioms exactDrop_mem_fluxLinkageLinear_ker_of_boundaryOne_eq_zero
#print axioms meridianChainDrive_mem_crossSectionCurrentLinear_ker
#print axioms longitudeChainDrive_not_mem_crossSectionCurrentLinear_ker
#print axioms crossSectionCurrentFibreEquivKernel
#print axioms fluxLinkageFibreEquivKernel
#print axioms currentFluxPassage_retains_occurrence
#print axioms fluxLinkage_branchProbe
#print axioms meridianWindingChain_ne_zero
#print axioms crossSectionCurrentInsufficiency
#print axioms cutAndProbeReceiver_separates_zero_meridian
end Audit

import ElementaryHolonics.Geometry.SixSphereTorusFibre
import ElementaryHolonics.Geometry.Telescoping
import ElementaryHolonics.Millennium.HolonicFourTorusParametronRealization

/-!
# Exact induction grains on the polygonal four-torus Parametron

**[proved-derived]** The elementary induction occurrence is an addressed pair consisting of one
time step and one oriented two-cell.  An electric one-cochain is integrated around the cellular
boundary of that face, and Faraday's law identifies that circulation with the negative returned
magnetic-flux difference.  This is the finite Stokes law itself: it assumes no circular coil,
radius, or occurrence of `π`.

The file also separates three further objects which a scalar circuit diagram conflates:

* an exact nodal drop, whose circulation vanishes on every face;
* an induced electromotive cochain, which cannot be an exact nodal drop wherever flux changes;
* a conductive branch response, whose node divergence enters the charge/current ledger and which
  is an eddy current only when the returned branch current is a nonzero closed circulation.

Finally the four period directions of the complex two-torus are attached to their actual period
columns `(γ̂, û, ŵ, δ̂)`.  A completely general four-by-four mutual-inductance table sends changes
of their current coordinates to induced electromotive coordinates.  The table and current
transform together under winding reorientation, so the induced response is orientation covariant.
No material Hodge star, conductivity calibration, Maxwell continuum limit, flux quantization, or
hardware law is inferred from cellular incidence alone.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicDiscreteInduction

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Geometry.SixSpherePeriods
open Soma.Holonics.Geometry.SixSphereTorusFibre
open Soma.Holonics.Millennium.HolonicComplexParametron
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicFourTorusParametronRealization

/-! ## One face at one temporal grain -/

/-- Real node, edge, and face sections on the finite four-torus carrier. -/
abbrev NodeSection (grain : ℕ) := ParametronNode grain → ℝ
abbrev EdgeSection (grain : ℕ) := ParametronBranch grain → ℝ
abbrev FaceSection (grain : ℕ) := Face grain → ℝ

/-- The discrete curl/circulation of an edge cochain around one oriented square face. -/
def faceCirculation (emf : EdgeSection grain) (face : Face grain) : ℝ :=
  ∑ edge, (faceBoundary face edge : ℝ) * emf edge

/-- Cellular Stokes in evaluation form: face circulation is the edge cochain paired with the
oriented cellular boundary of the face. -/
theorem faceCirculation_eq_boundaryPairing (emf : EdgeSection grain) (face : Face grain) :
    faceCirculation emf face =
      ∑ edge, (faceBoundary face edge : ℝ) * emf edge :=
  rfl

/-- The curl of every exact nodal drop is zero.  This is `d₁ d₀ = 0`, obtained from the already
proved cellular law `∂₁ ∂₂ = 0`. -/
theorem faceCirculation_exactDrop_eq_zero
    (state : NodeSection grain) (face : Face grain) :
    faceCirculation
        (fun edge ↦ branchDrop cellularIncidence state edge) face = 0 := by
  have hclosed : boundaryOne (faceBoundary face) = 0 :=
    boundaryOne_faceBoundary_eq_zero face
  have haction := driveAction_chainDrive_eq_zero_of_boundaryOne_eq_zero
    (faceBoundary face) hclosed state
  simpa [faceCirculation, driveAction, chainDrive] using haction

/-- Returned change of the magnetic flux attached to one oriented face. -/
def faceFluxDifference (before after : FaceSection grain) (face : Face grain) : ℝ :=
  after face - before face

/-- One exact temporal induction grain.  Its elementary occurrences are the addressed faces; the
law keeps the complete edge electromotive cochain rather than selecting a representative from its
curl fibre. -/
structure InductionGrain (grain : ℕ) where
  fluxBefore : FaceSection grain
  fluxAfter : FaceSection grain
  emf : EdgeSection grain
  faraday : ∀ face,
    faceCirculation emf face = -faceFluxDifference fluxBefore fluxAfter face

/-- A nonzero face-flux change forces nonzero electromotive circulation. -/
theorem InductionGrain.faceCirculation_ne_zero_of_fluxDifference_ne_zero
    (induction : InductionGrain grain) (face : Face grain)
    (hflux : faceFluxDifference induction.fluxBefore induction.fluxAfter face ≠ 0) :
    faceCirculation induction.emf face ≠ 0 := by
  rw [induction.faraday face]
  exact neg_ne_zero.mpr hflux

/-- Therefore an induced electromotive cochain cannot be a globally exact nodal-potential drop on
any face whose flux changes.  The omitted reconstruction fibre is physically and mathematically
real: Faraday fixes the curl, not a unique edge representative. -/
theorem InductionGrain.emf_ne_exactDrop_of_fluxDifference_ne_zero
    (induction : InductionGrain grain) (face : Face grain)
    (hflux : faceFluxDifference induction.fluxBefore induction.fluxAfter face ≠ 0) :
    ¬ ∃ state : NodeSection grain,
      induction.emf = fun edge ↦ branchDrop cellularIncidence state edge := by
  rintro ⟨state, hemf⟩
  have hnonzero := induction.faceCirculation_ne_zero_of_fluxDifference_ne_zero face hflux
  rw [hemf, faceCirculation_exactDrop_eq_zero] at hnonzero
  exact hnonzero rfl

/-- Face circulation is additive over an oriented difference of electromotive cochains. -/
theorem faceCirculation_sub (left right : EdgeSection grain) (face : Face grain) :
    faceCirculation (left - right) face =
      faceCirculation left face - faceCirculation right face := by
  simp [faceCirculation, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Two electromotive cochains with the same face circulations differ by a curl-free cochain. -/
theorem faceCirculation_sub_eq_zero_of_eq
    (left right : EdgeSection grain)
    (hsame : ∀ face, faceCirculation left face = faceCirculation right face)
    (face : Face grain) :
    faceCirculation (left - right) face = 0 := by
  rw [faceCirculation_sub, hsame face, sub_self]

/-- A complete history states Faraday's law at every time-face occurrence. -/
def SatisfiesFaradayHistory
    (flux : ℕ → FaceSection grain) (emf : ℕ → EdgeSection grain) : Prop :=
  ∀ time face,
    faceCirculation (emf time) face = -(flux (time + 1) face - flux time face)

/-- Across any finite number of time grains the local induced circulations telescope exactly to
the one exterior flux difference.  There is no rounding, limiting argument, or chosen time scale. -/
theorem faradayHistory_telescopes
    (flux : ℕ → FaceSection grain) (emf : ℕ → EdgeSection grain)
    (hfaraday : SatisfiesFaradayHistory flux emf) (steps : ℕ) (face : Face grain) :
    (∑ time ∈ Finset.range steps, faceCirculation (emf time) face) =
      -(flux steps face - flux 0 face) := by
  calc
    (∑ time ∈ Finset.range steps, faceCirculation (emf time) face) =
        ∑ time ∈ Finset.range steps, -(flux (time + 1) face - flux time face) := by
      apply Finset.sum_congr rfl
      intro time htime
      exact hfaraday time face
    _ = -(∑ time ∈ Finset.range steps,
        (flux (time + 1) face - flux time face)) := by
      simp
    _ = -(flux steps face - flux 0 face) := by
      rw [Soma.Holonics.finite_telescoping (fun time ↦ flux time face) steps]

/-! ## Conductive return and the eddy-current cut -/

/-- Node divergence of a real branch-current section.  Each edge current is paired with its exact
terminal-minus-initial incidence. -/
def nodeDivergence (current : EdgeSection grain) (node : ParametronNode grain) : ℝ :=
  ∑ edge, current edge * cellularIncidence edge node

/-- The elementary local circulation carried by one oriented face boundary.  This is the finite
eddy-loop grain supplied by topology; whether it is physically excited and with what magnitude is
still a constitutive question. -/
def localFaceCurrent (face : Face grain) : EdgeSection grain :=
  chainDrive (faceBoundary face)

/-- Every local face current is source-free at each node because the boundary of the face boundary
vanishes. -/
theorem nodeDivergence_localFaceCurrent_eq_zero
    (face : Face grain) (node : ParametronNode grain) :
    nodeDivergence (localFaceCurrent face) node = 0 := by
  rw [nodeDivergence, localFaceCurrent,
    cellularIncidence_sum_eq_boundaryOne, boundaryOne_faceBoundary_eq_zero]
  simp

/-- The total divergence of every branch-current section on the closed finite carrier is zero:
every branch departure and arrival cancel once. -/
theorem sum_nodeDivergence_eq_zero (current : EdgeSection grain) :
    ∑ node, nodeDivergence current node = 0 := by
  unfold nodeDivergence
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro edge hedge
  rw [← Finset.mul_sum]
  have hincidence : ∑ node, cellularIncidence edge node = 0 := by
    simp only [cellularIncidence, edgeBoundary, Finsupp.sub_apply, Int.cast_sub]
    rw [Finset.sum_sub_distrib]
    have hterminal :
        ∑ node, ((Finsupp.single (stepVertex edge.direction edge.base) 1 node : ℤ) : ℝ) = 1 := by
      simp [Finsupp.single_apply]
    have hinitial :
        ∑ node, ((Finsupp.single edge.base 1 node : ℤ) : ℝ) = 1 := by
      simp [Finsupp.single_apply]
    rw [hterminal, hinitial, sub_self]
  rw [hincidence, mul_zero]

/-- One charge/current continuity grain.  Storage and exterior source are retained separately from
the current divergence. -/
structure ContinuityGrain (grain : ℕ) where
  chargeBefore : NodeSection grain
  chargeAfter : NodeSection grain
  current : EdgeSection grain
  source : NodeSection grain
  balance : ∀ node,
    chargeAfter node - chargeBefore node + nodeDivergence current node = source node

/-- Summing the local continuity law returns the exact global source/storage balance; the interior
current cancels by the finite divergence theorem. -/
theorem ContinuityGrain.globalBalance (continuity : ContinuityGrain grain) :
    (∑ node, (continuity.chargeAfter node - continuity.chargeBefore node)) =
      ∑ node, continuity.source node := by
  have hsum :
      (∑ node : ParametronNode grain,
        (continuity.chargeAfter node - continuity.chargeBefore node +
          nodeDivergence continuity.current node)) =
        ∑ node : ParametronNode grain, continuity.source node := by
    apply Finset.sum_congr rfl
    intro node hnode
    exact continuity.balance node
  rw [Finset.sum_add_distrib, sum_nodeDivergence_eq_zero, add_zero] at hsum
  exact hsum

/-- A diagonal conductive response.  The conductance field is a declared material section rather
than a consequence of cell geometry. -/
def conductiveResponse
    (conductance emf : EdgeSection grain) : EdgeSection grain :=
  fun edge ↦ conductance edge * emf edge

/-- A returned branch current is an eddy-current circulation at this receiver exactly when it is
nonzero and source-free at every node. -/
def IsEddyCurrent (current : EdgeSection grain) : Prop :=
  current ≠ 0 ∧ ∀ node, nodeDivergence current node = 0

/-- A conductive induction grain keeps induction, material response, and circulation as distinct
fields.  The structure does not postulate that every induced conductive response is closed. -/
structure ConductiveInductionGrain (grain : ℕ) extends InductionGrain grain where
  conductance : EdgeSection grain
  current : EdgeSection grain
  currentLaw : current = conductiveResponse conductance emf

/-- Zero electromotive current produces zero diagonal conductive current exactly. -/
theorem ConductiveInductionGrain.current_eq_zero_of_emf_eq_zero
    (induction : ConductiveInductionGrain grain) (hemf : induction.emf = 0) :
    induction.current = 0 := by
  rw [induction.currentLaw, hemf]
  funext edge
  simp [conductiveResponse]

/-! ## The four global period directions and mutual induction -/

/-- The four period coordinates, in the source paper's ordered basis. -/
abbrev gammaDirection : Direction := 0
abbrev uDirection : Direction := 1
abbrev wDirection : Direction := 2
abbrev deltaDirection : Direction := 3

/-- One unit integral cycle in the declared period direction. -/
def periodBasisCycle (direction : Direction) : Lattice :=
  Pi.single direction 1

/-- The `γ̂` cycle translates the universal cover by the first period column `(6μ, β)`. -/
theorem gammaPeriodVector (point : PeriodPoint) :
    periodColumnVector point (periodBasisCycle gammaDirection) =
      ![6 * point.μ, point.β] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodColumnVector, periodBasisCycle, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, gammaDirection]

/-- The `û` cycle translates by the second period column `(τ, μ)`. -/
theorem uPeriodVector (point : PeriodPoint) :
    periodColumnVector point (periodBasisCycle uDirection) =
      ![point.τ, point.μ] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodColumnVector, periodBasisCycle, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, uDirection]

/-- The `ŵ` cycle is the unit translation in the first complex fibre coordinate. -/
theorem wPeriodVector (point : PeriodPoint) :
    periodColumnVector point (periodBasisCycle wDirection) = ![1, 0] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodColumnVector, periodBasisCycle, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, wDirection]

/-- The `δ̂` cycle is the unit translation in the second complex fibre coordinate. -/
theorem deltaPeriodVector (point : PeriodPoint) :
    periodColumnVector point (periodBasisCycle deltaDirection) = ![0, 1] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodColumnVector, periodBasisCycle, periodMatrix, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, deltaDirection]

/-- The source paper's invariant bivector `η`, read as an alternating form on the dual period
lattice `Λ`: `η(û,ŵ)=1` and `η(γ̂,δ̂)=6`.  This is distinct from its inverse alternating form
`Q₀` on the primal lattice `V`. -/
def periodBivector : LatticeEnd :=
  !![0, 0, 0, 6;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -6, 0, 0, 0]

theorem periodBivector_isAlternating : periodBivector.transpose = -periodBivector := by
  decide

theorem periodBivector_is_A1_invariant :
    A1.transpose * periodBivector * A1 = periodBivector := by
  decide

theorem periodBivector_is_A2_invariant :
    A2.transpose * periodBivector * A2 = periodBivector := by
  decide

theorem periodBivector_is_M0_invariant :
    M0.transpose * periodBivector * M0 = periodBivector := by
  decide

/-- Evaluation of the invariant period-lattice bivector on two integral cycles. -/
def periodBivectorPairing (left right : Lattice) : ℤ :=
  dotProduct left (periodBivector.mulVec right)

/-- The first oriented period plane pairs `γ̂` with `δ̂` with multiplicity six. -/
theorem gamma_delta_periodPairing :
    periodBivectorPairing
      (periodBasisCycle gammaDirection) (periodBasisCycle deltaDirection) = 6 := by
  decide

/-- Reversing that plane reverses its hand. -/
theorem delta_gamma_periodPairing :
    periodBivectorPairing
      (periodBasisCycle deltaDirection) (periodBasisCycle gammaDirection) = -6 := by
  decide

/-- The second oriented period plane pairs `û` with `ŵ` once. -/
theorem u_w_periodPairing :
    periodBivectorPairing
      (periodBasisCycle uDirection) (periodBasisCycle wDirection) = 1 := by
  decide

/-- Reversing the second plane reverses its hand. -/
theorem w_u_periodPairing :
    periodBivectorPairing
      (periodBasisCycle wDirection) (periodBasisCycle uDirection) = -1 := by
  decide

/-- Real current coordinates and their full mutual flux-linkage table on the four period cycles. -/
abbrev AxisSection := Direction → ℝ
abbrev AxisCoupling := Direction → Direction → ℝ

/-- Flux linkage observed on one period winding from all four current coordinates. -/
def axisFluxLinkage
    (coupling : AxisCoupling) (current : AxisSection) (observed : Direction) : ℝ :=
  ∑ source, coupling observed source * current source

/-- The exact finite-time induced electromotive coordinate `-Δ(MI)` on one observed winding. -/
def inducedAxisEmf
    (coupling : AxisCoupling) (currentBefore currentAfter : AxisSection)
    (observed : Direction) : ℝ :=
  -(axisFluxLinkage coupling currentAfter observed -
    axisFluxLinkage coupling currentBefore observed)

/-- Every induced coordinate is the signed superposition of all four exact current differences.
The geometry and material enter only through the addressed mutual-coupling table. -/
theorem inducedAxisEmf_eq_sum_currentDifferences
    (coupling : AxisCoupling) (currentBefore currentAfter : AxisSection)
    (observed : Direction) :
    inducedAxisEmf coupling currentBefore currentAfter observed =
      -∑ source, coupling observed source *
        (currentAfter source - currentBefore source) := by
  simp only [inducedAxisEmf, axisFluxLinkage]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro source hsource
  ring

/-- Coordinated reorientation of the current coordinates and both indices of the mutual table
reorients the returned flux linkage and changes nothing else. -/
theorem axisFluxLinkage_reorient
    (selected : Direction → Bool) (coupling : AxisCoupling)
    (current : AxisSection) (observed : Direction) :
    axisFluxLinkage (reorientCoupling selected coupling)
        (reorientDrive selected current) observed =
      orientationSign selected observed *
        axisFluxLinkage coupling current observed := by
  unfold axisFluxLinkage reorientCoupling reorientDrive
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro source hsource
  have hsign := orientationSign_sq selected source
  calc
    (orientationSign selected observed * coupling observed source *
          orientationSign selected source) *
        (orientationSign selected source * current source) =
      orientationSign selected observed *
        (orientationSign selected source ^ 2 *
          (coupling observed source * current source)) := by ring
    _ = orientationSign selected observed *
        (coupling observed source * current source) := by rw [hsign, one_mul]

/-- Mutual induction is covariant under every coordinated winding-orientation change.  Thus
`up/down` is a receiver hand: changing the declared hand changes the coordinate sign while
preserving the coupled occurrence. -/
theorem inducedAxisEmf_reorient
    (selected : Direction → Bool) (coupling : AxisCoupling)
    (currentBefore currentAfter : AxisSection) :
    (fun observed ↦
      inducedAxisEmf (reorientCoupling selected coupling)
        (reorientDrive selected currentBefore)
        (reorientDrive selected currentAfter) observed) =
      reorientDrive selected
        (fun observed ↦ inducedAxisEmf coupling currentBefore currentAfter observed) := by
  funext observed
  change
    -(axisFluxLinkage (reorientCoupling selected coupling)
        (reorientDrive selected currentAfter) observed -
      axisFluxLinkage (reorientCoupling selected coupling)
        (reorientDrive selected currentBefore) observed) =
      orientationSign selected observed *
        -(axisFluxLinkage coupling currentAfter observed -
          axisFluxLinkage coupling currentBefore observed)
  rw [axisFluxLinkage_reorient, axisFluxLinkage_reorient]
  ring

end Soma.Holonics.Millennium.HolonicDiscreteInduction

section Audit
open Soma.Holonics.Millennium.HolonicDiscreteInduction
#print axioms faceCirculation_exactDrop_eq_zero
#print axioms InductionGrain.emf_ne_exactDrop_of_fluxDifference_ne_zero
#print axioms faceCirculation_sub_eq_zero_of_eq
#print axioms faradayHistory_telescopes
#print axioms nodeDivergence_localFaceCurrent_eq_zero
#print axioms sum_nodeDivergence_eq_zero
#print axioms ContinuityGrain.globalBalance
#print axioms gammaPeriodVector
#print axioms uPeriodVector
#print axioms wPeriodVector
#print axioms deltaPeriodVector
#print axioms periodBivector_isAlternating
#print axioms periodBivector_is_A1_invariant
#print axioms periodBivector_is_A2_invariant
#print axioms periodBivector_is_M0_invariant
#print axioms gamma_delta_periodPairing
#print axioms u_w_periodPairing
#print axioms inducedAxisEmf_eq_sum_currentDifferences
#print axioms axisFluxLinkage_reorient
#print axioms inducedAxisEmf_reorient
end Audit

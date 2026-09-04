import ElementaryHolonics.Foundation.TransportLift
import ElementaryHolonics.Millennium.HolonicComposition
import ElementaryHolonics.Millennium.HolonicEntropyActionInduction
import ElementaryHolonics.Millennium.HolonicMaxwellPropagation
import ElementaryHolonics.Millennium.HolonicTypedOriginDimensions

/-!
# The cellular Maxwell operator returned from four-torus incidence

**[proved-derived]** The existing four-torus face boundary constructs both directions of the
coordinate Maxwell incidence passage.  `cellularCurl` evaluates an edge section on the oriented
boundary of every face.  `cellularCoCurl` is constructed from the transpose of those same signed
incidence coefficients.  Their finite coordinate pairings are exactly adjoint, so both resulting
curl--curl actions are sums of squares.

The construction also returns the complete preimage fibres.  In particular every exact
nodal drop lies in the curl kernel, so a face-circulation reading cannot silently reconstruct a
unique edge antecedent.  A concrete cellular Maxwell history then inherits the exact wave law and
the coefficient `c² = (permeability * permittivity)⁻¹` from the common propagation owner.

This file also constructs a positive finite-cell constitutive Hodge datum.  Its co-curl is the
forced weighted transpose `M₁⁻¹ Bᵀ M₂`; weighted adjointness, nonnegative self-pairing, and
trivial receiver radical are exact.  Exact positive primal/dual cell measures now return those
weights with their addressed quantity origins.  Midpoint Maxwell transport returns the complete
finite Poynting ledger, including its boundary/interface adjoint defect, and a constituted scale
passage preserves both curls and both Hodge pairings.  Material calibration, a cut-body port trace,
and source-specific continuum reconstruction remain later passages.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicDiscreteMaxwellOperator

open scoped BigOperators
open Soma.Holonics.Foundation
open Soma.Holonics.Millennium.HolonicDifferenceCalculus
open Soma.Holonics.Millennium.HolonicComplexParametron
open Soma.Holonics.Millennium.HolonicComposition
open Soma.Holonics.Millennium.HolonicDiscreteInduction
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicFourTorusParametronRealization
open Soma.Holonics.Millennium.HolonicMaxwellPropagation
open Soma.Holonics.Millennium.HolonicEntropyActionInduction
open Soma.Holonics.Millennium.HolonicTypedOriginDimensions

/-! ## Incidence and its coordinate transpose -/

/-! ### Cellular Stokes as an abelian connection return -/

/-- The four retained signed edge increments around one addressed square. -/
def faceBoundaryIncrements (electric : EdgeSection grain) (face : Face grain) : List ℝ :=
  [ electric ⟨face.first, face.base⟩,
    electric ⟨face.second, stepVertex face.first face.base⟩,
    -electric ⟨face.first, stepVertex face.second face.base⟩,
    -electric ⟨face.second, face.base⟩ ]

/-- Evaluating the cellular boundary is exactly the sum of its four retained signed increments. -/
theorem faceBoundaryIncrements_sum (electric : EdgeSection grain) (face : Face grain) :
    (faceBoundaryIncrements electric face).sum = faceCirculation electric face := by
  let pairing : Edge grain → ℤ → ℝ :=
    fun edge coefficient ↦ (coefficient : ℝ) * electric edge
  have hfinite : (faceBoundary face).sum pairing = faceCirculation electric face := by
    rw [Finsupp.sum_fintype]
    · rfl
    · intro edge
      simp [pairing]
  rw [← hfinite]
  have hsub : ∀ edge (left right : ℤ),
      pairing edge (left - right) = pairing edge left - pairing edge right := by
    intro edge left right
    simp only [pairing]
    push_cast
    ring
  rw [faceBoundary, Finsupp.sum_sub_index hsub, Finsupp.sum_sub_index hsub]
  rw [Finsupp.sum_add_index]
  · simp [faceBoundaryIncrements, pairing]
    ring
  · intro edge hedge
    simp [pairing]
  · intro edge hedge left right
    simp [pairing]
    ring

/-- Additive connection transport around a cellular face is translation by its exact curl.  This
is the connection form of discrete Stokes; no circular-coil or continuum approximation enters. -/
theorem faceConnectionHolonomy_eq_curlTranslation
    (electric : EdgeSection grain) (face : Face grain) :
    parallelTransport
        ((faceBoundaryIncrements electric face).map additiveTranslation) =
      additiveTranslation (faceCirculation electric face) := by
  rw [parallelTransport_additiveTranslation, faceBoundaryIncrements_sum]

/-- Edge circulation on every addressed square face, as one real-linear receiver. -/
def cellularCurl (grain : ℕ) : EdgeSection grain →ₗ[ℝ] FaceSection grain where
  toFun electric face := faceCirculation electric face
  map_add' left right := by
    funext face
    simp [faceCirculation, mul_add, Finset.sum_add_distrib]
  map_smul' scalar electric := by
    funext face
    simp only [faceCirculation, Pi.smul_apply, smul_eq_mul]
    change (∑ edge, (faceBoundary face edge : ℝ) * (scalar * electric edge)) =
      scalar * ∑ edge, (faceBoundary face edge : ℝ) * electric edge
    calc
      _ = ∑ edge, scalar * ((faceBoundary face edge : ℝ) * electric edge) := by
        apply Finset.sum_congr rfl
        intro edge _
        ring
      _ = _ := by rw [Finset.mul_sum]

/-- The coordinate transpose of cellular curl, constructed from the same signed face boundary. -/
def cellularCoCurl (grain : ℕ) : FaceSection grain →ₗ[ℝ] EdgeSection grain where
  toFun magnetic edge :=
    ∑ face, (faceBoundary face edge : ℝ) * magnetic face
  map_add' left right := by
    funext edge
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar magnetic := by
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul]
    change (∑ face, (faceBoundary face edge : ℝ) * (scalar * magnetic face)) =
      scalar * ∑ face, (faceBoundary face edge : ℝ) * magnetic face
    calc
      _ = ∑ face, scalar * ((faceBoundary face edge : ℝ) * magnetic face) := by
        apply Finset.sum_congr rfl
        intro face _
        ring
      _ = _ := by rw [Finset.mul_sum]

/-- Coordinate pairing of two edge sections. -/
def edgePairing (left right : EdgeSection grain) : ℝ :=
  ∑ edge, left edge * right edge

/-- Coordinate pairing of two face sections. -/
def facePairing (left right : FaceSection grain) : ℝ :=
  ∑ face, left face * right face

theorem edgePairing_comm (left right : EdgeSection grain) :
    edgePairing left right = edgePairing right left := by
  simp only [edgePairing]
  apply Finset.sum_congr rfl
  intro edge _
  exact mul_comm _ _

theorem facePairing_comm (left right : FaceSection grain) :
    facePairing left right = facePairing right left := by
  simp only [facePairing]
  apply Finset.sum_congr rfl
  intro face _
  exact mul_comm _ _

/-- The two constructed incidence directions are exactly adjoint under the coordinate pairings. -/
theorem cellularCurl_adjoint
    (electric : EdgeSection grain) (magnetic : FaceSection grain) :
    facePairing (cellularCurl grain electric) magnetic =
      edgePairing electric (cellularCoCurl grain magnetic) := by
  simp only [facePairing, edgePairing, cellularCurl, cellularCoCurl, faceCirculation,
    LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ face, (∑ edge, (faceBoundary face edge : ℝ) * electric edge) * magnetic face) =
        ∑ face, ∑ edge,
          ((faceBoundary face edge : ℝ) * electric edge) * magnetic face := by
      apply Finset.sum_congr rfl
      intro face _
      rw [Finset.sum_mul]
    _ = ∑ edge, ∑ face,
        ((faceBoundary face edge : ℝ) * electric edge) * magnetic face := by
      rw [Finset.sum_comm]
    _ = ∑ edge, electric edge *
        ∑ face, (faceBoundary face edge : ℝ) * magnetic face := by
      apply Finset.sum_congr rfl
      intro edge _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro face _
      ring

/-! ## Positive finite-cell constitutive Hodge law -/

/-- Positive diagonal cochain metrics on the retained addressed edge and face populations.
The weights are constitutive data; no uniform-cell or circular-coil geometry is assumed. -/
structure PositiveCellHodge (grain : ℕ) where
  edgeWeight : Edge grain → ℝ
  faceWeight : Face grain → ℝ
  edgeWeight_pos : ∀ edge, 0 < edgeWeight edge
  faceWeight_pos : ∀ face, 0 < faceWeight face

namespace PositiveCellHodge

/-- Receiver pairing on edge current, retaining an independent positive weight at every address. -/
def edgePairing (hodge : PositiveCellHodge grain)
    (left right : EdgeSection grain) : ℝ :=
  ∑ edge, hodge.edgeWeight edge * left edge * right edge

/-- Receiver pairing on face flux, retaining an independent positive weight at every address. -/
def facePairing (hodge : PositiveCellHodge grain)
    (left right : FaceSection grain) : ℝ :=
  ∑ face, hodge.faceWeight face * left face * right face

theorem edgePairing_comm (hodge : PositiveCellHodge grain)
    (left right : EdgeSection grain) :
    hodge.edgePairing left right = hodge.edgePairing right left := by
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem facePairing_comm (hodge : PositiveCellHodge grain)
    (left right : FaceSection grain) :
    hodge.facePairing left right = hodge.facePairing right left := by
  apply Finset.sum_congr rfl
  intro face _
  ring

/-- The constitutive co-curl forced by the positive cell metrics: `M₁⁻¹ Bᵀ M₂`. -/
def coCurl (hodge : PositiveCellHodge grain) :
    FaceSection grain →ₗ[ℝ] EdgeSection grain where
  toFun magnetic edge :=
    (hodge.edgeWeight edge)⁻¹ *
      ∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) * magnetic face
  map_add' left right := by
    funext edge
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' scalar magnetic := by
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (hodge.edgeWeight edge)⁻¹ *
          (∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) *
            (scalar * magnetic face)) =
        (hodge.edgeWeight edge)⁻¹ *
          (scalar * ∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) *
            magnetic face) := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro face _
              ring
      _ = scalar * ((hodge.edgeWeight edge)⁻¹ *
          ∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) *
            magnetic face) := by ring

lemma edgeWeight_ne (hodge : PositiveCellHodge grain) (edge : Edge grain) :
    hodge.edgeWeight edge ≠ 0 :=
  ne_of_gt (hodge.edgeWeight_pos edge)

private lemma edge_cancel (hodge : PositiveCellHodge grain)
    (edge : Edge grain) (left right : ℝ) :
    hodge.edgeWeight edge * left * ((hodge.edgeWeight edge)⁻¹ * right) =
      left * right := by
  field_simp [hodge.edgeWeight_ne edge]

/-- The material co-curl is exactly adjoint to the same cellular Stokes/curl owner. -/
theorem adjoint (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) (magnetic : FaceSection grain) :
    hodge.facePairing (cellularCurl grain electric) magnetic =
      hodge.edgePairing electric (hodge.coCurl magnetic) := by
  simp only [facePairing, edgePairing, cellularCurl, coCurl, faceCirculation,
    LinearMap.coe_mk, AddHom.coe_mk]
  calc
    (∑ face, hodge.faceWeight face *
        (∑ edge, (faceBoundary face edge : ℝ) * electric edge) * magnetic face) =
      ∑ face, ∑ edge,
        hodge.faceWeight face * ((faceBoundary face edge : ℝ) * electric edge) *
          magnetic face := by
            apply Finset.sum_congr rfl
            intro face _
            rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ edge, ∑ face,
        hodge.faceWeight face * ((faceBoundary face edge : ℝ) * electric edge) *
          magnetic face := by rw [Finset.sum_comm]
    _ = ∑ edge, electric edge *
        (∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) * magnetic face) := by
          apply Finset.sum_congr rfl
          intro edge _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro face _
          ring
    _ = ∑ edge, hodge.edgeWeight edge * electric edge *
        ((hodge.edgeWeight edge)⁻¹ *
          ∑ face, hodge.faceWeight face * (faceBoundary face edge : ℝ) * magnetic face) := by
          apply Finset.sum_congr rfl
          intro edge _
          exact (hodge.edge_cancel edge _ _).symm

/-- Positive material edge current has nonnegative receiver self-pairing. -/
theorem edgePairing_self_nonneg (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) :
    0 ≤ hodge.edgePairing electric electric := by
  apply Finset.sum_nonneg
  intro edge _
  have hweight : 0 ≤ hodge.edgeWeight edge := le_of_lt (hodge.edgeWeight_pos edge)
  nlinarith [sq_nonneg (electric edge)]

/-- Positive material face flux has nonnegative receiver self-pairing. -/
theorem facePairing_self_nonneg (hodge : PositiveCellHodge grain)
    (magnetic : FaceSection grain) :
    0 ≤ hodge.facePairing magnetic magnetic := by
  apply Finset.sum_nonneg
  intro face _
  have hweight : 0 ≤ hodge.faceWeight face := le_of_lt (hodge.faceWeight_pos face)
  nlinarith [sq_nonneg (magnetic face)]

/-- Material face-wave action `curl ∘ coCurl`. -/
def faceCurlCurl (hodge : PositiveCellHodge grain) :
    FaceSection grain →ₗ[ℝ] FaceSection grain :=
  (cellularCurl grain).comp hodge.coCurl

/-- Material edge-wave action `coCurl ∘ curl`. -/
def edgeCurlCurl (hodge : PositiveCellHodge grain) :
    EdgeSection grain →ₗ[ℝ] EdgeSection grain :=
  hodge.coCurl.comp (cellularCurl grain)

theorem faceCurlCurl_pairing_self (hodge : PositiveCellHodge grain)
    (magnetic : FaceSection grain) :
    hodge.facePairing (hodge.faceCurlCurl magnetic) magnetic =
      hodge.edgePairing (hodge.coCurl magnetic) (hodge.coCurl magnetic) := by
  change hodge.facePairing (cellularCurl grain (hodge.coCurl magnetic)) magnetic = _
  exact hodge.adjoint (hodge.coCurl magnetic) magnetic

theorem edgeCurlCurl_pairing_self (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) :
    hodge.edgePairing (hodge.edgeCurlCurl electric) electric =
      hodge.facePairing (cellularCurl grain electric) (cellularCurl grain electric) := by
  rw [hodge.edgePairing_comm]
  change hodge.edgePairing electric (hodge.coCurl (cellularCurl grain electric)) = _
  exact (hodge.adjoint electric (cellularCurl grain electric)).symm

/-- The material face-wave action is passive under the same positive Hodge receiver. -/
theorem faceCurlCurl_pairing_nonneg (hodge : PositiveCellHodge grain)
    (magnetic : FaceSection grain) :
    0 ≤ hodge.facePairing (hodge.faceCurlCurl magnetic) magnetic := by
  rw [hodge.faceCurlCurl_pairing_self]
  exact hodge.edgePairing_self_nonneg (hodge.coCurl magnetic)

/-- The material edge-wave action is passive under the same positive Hodge receiver. -/
theorem edgeCurlCurl_pairing_nonneg (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) :
    0 ≤ hodge.edgePairing (hodge.edgeCurlCurl electric) electric := by
  rw [hodge.edgeCurlCurl_pairing_self]
  exact hodge.facePairing_self_nonneg (cellularCurl grain electric)

/-- Positivity closes the edge receiver radical: zero self-pairing means zero current section. -/
theorem edgePairing_self_eq_zero_iff (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) :
    hodge.edgePairing electric electric = 0 ↔ electric = 0 := by
  constructor
  · intro hzero
    funext edge
    have hall : ∀ edge ∈ (Finset.univ : Finset (Edge grain)),
        hodge.edgeWeight edge * electric edge * electric edge = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun edge _ ↦ by
          have hweight : 0 ≤ hodge.edgeWeight edge :=
            le_of_lt (hodge.edgeWeight_pos edge)
          nlinarith [sq_nonneg (electric edge)])).mp (by
            simpa only [edgePairing] using hzero)
    have hterm := hall edge (Finset.mem_univ edge)
    have hfactor : hodge.edgeWeight edge * (electric edge * electric edge) = 0 := by
      simpa only [mul_assoc] using hterm
    rcases mul_eq_zero.mp hfactor with hweight | helectric
    · exact (hodge.edgeWeight_ne edge hweight).elim
    · exact mul_self_eq_zero.mp helectric
  · intro helectric
    subst electric
    simp [edgePairing]

/-- Positivity closes the face receiver radical: zero self-pairing means zero flux section. -/
theorem facePairing_self_eq_zero_iff (hodge : PositiveCellHodge grain)
    (magnetic : FaceSection grain) :
    hodge.facePairing magnetic magnetic = 0 ↔ magnetic = 0 := by
  constructor
  · intro hzero
    funext face
    have hall : ∀ face ∈ (Finset.univ : Finset (Face grain)),
        hodge.faceWeight face * magnetic face * magnetic face = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun face _ ↦ by
          have hweight : 0 ≤ hodge.faceWeight face :=
            le_of_lt (hodge.faceWeight_pos face)
          nlinarith [sq_nonneg (magnetic face)])).mp (by
            simpa only [facePairing] using hzero)
    have hterm := hall face (Finset.mem_univ face)
    have hweight_ne : hodge.faceWeight face ≠ 0 :=
      ne_of_gt (hodge.faceWeight_pos face)
    have hfactor : hodge.faceWeight face * (magnetic face * magnetic face) = 0 := by
      simpa only [mul_assoc] using hterm
    rcases mul_eq_zero.mp hfactor with hweight | hmagnetic
    · exact (hweight_ne hweight).elim
    · exact mul_self_eq_zero.mp hmagnetic
  · intro hmagnetic
    subst magnetic
    simp [facePairing]

end PositiveCellHodge

/-! ## Exact primal/dual geometry returns the positive Hodge weights -/

/-- The addressed source occurrence of one cell measure.  Equal coordinates across constructors
do not identify a primal cell, its dual, or another addressed cell. -/
inductive CellMeasureOrigin (grain : ℕ) where
  | primalEdge : Edge grain → CellMeasureOrigin grain
  | dualEdge : Edge grain → CellMeasureOrigin grain
  | primalFace : Face grain → CellMeasureOrigin grain
  | dualFace : Face grain → CellMeasureOrigin grain

/-- Exact positive rational measures on the primal one/two-cells and their dual cells. -/
structure PositivePrimalDualCellGeometry (grain : ℕ) where
  primalEdgeMeasure : Edge grain → ℚ
  dualEdgeMeasure : Edge grain → ℚ
  primalFaceMeasure : Face grain → ℚ
  dualFaceMeasure : Face grain → ℚ
  primalEdgeMeasure_pos : ∀ edge, 0 < primalEdgeMeasure edge
  dualEdgeMeasure_pos : ∀ edge, 0 < dualEdgeMeasure edge
  primalFaceMeasure_pos : ∀ face, 0 < primalFaceMeasure face
  dualFaceMeasure_pos : ∀ face, 0 < dualFaceMeasure face

namespace PositivePrimalDualCellGeometry

/-- The primal edge length with its addressed source origin retained. -/
def primalEdgeQuantity (geometry : PositivePrimalDualCellGeometry grain) (edge : Edge grain) :
    QuantityOccurrence (CellMeasureOrigin grain) primalEdgeMeasureDim where
  origin := .primalEdge edge
  coordinate := geometry.primalEdgeMeasure edge

/-- The dual edge-cell three-volume with its addressed source origin retained. -/
def dualEdgeQuantity (geometry : PositivePrimalDualCellGeometry grain) (edge : Edge grain) :
    QuantityOccurrence (CellMeasureOrigin grain) dualEdgeMeasureDim where
  origin := .dualEdge edge
  coordinate := geometry.dualEdgeMeasure edge

/-- The primal face area with its addressed source origin retained. -/
def primalFaceQuantity (geometry : PositivePrimalDualCellGeometry grain) (face : Face grain) :
    QuantityOccurrence (CellMeasureOrigin grain) primalFaceMeasureDim where
  origin := .primalFace face
  coordinate := geometry.primalFaceMeasure face

/-- The dual face area with its addressed source origin retained. -/
def dualFaceQuantity (geometry : PositivePrimalDualCellGeometry grain) (face : Face grain) :
    QuantityOccurrence (CellMeasureOrigin grain) dualFaceMeasureDim where
  origin := .dualFace face
  coordinate := geometry.dualFaceMeasure face

/-- Equal numerical measure coordinates cannot erase the primal/dual edge provenance. -/
theorem primalEdgeQuantity_origin_ne_dualEdgeQuantity_origin
    (geometry : PositivePrimalDualCellGeometry grain) (edge : Edge grain) :
    (geometry.primalEdgeQuantity edge).origin ≠
      (geometry.dualEdgeQuantity edge).origin := by
  simp [primalEdgeQuantity, dualEdgeQuantity]

/-- Equal numerical measure coordinates cannot erase the primal/dual face provenance. -/
theorem primalFaceQuantity_origin_ne_dualFaceQuantity_origin
    (geometry : PositivePrimalDualCellGeometry grain) (face : Face grain) :
    (geometry.primalFaceQuantity face).origin ≠
      (geometry.dualFaceQuantity face).origin := by
  simp [primalFaceQuantity, dualFaceQuantity]

/-- Exact rational one-cell Hodge ratio `|dual edge| / |primal edge|`. -/
def edgeHodgeWeight (geometry : PositivePrimalDualCellGeometry grain) (edge : Edge grain) : ℚ :=
  geometry.dualEdgeMeasure edge / geometry.primalEdgeMeasure edge

/-- Exact rational two-cell Hodge ratio `|dual face| / |primal face|`. -/
def faceHodgeWeight (geometry : PositivePrimalDualCellGeometry grain) (face : Face grain) : ℚ :=
  geometry.dualFaceMeasure face / geometry.primalFaceMeasure face

theorem edgeHodgeWeight_pos (geometry : PositivePrimalDualCellGeometry grain)
    (edge : Edge grain) :
    0 < geometry.edgeHodgeWeight edge :=
  div_pos (geometry.dualEdgeMeasure_pos edge) (geometry.primalEdgeMeasure_pos edge)

theorem faceHodgeWeight_pos (geometry : PositivePrimalDualCellGeometry grain)
    (face : Face grain) :
    0 < geometry.faceHodgeWeight face :=
  div_pos (geometry.dualFaceMeasure_pos face) (geometry.primalFaceMeasure_pos face)

/-- Exact rational geometry transported into the existing real positive Hodge owner. -/
def toPositiveCellHodge (geometry : PositivePrimalDualCellGeometry grain) :
    PositiveCellHodge grain where
  edgeWeight edge := geometry.edgeHodgeWeight edge
  faceWeight face := geometry.faceHodgeWeight face
  edgeWeight_pos edge := by
    exact_mod_cast geometry.edgeHodgeWeight_pos edge
  faceWeight_pos face := by
    exact_mod_cast geometry.faceHodgeWeight_pos face

@[simp] theorem toPositiveCellHodge_edgeWeight
    (geometry : PositivePrimalDualCellGeometry grain) (edge : Edge grain) :
    geometry.toPositiveCellHodge.edgeWeight edge = geometry.edgeHodgeWeight edge := rfl

@[simp] theorem toPositiveCellHodge_faceWeight
    (geometry : PositivePrimalDualCellGeometry grain) (face : Face grain) :
    geometry.toPositiveCellHodge.faceWeight face = geometry.faceHodgeWeight face := rfl

end PositivePrimalDualCellGeometry

/-! ## Exact midpoint polarization and Poynting/current return -/

/-- The exact arithmetic midpoint of two successive field occurrences. -/
def midpointSection {V : Type*} [AddCommGroup V] [Module ℝ V]
    (history : ℕ → V) (time : ℕ) : V :=
  (2 : ℝ)⁻¹ • (history (time + 1) + history time)

/-- Coordinate-free finite polarization reduced to one exact weighted finite sum. -/
theorem weighted_midpoint_difference
    {Index : Type*} [Fintype Index]
    (weight source target : Index → ℝ) :
    (∑ index, weight index * ((2 : ℝ)⁻¹ * (target index + source index)) *
        (target index - source index)) =
      (2 : ℝ)⁻¹ *
        ((∑ index, weight index * target index * target index) -
          ∑ index, weight index * source index * source index) := by
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

namespace PositiveCellHodge

theorem edgePairing_sub_right (hodge : PositiveCellHodge grain)
    (left right remainder : EdgeSection grain) :
    hodge.edgePairing left (right - remainder) =
      hodge.edgePairing left right - hodge.edgePairing left remainder := by
  simp only [PositiveCellHodge.edgePairing, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  ring

theorem facePairing_neg_right (hodge : PositiveCellHodge grain)
    (left right : FaceSection grain) :
    hodge.facePairing left (-right) = -hodge.facePairing left right := by
  simp only [PositiveCellHodge.facePairing, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro face _
  ring

/-- Stored electromagnetic field energy in the declared finite Hodge receiver. -/
def fieldEnergy (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) (magnetic : FaceSection grain) : ℝ :=
  (2 : ℝ)⁻¹ *
    (hodge.edgePairing electric electric + hodge.facePairing magnetic magnetic)

theorem edge_midpoint_pairing_firstDifference
    (hodge : PositiveCellHodge grain) (electric : ℕ → EdgeSection grain) (time : ℕ) :
    hodge.edgePairing (midpointSection electric time) (firstDifference electric time) =
      (2 : ℝ)⁻¹ *
        (hodge.edgePairing (electric (time + 1)) (electric (time + 1)) -
          hodge.edgePairing (electric time) (electric time)) := by
  simpa only [PositiveCellHodge.edgePairing, midpointSection, firstDifference,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] using
      (weighted_midpoint_difference hodge.edgeWeight (electric time) (electric (time + 1)))

theorem face_midpoint_pairing_firstDifference
    (hodge : PositiveCellHodge grain) (magnetic : ℕ → FaceSection grain) (time : ℕ) :
    hodge.facePairing (midpointSection magnetic time) (firstDifference magnetic time) =
      (2 : ℝ)⁻¹ *
        (hodge.facePairing (magnetic (time + 1)) (magnetic (time + 1)) -
          hodge.facePairing (magnetic time) (magnetic time)) := by
  simpa only [PositiveCellHodge.facePairing, midpointSection, firstDifference,
    Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul] using
      (weighted_midpoint_difference hodge.faceWeight (magnetic time) (magnetic (time + 1)))

/-- Exact field-energy difference, with no forward-step remainder. -/
theorem fieldEnergy_firstDifference
    (hodge : PositiveCellHodge grain)
    (electric : ℕ → EdgeSection grain) (magnetic : ℕ → FaceSection grain) (time : ℕ) :
    hodge.fieldEnergy (electric (time + 1)) (magnetic (time + 1)) -
        hodge.fieldEnergy (electric time) (magnetic time) =
      hodge.edgePairing (midpointSection electric time) (firstDifference electric time) +
        hodge.facePairing (midpointSection magnetic time) (firstDifference magnetic time) := by
  rw [hodge.edge_midpoint_pairing_firstDifference electric time,
    hodge.face_midpoint_pairing_firstDifference magnetic time]
  simp only [fieldEnergy]
  ring

/-- Failure of the proposed face-to-edge law to be the Hodge adjoint of curl.  On a cut body this
is the exact boundary/interface power, not an approximation error. -/
def boundaryPower (hodge : PositiveCellHodge grain)
    (faceToEdge : FaceSection grain →ₗ[ℝ] EdgeSection grain)
    (electric : EdgeSection grain) (magnetic : FaceSection grain) : ℝ :=
  hodge.facePairing (cellularCurl grain electric) magnetic -
    hodge.edgePairing electric (faceToEdge magnetic)

/-- The complete material co-curl closes the boundary-power port on the closed carrier. -/
theorem boundaryPower_materialCoCurl_eq_zero
    (hodge : PositiveCellHodge grain)
    (electric : EdgeSection grain) (magnetic : FaceSection grain) :
    hodge.boundaryPower hodge.coCurl electric magnetic = 0 := by
  rw [boundaryPower, hodge.adjoint]
  exact sub_self _

/-- Exact finite Poynting law for one midpoint Maxwell grain. -/
theorem poynting_balance
    (hodge : PositiveCellHodge grain)
    (faceToEdge : FaceSection grain →ₗ[ℝ] EdgeSection grain)
    (electric : ℕ → EdgeSection grain) (magnetic : ℕ → FaceSection grain)
    (current : ℕ → EdgeSection grain) (time : ℕ)
    (faraday : firstDifference magnetic time =
      -(cellularCurl grain) (midpointSection electric time))
    (ampere : firstDifference electric time =
      faceToEdge (midpointSection magnetic time) - current time) :
    hodge.fieldEnergy (electric (time + 1)) (magnetic (time + 1)) -
        hodge.fieldEnergy (electric time) (magnetic time) +
        hodge.boundaryPower faceToEdge (midpointSection electric time)
          (midpointSection magnetic time) +
        hodge.edgePairing (midpointSection electric time) (current time) = 0 := by
  rw [hodge.fieldEnergy_firstDifference electric magnetic time, faraday, ampere]
  rw [hodge.edgePairing_sub_right, hodge.facePairing_neg_right,
    hodge.facePairing_comm (midpointSection magnetic time)
      ((cellularCurl grain) (midpointSection electric time))]
  simp only [boundaryPower]
  ring

end PositiveCellHodge

/-- One exact midpoint Maxwell history.  `faceToEdge` may be the closed material co-curl or an
open/interface operator whose adjoint defect is returned as boundary power. -/
structure MidpointMaxwellHistory (hodge : PositiveCellHodge grain) where
  faceToEdge : FaceSection grain →ₗ[ℝ] EdgeSection grain
  electric : ℕ → EdgeSection grain
  magnetic : ℕ → FaceSection grain
  current : ℕ → EdgeSection grain
  faraday : ∀ time, firstDifference magnetic time =
    -(cellularCurl grain) (midpointSection electric time)
  ampere : ∀ time, firstDifference electric time =
    faceToEdge (midpointSection magnetic time) - current time

namespace MidpointMaxwellHistory

def energy (history : MidpointMaxwellHistory hodge) (time : ℕ) : ℝ :=
  hodge.fieldEnergy (history.electric time) (history.magnetic time)

def outwardBoundaryPower (history : MidpointMaxwellHistory hodge) (time : ℕ) : ℝ :=
  hodge.boundaryPower history.faceToEdge (midpointSection history.electric time)
    (midpointSection history.magnetic time)

def sourceWork (history : MidpointMaxwellHistory hodge) (time : ℕ) : ℝ :=
  hodge.edgePairing (midpointSection history.electric time) (history.current time)

theorem localBalance (history : MidpointMaxwellHistory hodge) (time : ℕ) :
    history.energy (time + 1) - history.energy time +
        history.outwardBoundaryPower time = -history.sourceWork time := by
  have returned := hodge.poynting_balance history.faceToEdge history.electric
    history.magnetic history.current time (history.faraday time) (history.ampere time)
  simpa only [energy, outwardBoundaryPower, sourceWork] using eq_neg_of_add_eq_zero_left returned

/-- The electromagnetic history is exactly one instance of the standing current-balance owner. -/
def toCurrentBalance (history : MidpointMaxwellHistory hodge) : CurrentBalance ℝ where
  storage := history.energy
  outwardFlux := history.outwardBoundaryPower
  production := fun time ↦ -history.sourceWork time
  localBalance := history.localBalance

/-- Complete finite world-tube Poynting ledger. -/
theorem telescopes (history : MidpointMaxwellHistory hodge) (steps : ℕ) :
    history.energy steps - history.energy 0 +
        ∑ time ∈ Finset.range steps, history.outwardBoundaryPower time =
      ∑ time ∈ Finset.range steps, -history.sourceWork time := by
  exact history.toCurrentBalance.telescopes steps

/-- Nonnegative outward power and nonnegative material work make stored field energy descend. -/
theorem energy_antitone_step
    (history : MidpointMaxwellHistory hodge) (time : ℕ)
    (boundary_nonnegative : 0 ≤ history.outwardBoundaryPower time)
    (work_nonnegative : 0 ≤ history.sourceWork time) :
    history.energy (time + 1) ≤ history.energy time := by
  have returned := history.localBalance time
  linarith

/-- On the closed material carrier with no source work, the exact midpoint law conserves energy. -/
theorem closed_material_sourceFree_conserves
    (history : MidpointMaxwellHistory hodge) (time : ℕ)
    (material : history.faceToEdge = hodge.coCurl)
    (sourceFree : history.current time = 0) :
    history.energy (time + 1) = history.energy time := by
  have returned := hodge.poynting_balance history.faceToEdge history.electric
    history.magnetic history.current time (history.faraday time) (history.ampere time)
  have hboundary : history.outwardBoundaryPower time = 0 := by
    simp only [outwardBoundaryPower, material]
    exact hodge.boundaryPower_materialCoCurl_eq_zero _ _
  have hwork : history.sourceWork time = 0 := by
    simp [sourceWork, sourceFree, PositiveCellHodge.edgePairing]
  change history.energy (time + 1) - history.energy time +
      history.outwardBoundaryPower time + history.sourceWork time = 0 at returned
  rw [hboundary, hwork] at returned
  linarith

end MidpointMaxwellHistory

/-! ## Constituted scale passage -/

/-- One passage between two cell grains which preserves both differential directions and the
complete bilinear energy receivers. -/
structure CellHodgeScalePassage
    {fineGrain coarseGrain : ℕ}
    (fineHodge : PositiveCellHodge fineGrain)
    (coarseHodge : PositiveCellHodge coarseGrain) where
  edgeTransport : EdgeSection fineGrain →ₗ[ℝ] EdgeSection coarseGrain
  faceTransport : FaceSection fineGrain →ₗ[ℝ] FaceSection coarseGrain
  curl_natural :
    (cellularCurl coarseGrain).comp edgeTransport =
      faceTransport.comp (cellularCurl fineGrain)
  coCurl_natural :
    coarseHodge.coCurl.comp faceTransport = edgeTransport.comp fineHodge.coCurl
  edgePairing_natural : ∀ left right,
    coarseHodge.edgePairing (edgeTransport left) (edgeTransport right) =
      fineHodge.edgePairing left right
  facePairing_natural : ∀ left right,
    coarseHodge.facePairing (faceTransport left) (faceTransport right) =
      fineHodge.facePairing left right

namespace CellHodgeScalePassage

variable {fineGrain middleGrain coarseGrain : ℕ}
variable {fineHodge : PositiveCellHodge fineGrain}
variable {middleHodge : PositiveCellHodge middleGrain}
variable {coarseHodge : PositiveCellHodge coarseGrain}

theorem transport_curl
    (passage : CellHodgeScalePassage fineHodge coarseHodge)
    (electric : EdgeSection fineGrain) :
    cellularCurl coarseGrain (passage.edgeTransport electric) =
      passage.faceTransport (cellularCurl fineGrain electric) := by
  exact LinearMap.congr_fun passage.curl_natural electric

theorem transport_coCurl
    (passage : CellHodgeScalePassage fineHodge coarseHodge)
    (magnetic : FaceSection fineGrain) :
    coarseHodge.coCurl (passage.faceTransport magnetic) =
      passage.edgeTransport (fineHodge.coCurl magnetic) := by
  exact LinearMap.congr_fun passage.coCurl_natural magnetic

/-- The complete constituted field-energy receiver is invariant through the scale passage. -/
theorem fieldEnergy_natural
    (passage : CellHodgeScalePassage fineHodge coarseHodge)
    (electric : EdgeSection fineGrain) (magnetic : FaceSection fineGrain) :
    coarseHodge.fieldEnergy (passage.edgeTransport electric) (passage.faceTransport magnetic) =
      fineHodge.fieldEnergy electric magnetic := by
  simp only [PositiveCellHodge.fieldEnergy]
  rw [passage.edgePairing_natural, passage.facePairing_natural]

/-- Complete Hodge-pairing preservation forbids loss of an edge-current direction. -/
theorem edgeTransport_injective
    (passage : CellHodgeScalePassage fineHodge coarseHodge) :
    Function.Injective passage.edgeTransport := by
  intro left right equal
  have htransport : passage.edgeTransport (left - right) = 0 := by
    rw [map_sub, equal, sub_self]
  have hpair : fineHodge.edgePairing (left - right) (left - right) = 0 := by
    rw [← passage.edgePairing_natural]
    rw [htransport]
    simp [PositiveCellHodge.edgePairing]
  exact sub_eq_zero.mp ((fineHodge.edgePairing_self_eq_zero_iff (left - right)).mp hpair)

/-- Complete Hodge-pairing preservation forbids loss of a face-flux direction. -/
theorem faceTransport_injective
    (passage : CellHodgeScalePassage fineHodge coarseHodge) :
    Function.Injective passage.faceTransport := by
  intro left right equal
  have htransport : passage.faceTransport (left - right) = 0 := by
    rw [map_sub, equal, sub_self]
  have hpair : fineHodge.facePairing (left - right) (left - right) = 0 := by
    rw [← passage.facePairing_natural]
    rw [htransport]
    simp [PositiveCellHodge.facePairing]
  exact sub_eq_zero.mp ((fineHodge.facePairing_self_eq_zero_iff (left - right)).mp hpair)

/-- A genuinely lossy edge receiver cannot be promoted to a complete constituted scale passage. -/
theorem no_passage_with_noninjective_edgeTransport
    (transport : EdgeSection fineGrain →ₗ[ℝ] EdgeSection coarseGrain)
    (notInjective : ¬ Function.Injective transport) :
    ¬ ∃ passage : CellHodgeScalePassage fineHodge coarseHodge,
      passage.edgeTransport = transport := by
  rintro ⟨passage, equal⟩
  apply notInjective
  rw [← equal]
  exact passage.edgeTransport_injective

/-- A genuinely lossy face receiver cannot be promoted to a complete constituted scale passage. -/
theorem no_passage_with_noninjective_faceTransport
    (transport : FaceSection fineGrain →ₗ[ℝ] FaceSection coarseGrain)
    (notInjective : ¬ Function.Injective transport) :
    ¬ ∃ passage : CellHodgeScalePassage fineHodge coarseHodge,
      passage.faceTransport = transport := by
  rintro ⟨passage, equal⟩
  apply notInjective
  rw [← equal]
  exact passage.faceTransport_injective

/-- The zero edge receiver is a concrete lossy scale map on every nonempty four-torus grain. -/
def zeroEdgeTransport :
    EdgeSection fineGrain →ₗ[ℝ] EdgeSection coarseGrain := 0

theorem zeroEdgeTransport_not_injective :
    ¬ Function.Injective (zeroEdgeTransport (fineGrain := fineGrain)
      (coarseGrain := coarseGrain)) := by
  intro injective
  let unitSection : EdgeSection fineGrain := fun _ ↦ 1
  have collapsed :
      zeroEdgeTransport (fineGrain := fineGrain) (coarseGrain := coarseGrain) unitSection =
        zeroEdgeTransport (fineGrain := fineGrain) (coarseGrain := coarseGrain) 0 := by
    rfl
  have identified := injective collapsed
  let edge : Edge fineGrain := ⟨0, fun _ ↦ 0⟩
  have coordinate := congrFun identified edge
  norm_num [unitSection] at coordinate

/-- The concrete zero receiver fires the complete-energy insufficiency condition. -/
theorem no_passage_through_zeroEdgeTransport :
    ¬ ∃ passage : CellHodgeScalePassage fineHodge coarseHodge,
      passage.edgeTransport =
        zeroEdgeTransport (fineGrain := fineGrain) (coarseGrain := coarseGrain) := by
  exact no_passage_with_noninjective_edgeTransport
    (zeroEdgeTransport (fineGrain := fineGrain) (coarseGrain := coarseGrain))
    zeroEdgeTransport_not_injective

/-- Constituted scale passages compose without losing curl, co-curl, or energy naturality. -/
def comp
    (fineToMiddle : CellHodgeScalePassage fineHodge middleHodge)
    (middleToCoarse : CellHodgeScalePassage middleHodge coarseHodge) :
    CellHodgeScalePassage fineHodge coarseHodge where
  edgeTransport := middleToCoarse.edgeTransport.comp fineToMiddle.edgeTransport
  faceTransport := middleToCoarse.faceTransport.comp fineToMiddle.faceTransport
  curl_natural := by
    apply LinearMap.ext
    intro electric
    simp only [LinearMap.comp_apply]
    calc
      cellularCurl coarseGrain
          (middleToCoarse.edgeTransport (fineToMiddle.edgeTransport electric)) =
        middleToCoarse.faceTransport
          (cellularCurl middleGrain (fineToMiddle.edgeTransport electric)) :=
            middleToCoarse.transport_curl (fineToMiddle.edgeTransport electric)
      _ = middleToCoarse.faceTransport
          (fineToMiddle.faceTransport (cellularCurl fineGrain electric)) :=
            congrArg middleToCoarse.faceTransport (fineToMiddle.transport_curl electric)
  coCurl_natural := by
    apply LinearMap.ext
    intro magnetic
    simp only [LinearMap.comp_apply]
    calc
      coarseHodge.coCurl
          (middleToCoarse.faceTransport (fineToMiddle.faceTransport magnetic)) =
        middleToCoarse.edgeTransport
          (middleHodge.coCurl (fineToMiddle.faceTransport magnetic)) :=
            middleToCoarse.transport_coCurl (fineToMiddle.faceTransport magnetic)
      _ = middleToCoarse.edgeTransport
          (fineToMiddle.edgeTransport (fineHodge.coCurl magnetic)) :=
            congrArg middleToCoarse.edgeTransport (fineToMiddle.transport_coCurl magnetic)
  edgePairing_natural left right := by
    calc
      coarseHodge.edgePairing
          (middleToCoarse.edgeTransport (fineToMiddle.edgeTransport left))
          (middleToCoarse.edgeTransport (fineToMiddle.edgeTransport right)) =
        middleHodge.edgePairing (fineToMiddle.edgeTransport left)
          (fineToMiddle.edgeTransport right) := middleToCoarse.edgePairing_natural _ _
      _ = fineHodge.edgePairing left right := fineToMiddle.edgePairing_natural _ _
  facePairing_natural left right := by
    calc
      coarseHodge.facePairing
          (middleToCoarse.faceTransport (fineToMiddle.faceTransport left))
          (middleToCoarse.faceTransport (fineToMiddle.faceTransport right)) =
        middleHodge.facePairing (fineToMiddle.faceTransport left)
          (fineToMiddle.faceTransport right) := middleToCoarse.facePairing_natural _ _
      _ = fineHodge.facePairing left right := fineToMiddle.facePairing_natural _ _

theorem comp_fieldEnergy_natural
    (fineToMiddle : CellHodgeScalePassage fineHodge middleHodge)
    (middleToCoarse : CellHodgeScalePassage middleHodge coarseHodge)
    (electric : EdgeSection fineGrain) (magnetic : FaceSection fineGrain) :
    coarseHodge.fieldEnergy
        ((fineToMiddle.comp middleToCoarse).edgeTransport electric)
        ((fineToMiddle.comp middleToCoarse).faceTransport magnetic) =
      fineHodge.fieldEnergy electric magnetic := by
  exact (fineToMiddle.comp middleToCoarse).fieldEnergy_natural electric magnetic

end CellHodgeScalePassage

/-! ## Positive curl--curl actions -/

/-- Face wave action `curl ∘ coCurl`. -/
def faceCurlCurl (grain : ℕ) : FaceSection grain →ₗ[ℝ] FaceSection grain :=
  (cellularCurl grain).comp (cellularCoCurl grain)

/-- Edge wave action `coCurl ∘ curl`. -/
def edgeCurlCurl (grain : ℕ) : EdgeSection grain →ₗ[ℝ] EdgeSection grain :=
  (cellularCoCurl grain).comp (cellularCurl grain)

theorem faceCurlCurl_pairing_self (magnetic : FaceSection grain) :
    facePairing (faceCurlCurl grain magnetic) magnetic =
      ∑ edge, (cellularCoCurl grain magnetic edge) ^ 2 := by
  rw [show facePairing (faceCurlCurl grain magnetic) magnetic =
      facePairing (cellularCurl grain (cellularCoCurl grain magnetic)) magnetic by rfl]
  rw [cellularCurl_adjoint]
  simp [edgePairing, pow_two]

theorem edgeCurlCurl_pairing_self (electric : EdgeSection grain) :
    edgePairing (edgeCurlCurl grain electric) electric =
      ∑ face, (cellularCurl grain electric face) ^ 2 := by
  rw [edgePairing_comm]
  change edgePairing electric
    (cellularCoCurl grain (cellularCurl grain electric)) = _
  rw [← cellularCurl_adjoint]
  simp [facePairing, pow_two]

theorem faceCurlCurl_pairing_nonneg (magnetic : FaceSection grain) :
    0 ≤ facePairing (faceCurlCurl grain magnetic) magnetic := by
  rw [faceCurlCurl_pairing_self]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem edgeCurlCurl_pairing_nonneg (electric : EdgeSection grain) :
    0 ≤ edgePairing (edgeCurlCurl grain electric) electric := by
  rw [edgeCurlCurl_pairing_self]
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

/-! ## Preimage fibres -/

def cellularCurlAddHom (grain : ℕ) : EdgeSection grain →+ FaceSection grain :=
  { toFun := cellularCurl grain
    map_zero' := (cellularCurl grain).map_zero
    map_add' := (cellularCurl grain).map_add }

def cellularCoCurlAddHom (grain : ℕ) : FaceSection grain →+ EdgeSection grain :=
  { toFun := cellularCoCurl grain
    map_zero' := (cellularCoCurl grain).map_zero
    map_add' := (cellularCoCurl grain).map_add }

abbrev CurlFibre (grain : ℕ) (reading : FaceSection grain) :=
  Lift.PreimageFibre (cellularCurlAddHom grain) reading

abbrev CoCurlFibre (grain : ℕ) (reading : EdgeSection grain) :=
  Lift.PreimageFibre (cellularCoCurlAddHom grain) reading

/-- Every exact nodal drop is an explicit direction in the curl receiver's radical. -/
theorem exactDrop_mem_cellularCurl_kernel (state : NodeSection grain) :
    (fun edge ↦ branchDrop cellularIncidence state edge) ∈
      (cellularCurlAddHom grain).ker := by
  rw [AddMonoidHom.mem_ker]
  funext face
  change faceCirculation (fun edge ↦ branchDrop cellularIncidence state edge) face = 0
  exact faceCirculation_exactDrop_eq_zero state face

/-- Once one curl antecedent is known, every other antecedent is exactly a kernel translation. -/
def curlFibreEquivKernel (reading : FaceSection grain) (base : CurlFibre grain reading) :
    CurlFibre grain reading ≃ (cellularCurlAddHom grain).ker :=
  Lift.fibreEquivKernel (cellularCurlAddHom grain) base

/-- The same complete-fibre law for the coordinate co-curl receiver. -/
def coCurlFibreEquivKernel (reading : EdgeSection grain) (base : CoCurlFibre grain reading) :
    CoCurlFibre grain reading ≃ (cellularCoCurlAddHom grain).ker :=
  Lift.fibreEquivKernel (cellularCoCurlAddHom grain) base

/-! ## Concrete cellular histories inherit the common wave law -/

/-- A source-free coordinate Maxwell history on one addressed four-torus grain. -/
structure CellularMaxwellHistory (grain : ℕ) where
  permeability : ℝ
  permittivity : ℝ
  permeability_pos : 0 < permeability
  permittivity_pos : 0 < permittivity
  electric : ℕ → EdgeSection grain
  magnetic : ℕ → FaceSection grain
  faraday : ∀ time,
    firstDifference magnetic time = -(cellularCurl grain) (electric time)
  ampereMaxwell : ∀ time,
    permittivity • firstDifference electric time =
      permeability⁻¹ • (cellularCoCurl grain) (magnetic time)

namespace CellularMaxwellHistory

def toVacuumMaxwellPassage (history : CellularMaxwellHistory grain) :
    VacuumMaxwellPassage (Electric := EdgeSection grain) (Magnetic := FaceSection grain) where
  permeability := history.permeability
  permittivity := history.permittivity
  permeability_pos := history.permeability_pos
  permittivity_pos := history.permittivity_pos
  electricCurl := cellularCurl grain
  magneticCurl := cellularCoCurl grain
  electric := history.electric
  magnetic := history.magnetic
  faraday := history.faraday
  ampereMaxwell := history.ampereMaxwell

/-- The concrete edge-field wave law with the exact constitutive coefficient. -/
theorem electric_secondDifference (history : CellularMaxwellHistory grain) (time : ℕ) :
    secondDifference history.electric time =
      (-history.toVacuumMaxwellPassage.propagationSpeedSquared) •
        edgeCurlCurl grain (history.electric time) := by
  exact history.toVacuumMaxwellPassage.electric_secondDifference time

/-- The concrete face-flux wave law with the exact constitutive coefficient. -/
theorem magnetic_secondDifference (history : CellularMaxwellHistory grain) (time : ℕ) :
    secondDifference history.magnetic time =
      (-history.toVacuumMaxwellPassage.propagationSpeedSquared) •
        faceCurlCurl grain (history.magnetic time) := by
  exact history.toVacuumMaxwellPassage.magnetic_secondDifference time

end CellularMaxwellHistory

end Soma.Holonics.Millennium.HolonicDiscreteMaxwellOperator

section Audit
open Soma.Holonics.Millennium.HolonicDiscreteMaxwellOperator
#print axioms faceBoundaryIncrements_sum
#print axioms faceConnectionHolonomy_eq_curlTranslation
#print axioms cellularCurl_adjoint
#print axioms PositiveCellHodge.adjoint
#print axioms PositiveCellHodge.edgePairing_self_nonneg
#print axioms PositiveCellHodge.facePairing_self_nonneg
#print axioms PositiveCellHodge.edgePairing_self_eq_zero_iff
#print axioms PositiveCellHodge.facePairing_self_eq_zero_iff
#print axioms PositiveCellHodge.faceCurlCurl_pairing_self
#print axioms PositiveCellHodge.edgeCurlCurl_pairing_self
#print axioms PositiveCellHodge.faceCurlCurl_pairing_nonneg
#print axioms PositiveCellHodge.edgeCurlCurl_pairing_nonneg
#print axioms PositivePrimalDualCellGeometry.primalEdgeQuantity_origin_ne_dualEdgeQuantity_origin
#print axioms PositivePrimalDualCellGeometry.primalFaceQuantity_origin_ne_dualFaceQuantity_origin
#print axioms PositivePrimalDualCellGeometry.edgeHodgeWeight_pos
#print axioms PositivePrimalDualCellGeometry.faceHodgeWeight_pos
#print axioms weighted_midpoint_difference
#print axioms PositiveCellHodge.fieldEnergy_firstDifference
#print axioms PositiveCellHodge.boundaryPower_materialCoCurl_eq_zero
#print axioms PositiveCellHodge.poynting_balance
#print axioms MidpointMaxwellHistory.localBalance
#print axioms MidpointMaxwellHistory.telescopes
#print axioms MidpointMaxwellHistory.energy_antitone_step
#print axioms MidpointMaxwellHistory.closed_material_sourceFree_conserves
#print axioms CellHodgeScalePassage.fieldEnergy_natural
#print axioms CellHodgeScalePassage.edgeTransport_injective
#print axioms CellHodgeScalePassage.faceTransport_injective
#print axioms CellHodgeScalePassage.no_passage_with_noninjective_edgeTransport
#print axioms CellHodgeScalePassage.no_passage_with_noninjective_faceTransport
#print axioms CellHodgeScalePassage.zeroEdgeTransport_not_injective
#print axioms CellHodgeScalePassage.no_passage_through_zeroEdgeTransport
#print axioms CellHodgeScalePassage.comp_fieldEnergy_natural
#print axioms faceCurlCurl_pairing_self
#print axioms edgeCurlCurl_pairing_self
#print axioms faceCurlCurl_pairing_nonneg
#print axioms edgeCurlCurl_pairing_nonneg
#print axioms exactDrop_mem_cellularCurl_kernel
#print axioms CellularMaxwellHistory.electric_secondDifference
#print axioms CellularMaxwellHistory.magnetic_secondDifference
end Audit

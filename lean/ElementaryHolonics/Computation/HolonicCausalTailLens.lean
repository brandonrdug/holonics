import ElementaryHolonics.Computation.HolonicOrientedSiteTransport
import ElementaryHolonics.Foundation.HolonTensorLens
import Mathlib.Data.NNReal.Defs

/-!
# The causal-tail lens over addressed neural current

This exterior receiver groups a complete finite addressed pair-current section by a declared depth
and returns nonnegative energy at each depth. The signed or complex current and both endpoint
indices remain in the source holons and complete preimage fibres. The scalar receiver never becomes
native morphology or a transport governor.

The causal-depth section is presented as one rank-one tensor slot. Depth labels are coordinates in
that vector slot, not tensor slots whose tensor product would multiply and erase the section.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicCausalTailLens

open scoped BigOperators TensorProduct
open Soma.Holonics.Computation.HolonicOrientedSiteTransport

universe uS uC uD uD' uI uP

/-- A complete current section still indexed by both oriented endpoints. -/
abbrev AddressedPairSection (Site : Type uS) (Current : Type uC) := Site → Site → Current

/-- Exterior depth and nonnegative-energy receiver over one finite addressed pair population. -/
structure CausalTailLens (Site : Type uS) (Current : Type uC) (Depth : Type uD)
    [Fintype Site] [Fintype Depth] [DecidableEq Depth] [Zero Current] where
  depth : Site → Site → Depth
  energy : Current → NNReal
  energy_zero : energy 0 = 0

namespace CausalTailLens

variable {Site : Type uS} {Current : Type uC} {Depth : Type uD}
variable [Fintype Site] [Fintype Depth] [DecidableEq Depth] [Zero Current]

/-- Sum exactly those pair-energy faces at the receiver-declared depth. -/
def project (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) : Depth → NNReal :=
  fun depth ↦ ∑ target : Site, ∑ source : Site,
    if lens.depth target source = depth then lens.energy (currents target source) else 0

@[simp] theorem project_zero (lens : CausalTailLens Site Current Depth) :
    lens.project (0 : AddressedPairSection Site Current) = 0 := by
  funext depth
  simp [project, lens.energy_zero]

/-- Every pair remains an occurrence with source and target addresses. -/
def addressedPairHolon (currents : AddressedPairSection Site Current) :
    Holon Site Site Current where
  Occurrence := Site × Site
  source pair := pair.2
  target pair := pair.1
  receive pair := currents pair.1 pair.2

/-- The pointwise energy receiver preserves the same addressed occurrence population. -/
def pointEnergyHolon (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) : Holon Site Site NNReal where
  Occurrence := Site × Site
  source pair := pair.2
  target pair := pair.1
  receive pair := lens.energy (currents pair.1 pair.2)

/-- One addressed pair inhabits the literal preimage of its returned point-energy face. -/
def pointEnergyPreimageOfPair (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) (target source : Site) :
    (lens.pointEnergyHolon currents).PreimageFibre (lens.energy (currents target source)) :=
  ⟨(target, source), rfl⟩

/-- The population holon retains the complete addressed section behind a depth face. -/
def populationHolon (lens : CausalTailLens Site Current Depth) :
    Holon (AddressedPairSection Site Current) (Depth → NNReal) (Depth → NNReal) where
  Occurrence := AddressedPairSection Site Current
  source currents := currents
  target currents := lens.project currents
  receive currents := lens.project currents

/-- A complete addressed section inhabits the literal preimage of its returned depth face. -/
def populationPreimageOf (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) :
    lens.populationHolon.PreimageFibre (lens.project currents) :=
  ⟨currents, rfl⟩

/-- Relabel only the exterior depth chart. -/
def relabel {Depth' : Type uD'} [Fintype Depth'] [DecidableEq Depth']
    (lens : CausalTailLens Site Current Depth) (e : Depth ≃ Depth') :
    CausalTailLens Site Current Depth' where
  depth target source := e (lens.depth target source)
  energy := lens.energy
  energy_zero := lens.energy_zero

/-- Relabel a depth-vector's coordinates by equivalence. -/
def relabelSectionLinearEquiv {Depth' : Type uD'} [Fintype Depth']
    (e : Depth ≃ Depth') : (Depth → NNReal) ≃ₗ[NNReal] (Depth' → NNReal) :=
  LinearEquiv.piCongrLeft' NNReal (fun _ : Depth ↦ NNReal) e

/-- Depth relabeling commutes exactly with the causal-tail projection. -/
theorem relabelSectionLinearEquiv_project {Depth' : Type uD'}
    [Fintype Depth'] [DecidableEq Depth']
    (lens : CausalTailLens Site Current Depth) (e : Depth ≃ Depth')
    (currents : AddressedPairSection Site Current) :
    relabelSectionLinearEquiv e (lens.project currents) =
      (lens.relabel e).project currents := by
  funext depth'
  simp [relabelSectionLinearEquiv, project, relabel, Equiv.eq_symm_apply]
  rfl

/-- Depth relabeling is a rebase of the complete population diagram. -/
def populationHolonRebase {Depth' : Type uD'} [Fintype Depth'] [DecidableEq Depth']
    (lens : CausalTailLens Site Current Depth) (e : Depth ≃ Depth') :
    Holon.Rebase lens.populationHolon (lens.relabel e).populationHolon where
  occurrenceEquiv := Equiv.refl _
  sourceEquiv := Equiv.refl _
  targetEquiv := (relabelSectionLinearEquiv e).toEquiv
  faceEquiv := (relabelSectionLinearEquiv e).toEquiv
  source_natural _ := rfl
  target_natural currents := relabelSectionLinearEquiv_project lens e currents
  receive_natural currents := relabelSectionLinearEquiv_project lens e currents

/-- Relabeling transports the complete population preimage, not only its displayed face. -/
def relabelPreimageFibreEquiv {Depth' : Type uD'} [Fintype Depth'] [DecidableEq Depth']
    (lens : CausalTailLens Site Current Depth) (e : Depth ≃ Depth')
    (face : Depth → NNReal) :
    lens.populationHolon.PreimageFibre face ≃
      (lens.relabel e).populationHolon.PreimageFibre (relabelSectionLinearEquiv e face) :=
  (populationHolonRebase lens e).preimageFibreEquiv face

/-! ## Rank-one tensor presentation -/

/-- The depth vector is one rank-one tensor slot; depth labels remain coordinates in that slot. -/
abbrev CausalTailTensorFace (Depth : Type uD) [Fintype Depth] :=
  TensorFace NNReal (fun _ : Fin 1 ↦ Depth → NNReal)

/-- Present the complete depth section as a rank-one tensor face. -/
def tensorFace (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) : CausalTailTensorFace Depth :=
  PiTensorProduct.tprod NNReal (fun _ : Fin 1 ↦ lens.project currents)

/-- The causal-tail projection through the standing tensor-lens owner. -/
def tensorLens (lens : CausalTailLens Site Current Depth) :
    TensorLens (AddressedPairSection Site Current) NNReal (Fin 1)
      (fun _ ↦ Depth → NNReal) where
  project := lens.tensorFace

/-- Relabel vector coordinates inside the single rank-one tensor slot. -/
def tensorRelabel {Depth' : Type uD'} [Fintype Depth'] (e : Depth ≃ Depth') :
    CausalTailTensorFace Depth ≃ₗ[NNReal] CausalTailTensorFace Depth' :=
  PiTensorProduct.congr (fun _ : Fin 1 ↦ relabelSectionLinearEquiv e)

/-- Exact depth relabeling preserves the rank-one tensor face. -/
theorem tensorRelabel_tensorFace {Depth' : Type uD'}
    [Fintype Depth'] [DecidableEq Depth']
    (lens : CausalTailLens Site Current Depth) (e : Depth ≃ Depth')
    (currents : AddressedPairSection Site Current) :
    tensorRelabel e (lens.tensorFace currents) = (lens.relabel e).tensorFace currents := by
  rw [tensorRelabel, tensorFace, tensorFace, PiTensorProduct.congr_tprod]
  congr 1
  funext _axis
  exact relabelSectionLinearEquiv_project lens e currents

end CausalTailLens

/-! ## Composition with the standing oriented neural transport -/

variable {Scalar : Type*} {Site : Type uS} {Incidence : Type uI} {Port : Type uP}
variable [CommSemiring Scalar] [Fintype Site] [Fintype Incidence]

/-- Existing oriented transport supplies the complete addressed source section definitionally. -/
def orientedPairSection (T : OrientedPortSiteTransport Scalar Site Incidence Port)
    (port : Port) (state : Site → Scalar) : AddressedPairSection Site Scalar :=
  fun target source ↦ T.pairCurrent port state target source

/-- The section is definitionally the local-current field of the standing neural ecology. -/
theorem orientedPairSection_eq_ecology_localCurrent
    (T : OrientedPortSiteTransport Scalar Site Incidence Port)
    (port : Port) (state : Site → Scalar) (target source : Site) :
    orientedPairSection T port state target source =
      (OrientedPortSiteTransport.ecology
        (Scalar := Scalar) (Site := Site) (Incidence := Incidence) (Port := Port)).localCurrent
          T port state target source := rfl

/-- The addressed source holon receives the standing pair current without an intermediate chart. -/
theorem orientedPairSection_holon_receive
    (T : OrientedPortSiteTransport Scalar Site Incidence Port)
    (port : Port) (state : Site → Scalar) (target source : Site) :
    (CausalTailLens.addressedPairHolon (orientedPairSection T port state)).receive
      (target, source) = T.pairCurrent port state target source := rfl

end Soma.Holonics.Computation.HolonicCausalTailLens

section Audit
open Soma.Holonics.Computation.HolonicCausalTailLens
#print axioms CausalTailLens.project_zero
#print axioms CausalTailLens.pointEnergyPreimageOfPair
#print axioms CausalTailLens.populationPreimageOf
#print axioms CausalTailLens.relabelSectionLinearEquiv_project
#print axioms CausalTailLens.relabelPreimageFibreEquiv
#print axioms CausalTailLens.tensorRelabel_tensorFace
#print axioms orientedPairSection_eq_ecology_localCurrent
#print axioms orientedPairSection_holon_receive
end Audit

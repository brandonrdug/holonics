import ElementaryHolonics.Computation.HolonicCausalTailLens

/-!
# The complete addressed pair-current tensor face

The tensor lens in this owner is applied to the complete target/source-indexed current section
before `CausalTailLens.energy` collapses that current to a nonnegative face.  Its one tensor slot is
the entire explicit role-bearing pair section.  This is a rank-one tensor presentation of an
already-coordinate-indexed carrier, not a basis-free claim that every abstract order-two tensor is
a matrix.

The signed control exhibits the exact lost distinction: `+1` and `-1` have the same selected
magnitude and different complete tensor faces.  Both scalar and tensor preimages remain explicit.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicPairCurrentTensorFace

open scoped BigOperators TensorProduct
open Soma.Holonics.Computation.HolonicCausalTailLens

universe uR uS

variable {R : Type uR} {Site : Type uS}
variable [CommSemiring R]

/-- A rank-one tensor whose sole slot is the complete target/source pair-current section. -/
abbrev PairCurrentTensorFace :=
  TensorFace R (fun _ : Fin 1 ↦ AddressedPairSection Site R)

/-- Present a complete addressed current section without applying an energy receiver. -/
def pairCurrentTensorFace (currents : AddressedPairSection Site R) :
    PairCurrentTensorFace (R := R) (Site := Site) :=
  PiTensorProduct.tprod R (fun _ : Fin 1 ↦ currents)

/-- The singleton tensor slot recovers the complete addressed section exactly. -/
theorem subsingletonEquiv_pairCurrentTensorFace
    (currents : AddressedPairSection Site R) :
    PiTensorProduct.subsingletonEquiv (R := R)
      (s := fun _ : Fin 1 ↦ AddressedPairSection Site R) 0
      (pairCurrentTensorFace currents) = currents := by
  simp [pairCurrentTensorFace]

/-- Equal complete tensor faces imply equal role-bearing pair-current sections. -/
theorem pairCurrentTensorFace_injective :
    Function.Injective (pairCurrentTensorFace (R := R) (Site := Site)) := by
  intro left right heq
  have recovered := congrArg
    (PiTensorProduct.subsingletonEquiv (R := R)
      (s := fun _ : Fin 1 ↦ AddressedPairSection Site R) 0) heq
  rw [subsingletonEquiv_pairCurrentTensorFace,
    subsingletonEquiv_pairCurrentTensorFace] at recovered
  exact recovered

/-- The tensor receiver over complete addressed current, before energy collapse. -/
def pairCurrentTensorLens :
    TensorLens (AddressedPairSection Site R) R (Fin 1)
      (fun _ ↦ AddressedPairSection Site R) where
  project := pairCurrentTensorFace

/-- The identity pair-section holon retains the complete current as its receiver face. -/
def completePairSectionHolon :
    Holon (AddressedPairSection Site R) (AddressedPairSection Site R)
      (AddressedPairSection Site R) where
  Occurrence := AddressedPairSection Site R
  source currents := currents
  target currents := currents
  receive currents := currents

/-- Every complete pair section inhabits the literal preimage of its tensor face. -/
def pairCurrentTensorPreimageOf (currents : AddressedPairSection Site R) :
    (pairCurrentTensorLens (R := R) (Site := Site)).PreimageFibre
      completePairSectionHolon (pairCurrentTensorFace currents) :=
  ⟨currents, rfl⟩

variable {Depth : Type*} [Fintype Site] [Fintype Depth] [DecidableEq Depth]

/-- A downstream scalar receiver which sums the declared depth-energy coordinates. -/
def aggregateMagnitude (lens : CausalTailLens Site R Depth)
    (currents : AddressedPairSection Site R) : NNReal :=
  ∑ depth, lens.project currents depth

/-- The scalar magnitude holon retains every complete section behind the selected scalar face. -/
def aggregateMagnitudeHolon (lens : CausalTailLens Site R Depth) :
    Holon (AddressedPairSection Site R) NNReal NNReal where
  Occurrence := AddressedPairSection Site R
  source currents := currents
  target currents := aggregateMagnitude lens currents
  receive currents := aggregateMagnitude lens currents

namespace Control

/-- Absolute signed magnitude, used only by the finite collapse control. -/
def signedEnergy (current : ℤ) : NNReal := current.natAbs

def signedLens : CausalTailLens Unit ℤ Unit where
  depth _ _ := ()
  energy := signedEnergy
  energy_zero := by simp [signedEnergy]

def positiveSection : AddressedPairSection Unit ℤ := fun _ _ ↦ 1
def negativeSection : AddressedPairSection Unit ℤ := fun _ _ ↦ -1

/-- Opposite signed currents return the same selected magnitude. -/
theorem signedControl_sameMagnitude :
    aggregateMagnitude signedLens positiveSection =
      aggregateMagnitude signedLens negativeSection := by
  simp [aggregateMagnitude, CausalTailLens.project, signedLens, signedEnergy,
    positiveSection, negativeSection]

/-- The complete tensor receiver retains the sign erased by magnitude. -/
theorem signedControl_differentTensor :
    pairCurrentTensorFace (R := ℤ) positiveSection ≠
      pairCurrentTensorFace (R := ℤ) negativeSection := by
  intro heq
  have hsections := pairCurrentTensorFace_injective (R := ℤ) (Site := Unit) heq
  have hvalue := congrFun (congrFun hsections ()) ()
  norm_num [positiveSection, negativeSection] at hvalue

/-- The two complete tensor preimages remain distinct occurrences. -/
def positiveTensorPreimage := pairCurrentTensorPreimageOf (R := ℤ) positiveSection
def negativeTensorPreimage := pairCurrentTensorPreimageOf (R := ℤ) negativeSection

/-- Both signed sections inhabit the same scalar-magnitude preimage. -/
def positiveMagnitudePreimage :
    (aggregateMagnitudeHolon signedLens).PreimageFibre
      (aggregateMagnitude signedLens positiveSection) :=
  ⟨positiveSection, rfl⟩

def negativeMagnitudePreimage :
    (aggregateMagnitudeHolon signedLens).PreimageFibre
      (aggregateMagnitude signedLens positiveSection) :=
  ⟨negativeSection, signedControl_sameMagnitude.symm⟩

/-- No function of the selected scalar magnitude can recover every complete tensor face. -/
theorem signedControl_no_tensor_descent :
    ¬ ∃ descend : NNReal → PairCurrentTensorFace (R := ℤ) (Site := Unit),
      ∀ currents, descend (aggregateMagnitude signedLens currents) =
        pairCurrentTensorFace currents := by
  rintro ⟨descend, exact⟩
  apply signedControl_differentTensor
  calc
    pairCurrentTensorFace (R := ℤ) positiveSection =
        descend (aggregateMagnitude signedLens positiveSection) := (exact positiveSection).symm
    _ = descend (aggregateMagnitude signedLens negativeSection) :=
      congrArg descend signedControl_sameMagnitude
    _ = pairCurrentTensorFace (R := ℤ) negativeSection := exact negativeSection

end Control

end Soma.Holonics.Computation.HolonicPairCurrentTensorFace

section Audit
open Soma.Holonics.Computation.HolonicPairCurrentTensorFace
#print axioms subsingletonEquiv_pairCurrentTensorFace
#print axioms pairCurrentTensorFace_injective
#print axioms pairCurrentTensorPreimageOf
#print axioms Control.signedControl_sameMagnitude
#print axioms Control.signedControl_differentTensor
#print axioms Control.positiveTensorPreimage
#print axioms Control.negativeTensorPreimage
#print axioms Control.positiveMagnitudePreimage
#print axioms Control.negativeMagnitudePreimage
#print axioms Control.signedControl_no_tensor_descent
end Audit

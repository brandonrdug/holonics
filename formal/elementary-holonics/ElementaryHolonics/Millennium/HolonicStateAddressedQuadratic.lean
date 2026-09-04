import ElementaryHolonics.Millennium.HolonicQuadraticMomentCondensation

/-!
# State-addressed quadratic receiver fronts

This file adds the smallest missing outer index to the existing quadratic moment laws.  A state is
an explicit direct-sum block of the upper-pair carrier; it is not folded into the factor-pair
coordinates (which would introduce undeclared cross-state terms), and it is not metadata retained
only in a cold reconstruction witness.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicStateAddressedQuadratic

open scoped BigOperators
open Soma.Holonics.Millennium.HolonicQuadraticMomentCondensation

variable {Scalar State Port Generator Support Cell Rank : Type*}
  [CommRing Scalar] [Fintype State] [Fintype Port] [Fintype Generator]
  [Fintype Support] [Fintype Cell] [Fintype Rank] [DecidableEq State]

/-! ## One state/port/generator face -/

/-- One addressed quadratic face: generator transport followed by the restriction on both legs.
The state remains an outer address and therefore cannot create cross-state pair terms. -/
def stateAddressedFace
    (moment : State → Matrix Cell Cell Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (state : State) (port : Port) (generatorFace : Generator) :
    Matrix Cell Cell Scalar :=
  restrictMoment (restriction state port)
    (transportMoment (generator generatorFace) (moment state))

/-- A selected situated front, grouped by its target state.  The summation retains every selected
source-state/port/generator occurrence until the target-state block is formed. -/
def selectedStateAddressedSum
    (moment : State → Matrix Cell Cell Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (targetState : State → Port → State)
    (selected : State → Port → Generator → Prop)
    (target : State) : Matrix Cell Cell Scalar := by
  classical
  exact ∑ state, ∑ port, ∑ generatorFace,
    if selected state port generatorFace ∧ targetState state port = target
    then stateAddressedFace moment generator restriction state port generatorFace
    else 0

/-! ## Exact compatibility with the existing moment transport theorem -/

/-- The state-addressed face is exactly the restricted second moment of the generated current.
This imports the existing two-leg generator law rather than introducing a state-blind aggregate. -/
theorem stateAddressedFace_eq_restrict_generatedMoment
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (state : State) (port : Port) (generatorFace : Generator) :
    stateAddressedFace (fun _ => quadraticMoment weight current) generator restriction
        state port generatorFace =
      restrictMoment (restriction state port)
        (quadraticMoment weight
          (fun support => (generator generatorFace).mulVec (current support))) := by
  unfold stateAddressedFace
  rw [quadraticMoment_generated_eq_transportMoment]

/-- The complete state-addressed selected front equals the direct sum of the restricted generated
moments.  This is the exact state-targeted quadratic carrier law used by the runtime: no generator
branches are added before transport, no states are merged before target addressing, and no
cross-state pair is introduced. -/
theorem selectedStateAddressedSum_eq_restrictedGeneratedSum
    (weight : Support → Scalar) (current : Support → Cell → Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (targetState : State → Port → State)
    (selected : State → Port → Generator → Prop)
    (target : State) :
    selectedStateAddressedSum
        (fun _ => quadraticMoment weight current) generator restriction targetState selected target =
      ∑ state, ∑ port, ∑ generatorFace,
        if selected state port generatorFace ∧ targetState state port = target
        then restrictMoment (restriction state port)
          (quadraticMoment weight
            (fun support => (generator generatorFace).mulVec (current support)))
        else 0 := by
  classical
  unfold selectedStateAddressedSum
  apply Finset.sum_congr rfl
  intro state _
  apply Finset.sum_congr rfl
  intro port _
  apply Finset.sum_congr rfl
  intro generatorFace _
  split
  · rw [stateAddressedFace_eq_restrict_generatedMoment]
  · rfl

/-! ## Low-rank state faces remain factored after both-leg restriction -/

/-- Apply one addressed boundary current to both cell legs of an incidence frame.  This is the
 smallest executable chart for the boundary restriction: it changes the frame rows, while the
 constitutive form remains on the derived image population. -/
def restrictFrame
    (restriction : Cell → Scalar)
    (frame : Matrix Rank Cell Scalar) : Matrix Rank Cell Scalar :=
  fun rank cell => restriction cell * frame rank cell

theorem restrictMoment_lowRankMoment_eq_lowRankMoment_restrictFrame
    (restriction : Cell → Scalar)
    (frame : Matrix Rank Cell Scalar)
    (constitutive : Matrix Rank Rank Scalar) :
    restrictMoment restriction (lowRankMoment frame constitutive) =
      lowRankMoment (restrictFrame restriction frame) constitutive := by
  ext left right
  simp [restrictMoment, lowRankMoment, restrictFrame, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro rank _
  apply Finset.sum_congr rfl
  intro source _
  ring

/-- A state/port/generator addressed face is the low-rank moment of the transported incidence
 after its boundary current is applied on both tensor legs.  State and port remain addresses; they
 do not become dimensions of the constitutive carrier or introduce cross-state pairs. -/
theorem stateAddressedFace_eq_lowRankMoment_restrictedTransportedFrame
    (frame : State → Matrix Rank Cell Scalar)
    (constitutive : State → Matrix Rank Rank Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (state : State) (port : Port) (generatorFace : Generator) :
    stateAddressedFace
        (fun state => lowRankMoment (frame state) (constitutive state))
        generator restriction state port generatorFace =
      lowRankMoment
        (restrictFrame (restriction state port)
          (frame state * (generator generatorFace).transpose))
        (constitutive state) := by
  unfold stateAddressedFace
  rw [transportMoment_lowRankMoment]
  exact restrictMoment_lowRankMoment_eq_lowRankMoment_restrictFrame
    (restriction state port)
    (frame state * (generator generatorFace).transpose)
    (constitutive state)

/-- The selected target-state front is a direct sum of these independently transported and
 restricted low-rank faces.  The target-state address is applied before the direct sum, so no
 cross-state constitutive term is manufactured by the condensation. -/
theorem selectedStateAddressedSum_eq_restrictedTransportedLowRankSum
    (frame : State → Matrix Rank Cell Scalar)
    (constitutive : State → Matrix Rank Rank Scalar)
    (generator : Generator → Matrix Cell Cell Scalar)
    (restriction : State → Port → Cell → Scalar)
    (targetState : State → Port → State)
    (selected : State → Port → Generator → Prop)
    (target : State) :
    selectedStateAddressedSum
        (fun state => lowRankMoment (frame state) (constitutive state))
        generator restriction targetState selected target =
      ∑ state, ∑ port, ∑ generatorFace,
        if selected state port generatorFace ∧ targetState state port = target
        then lowRankMoment
          (restrictFrame (restriction state port)
            (frame state * (generator generatorFace).transpose))
          (constitutive state)
        else 0 := by
  classical
  unfold selectedStateAddressedSum
  apply Finset.sum_congr rfl
  intro state _
  apply Finset.sum_congr rfl
  intro port _
  apply Finset.sum_congr rfl
  intro generatorFace _
  split
  · rw [stateAddressedFace_eq_lowRankMoment_restrictedTransportedFrame]
  · rfl

end Soma.Holonics.Millennium.HolonicStateAddressedQuadratic

#print axioms Soma.Holonics.Millennium.HolonicStateAddressedQuadratic.stateAddressedFace_eq_restrict_generatedMoment
#print axioms Soma.Holonics.Millennium.HolonicStateAddressedQuadratic.selectedStateAddressedSum_eq_restrictedGeneratedSum
#print axioms Soma.Holonics.Millennium.HolonicStateAddressedQuadratic.restrictMoment_lowRankMoment_eq_lowRankMoment_restrictFrame
#print axioms Soma.Holonics.Millennium.HolonicStateAddressedQuadratic.stateAddressedFace_eq_lowRankMoment_restrictedTransportedFrame
#print axioms Soma.Holonics.Millennium.HolonicStateAddressedQuadratic.selectedStateAddressedSum_eq_restrictedTransportedLowRankSum

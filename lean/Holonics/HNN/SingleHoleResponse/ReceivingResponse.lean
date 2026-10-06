import Holonics.HNN.SingleHoleResponse.LoadedWord

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

section ReceivingResponse

open Holonics.HNN.LoadedMedium
open Holonics.HNN.TickFamily
open Holonics.HNN.Propagation

variable {Ring Contact : Type*} [Fintype Ring] [Fintype Contact]
  [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type*} [∀ r, NormedAddCommGroup (V r)]
  [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type*} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]
variable {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop}


/-- The receiver reads the fixed-plus-same-label response after the tick-indexed loaded physical
word. The only caller bridge is `hopen`, which relates the native source opening to the constructive
first/offset expansion above. -/
theorem loadedReceiving_response
    {Label Y : Type*} [Fintype Label] [DecidableEq Label]
    [AddCommGroup Y] [Module ℝ Y]
    (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g))
    (h : ℝ) (openedAt t : ℕ)
    (openedState : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (anchor : LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (response : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hopen : ∀ c, openedState c = anchor + response c)
    (receiver : LoadedState (endRing := endRing) (V := V) (Ch := Ch) →ₗ[ℝ] Y) :
    ∀ c, receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) (openedState c) t) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) anchor t) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt) (response c) t) := by
  intro c
  rw [hopen c, absoluteLoaded_response_add]
  exact map_add receiver _ _


end ReceivingResponse

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.loadedReceiving_response

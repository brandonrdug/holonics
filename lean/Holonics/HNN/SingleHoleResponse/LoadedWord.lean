import Holonics.HNN.LoadedMedium
import Holonics.HNN.TickFamily

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

section LoadedConsumer

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

abbrev LoadedState := (b : Ring ⊕ Contact) → LoadedM endRing V Ch b

/-- Source responses change ring storage only. Their arriving waves, contact displacement/rate and
resonator positions/rates are zero; the fixed entered state supplies all such interior operands. -/
def SourceResponseShape (x : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) : Prop :=
  (∀ g, (x (.inl g)).1.2 = 0 ∧ (x (.inl g)).2 = (0, 0)) ∧
    ∀ a, (x (.inr a)).1 = 0

/-- The actual loaded full-block operator at the word's absolute opened tick. Each step therefore
uses the resonator pump phase at `openedAt + t`, as owned by `LoadedMedium.loadedOp`. -/
def absoluteLoadedFamily (T : BlockOp ℝ (BlockM endRing V Ch))
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (openedAt : ℕ) :
    ℕ → BlockOp ℝ (LoadedM endRing V Ch) :=
  fun t => loadedOp T res h (openedAt + t)

private theorem tick_add_loaded (T : BlockOp ℝ (LoadedM endRing V Ch))
    (x y : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) :
    tick T (x + y) = tick T x + tick T y := by
  funext b
  simp only [tick, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- A tick-indexed block word is additive in its full opening state. -/
theorem trajectoryAt_add_loaded (T : ℕ → BlockOp ℝ (LoadedM endRing V Ch))
    (x y : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) (t : ℕ) :
    trajectoryAt T (x + y) t = trajectoryAt T x t + trajectoryAt T y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [trajectoryAt, ih]
      exact tick_add_loaded (T t) _ _

/-- The loaded response identity at its concrete owner: `loadedOp` is evaluated at each actual
absolute tick `openedAt + k`, over storage, arrivals, contact states and resonator `(u,w)` alike. -/
theorem absoluteLoaded_response_add (T : BlockOp ℝ (BlockM endRing V Ch))
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (openedAt t : ℕ)
    (anchor response : LoadedState (endRing := endRing) (V := V) (Ch := Ch)) :
    trajectoryAt (absoluteLoadedFamily T res h openedAt) (anchor + response) t =
      trajectoryAt (absoluteLoadedFamily T res h openedAt) anchor t +
        trajectoryAt (absoluteLoadedFamily T res h openedAt) response t :=
  trajectoryAt_add_loaded (absoluteLoadedFamily T res h openedAt) anchor response t

end LoadedConsumer

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.absoluteLoaded_response_add

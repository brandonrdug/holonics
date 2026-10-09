import Holonics.HNN.SingleHoleResponse.SourceExpansion
import Holonics.HNN.SingleHoleResponse.LoadedWord
import Holonics.HNN.SingleHoleResponse.NormalizedOpening
import Holonics.HNN.SingleHoleResponse.ReceivingResponse
import Holonics.HNN.SingleHoleResponse.GrainRelease

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

section EndToEnd

open Holonics.HNN.LoadedMedium
open Holonics.HNN.TickFamily
open Holonics.HNN.Propagation
open Holonics.HNN.TickBlocks

universe u

variable {Ring Contact : Type u} [Fintype Ring] [Fintype Contact]
  [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)]
  [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]

abbrev EndToEndLoadedState := (b : Ring ⊕ Contact) → LoadedM endRing V Ch b

/-- The fixed, fully normalized source after the retained interior has been entered. -/
def normalizedSourceAnchor
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (entered : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (inject : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch)) :=
  entered + inject (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
    (fun e => ν (Fintype.card Station - offset e)))

/-- The common-label source response injected at a selected missing station. -/
def normalizedSourceResponse
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (offset : Station × Station → ℕ) (ν : ℕ → K) (c : Label)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (inject : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch)) :=
  inject (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
    (fun e => ν (Fintype.card Station - offset e)))

/-- End-to-end theorem for the accepted exact one-hole domain. It derives the anchor and shared
label response from the normalized source expansion and the retained full-state opening, advances
both through `LoadedMedium.loadedOp` at `openedAt + k`, reads the linear receiver, transports the
result through an explicit GrainCell face map, and releases a singleton exact leader union at zero
tolerance. `score ∘ grainCell` is supplied by the receiver chart; it is never identified with raw
coordinates of the linear receiver. -/
theorem normalizedSource_loadedWord_grain_singleton_release
    {K Station Label X W Y Grain Class : Type*} [Field K]
    [Fintype Station] [DecidableEq Station] [Fintype Label] [DecidableEq Label]
    [Fintype Class] [DecidableEq Class] [AddCommGroup X] [Module K X]
    [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (N : ℕ) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (hedges : ∀ e ∈ edges, e.1 ≠ e.2)
    (sourceInjection : W →ₗ[ℝ] EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (enteredInterior : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (openComplete : Label → EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hresponseShape : ∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))))
    (hopen : ∀ c, openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e))))
    (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g))
    (h : ℝ) (openedAt ticks : ℕ)
    (receiver : EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch) →ₗ[ℝ] Y)
    (grainCell : Y → Grain) (score : Grain → Class → ℚ)
    (reading : Label → Class → ℚ)
    (hreading : reading = fun c j => score (grainCell (receiver (trajectoryAt
      (absoluteLoadedFamily T res h openedAt)
      (normalizedSourceAnchor edges hole known basis offset ν P F Q enteredInterior sourceInjection +
        normalizedSourceResponse edges hole known basis offset ν c P F Q sourceInjection) ticks))) j)
    (greatest : Label → ℚ) (compatible : Finset Label) (hcompatible : compatible.Nonempty)
    (winner : Class)
    (hunion : exactLeaderUnion reading greatest compatible = {winner})
    (hmaximum : ∀ c ∈ compatible,
      (∀ j, reading c j ≤ greatest c) ∧ ∃ j, reading c j = greatest c)
    (emit : Label → Class)
    (hemits : ∀ c ∈ compatible, emit c ∈ exactLeaders (reading c) (greatest c))
    (classReading : Class → ℚ) :
    (∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c
        (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e))))) ∧
    (∀ c, receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (enteredInterior + sourceInjection
          (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (sourceInjection (responseSource edges hole known basis c
            (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks)) ∧
    (∀ c, grainCell (receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks)) =
      grainCell (receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (enteredInterior + sourceInjection
          (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks) +
        receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
          (sourceInjection (responseSource edges hole known basis c
            (ν (Fintype.card Station)) P F Q
            (fun e => ν (Fintype.card Station - offset e)))) ticks))) ∧
    (Holonics.Foundation.ReceiverRelease.holdingLaw Label Unit Unit 0).decide
      compatible hcompatible (fun c => classReading (emit c)) =
        Holonics.Foundation.ReceiverRelease.ReleaseReturn.released := by
  have hopened := openedState_from_normalized_source edges hole known basis N offset ν hN P F Q
    hedges sourceInjection enteredInterior openComplete hresponseShape hopen
  let anchor := enteredInterior + sourceInjection
    (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
      (fun e => ν (Fintype.card Station - offset e)))
  let response : Label → EndToEndLoadedState (endRing := endRing) (V := V) (Ch := Ch) :=
    fun c => sourceInjection (responseSource edges hole known basis c
      (ν (Fintype.card Station)) P F Q (fun e => ν (Fintype.card Station - offset e)))
  have hread := loadedReceiving_response T res h openedAt ticks openComplete anchor response
    hopened.1 receiver
  have hcomputed (c : Label) :
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (openComplete c) ticks) =
      receiver (trajectoryAt (absoluteLoadedFamily T res h openedAt)
        (anchor + response c) ticks) := by
    exact congrArg (fun z => receiver (trajectoryAt
      (absoluteLoadedFamily T res h openedAt) z ticks)) (hopened.1 c)
  have hfaceAdd (c : Label) := congrArg grainCell (hread c)
  -- Share the actual completed receiver/score term once. This proof-only expression sharing
  -- preserves the source/clock/grain operands and consumes their existing accepted owners.
  let fullValue (c : Label) := receiver (trajectoryAt
    (absoluteLoadedFamily T res h openedAt) (openComplete c) ticks)
  let fullReading (c : Label) (j : Class) := score (grainCell (fullValue c)) j
  have hreadingFull : fullReading = reading := by
    rw [hreading]
    funext c j
    dsimp [fullReading, fullValue]
    exact congrArg (fun z => score (grainCell z) j) (hcomputed c)
  have hunionFull : exactLeaderUnion fullReading greatest compatible = {winner} := by
    rw [hreadingFull]
    exact hunion
  have hmaximumFull : ∀ c ∈ compatible,
      (∀ j, fullReading c j ≤ greatest c) ∧
      ∃ j, fullReading c j = greatest c := by
    rw [hreadingFull]
    exact hmaximum
  have hemitsFull : ∀ c ∈ compatible,
      emit c ∈ exactLeaders (fullReading c) (greatest c) := by
    rw [hreadingFull]
    exact hemits
  have hsound := exactLeaderUnion_sound fullReading greatest compatible hmaximumFull
  have hfromSound (c : Label) (hc : c ∈ compatible) :
      emit c ∈ exactLeaderUnion fullReading greatest compatible := by
    apply (hsound (emit c)).2
    refine ⟨c, hc, (hmaximumFull c hc).1, ?_⟩
    exact (Finset.mem_filter.mp (hemitsFull c hc)).2
  have hconstant : ∀ c ∈ compatible, ∀ d ∈ compatible,
      classReading (emit c) = classReading (emit d) := by
    intro c hc d hd
    have hcWinner : emit c = winner := by
      have hx := hfromSound c hc
      rw [hunionFull] at hx
      simpa using hx
    have hdWinner : emit d = winner := by
      have hy := hfromSound d hd
      rw [hunionFull] at hy
      simpa using hy
    rw [hcWinner, hdWinner]
  refine ⟨hopened.2, ?_, ?_, ?_⟩
  · intro c
    exact hread c
  · intro c
    exact hfaceAdd c
  · exact holdingLaw_releases_constant_face_at_zero compatible hcompatible
      (fun c => classReading (emit c)) hconstant

end EndToEnd

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.normalizedSource_loadedWord_grain_singleton_release

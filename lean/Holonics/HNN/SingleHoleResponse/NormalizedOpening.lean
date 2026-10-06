import Holonics.HNN.SingleHoleResponse.SourceExpansion
import Holonics.HNN.SingleHoleResponse.LoadedWord

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

section NormalizedOpening

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
variable {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop}


/-- Full-state normalized source-opening bridge. `N` is certified as the station population;
each response is injected into storage only, with zero arrivals, contacts and resonator state. -/
theorem openedState_from_normalized_source
    {K Station Label X W : Type*} [Field K] [Fintype Station] [DecidableEq Station]
    [Fintype Label] [DecidableEq Label] [AddCommGroup X] [Module K X]
    [AddCommGroup W] [Module K W] [Module ℝ W]
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (N : ℕ) (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2)
    (sourceInjection : W →ₗ[ℝ] LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (enteredInterior : LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (openComplete : Label → LoadedState (endRing := endRing) (V := V) (Ch := Ch))
    (hresponseShape : ∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))))
    (hopen : ∀ c, openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν N) P F Q
        (fun e => ν (N - offset e)))) :
    (∀ c, openComplete c =
      (enteredInterior + sourceInjection
        (fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)))) +
      sourceInjection (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)))) ∧
    (∀ c, SourceResponseShape
      (sourceInjection (responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)))) := by
  have hsplit (c : Label) := populationNormalizedOneHoleSourceExpansion edges hole known basis c
    (Fintype.card Station) offset ν rfl P F Q hedges
  have hopen' (c : Label) : openComplete c = enteredInterior +
      sourceInjection (completeSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e))) := by
    simpa [hN] using hopen c
  constructor
  · intro c
    rw [hopen' c, hsplit c]
    simp only [map_add, add_assoc]
  · intro c
    simpa [hN] using hresponseShape c

end NormalizedOpening

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.openedState_from_normalized_source

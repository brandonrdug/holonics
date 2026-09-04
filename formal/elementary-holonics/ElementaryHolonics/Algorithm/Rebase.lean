import ElementaryHolonics.Algorithm.Transition
import Mathlib.Logic.Equiv.Defs

/-!
# Invertible rebase

An invertible state chart conjugates transitions and transports every boundary
face.  A noninvertible map is deliberately not called a rebase here.
-/

namespace Soma.Holonics

namespace SituatedAlgorithm

def rebase {Θ I S O S' : Type*}
    (A : SituatedAlgorithm Θ I S O) (e : S ≃ S') :
    SituatedAlgorithm Θ I S' O where
  init θ i s' := A.init θ i (e.symm s')
  step θ s' t' := A.step θ (e.symm s') (e.symm t')
  done θ s' := A.done θ (e.symm s')
  observe θ s' o := A.observe θ (e.symm s') o

theorem trace_rebase_iff {Θ I S O S' : Type*}
    (A : SituatedAlgorithm Θ I S O) (e : S ≃ S')
    (θ : Θ) (s t : S) :
    Trace ((A.rebase e).step θ) (e s) (e t) ↔
      Trace (A.step θ) s t := by
  constructor
  · intro h
    have mapped :=
      h.map e.symm (fun {_ _} hstep ↦ by
        simpa [rebase] using hstep)
    simpa using mapped
  · intro h
    exact h.map e (fun {_ _} hstep ↦ by
      simpa [rebase] using hstep)

theorem semantics_rebase_iff {Θ I S O S' : Type*}
    (A : SituatedAlgorithm Θ I S O) (e : S ≃ S')
    (θ : Θ) (input : I) (output : O) :
    (A.rebase e).Semantics θ input output ↔
      A.Semantics θ input output := by
  constructor
  · rintro ⟨s₀, sₙ, hinit, htrace, hdone, hobserve⟩
    refine ⟨e.symm s₀, e.symm sₙ, hinit, ?_, hdone, hobserve⟩
    have mapped :=
      htrace.map e.symm (fun {_ _} hstep ↦ by
        simpa [rebase] using hstep)
    exact mapped
  · rintro ⟨s₀, sₙ, hinit, htrace, hdone, hobserve⟩
    refine ⟨e s₀, e sₙ, ?_, ?_, ?_, ?_⟩
    · simpa [rebase] using hinit
    · exact (trace_rebase_iff A e θ s₀ sₙ).2 htrace
    · simpa [rebase] using hdone
    · simpa [rebase] using hobserve

end SituatedAlgorithm

end Soma.Holonics

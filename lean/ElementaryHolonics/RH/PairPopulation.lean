import ElementaryHolonics.RH.XiConjugation
import ElementaryHolonics.RH.WeilPositivity

/-!
# The pair population

The reflection `s ↦ 1 − s̄` across the critical line carries zeros of `ξ` to zeros of `ξ`
(`ξ(1 − s) = ξ(s)` and `ξ(s̄) = ξ(s)̄`), and its fixed locus is the line `Re s = ½`.  The pair
population is the set of zeros not fixed by it: on it the reflection is a fixed-point-free
involution, so its members come in pairs `{ρ, 1 − ρ̄}` straddling the line.  The Riemann
hypothesis empties the pair population, and an empty pair population puts every zero of `ξ` on
the line.  This is the corpus's reading of `½` as the exponent at which a thing meets its own
conjugate, made a definition.
-/

open Complex
open scoped ComplexConjugate
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiConjugation
open Soma.Holonics.RH.WeilPositivity

namespace Soma.Holonics.RH.PairPopulation

/-- The reflection across the critical line. -/
def reflect (s : ℂ) : ℂ := 1 - conj s

theorem reflect_reflect (s : ℂ) : reflect (reflect s) = s := by
  simp [reflect]

theorem reflect_eq_self_iff (s : ℂ) : reflect s = s ↔ s.re = 1 / 2 :=
  criticalLine_fixedLocus s

theorem riemannXi_reflect (s : ℂ) : riemannXi (reflect s) = conj (riemannXi s) := by
  rw [reflect, riemannXi_one_sub, riemannXi_conj]

theorem riemannXi_reflect_eq_zero_iff (s : ℂ) : riemannXi (reflect s) = 0 ↔ riemannXi s = 0 := by
  rw [riemannXi_reflect]
  exact map_eq_zero (starRingEnd ℂ)

/-- The zero set of `ξ`. -/
def zeroSet : Set ℂ := {ρ | riemannXi ρ = 0}

theorem reflect_mem_zeroSet {ρ : ℂ} (h : ρ ∈ zeroSet) : reflect ρ ∈ zeroSet :=
  (riemannXi_reflect_eq_zero_iff ρ).mpr h

/-- **The pair population**: the zeros of `ξ` not fixed by the reflection. -/
def pairPopulation : Set ℂ := {ρ | riemannXi ρ = 0 ∧ reflect ρ ≠ ρ}

theorem reflect_mem_pairPopulation {ρ : ℂ} (h : ρ ∈ pairPopulation) :
    reflect ρ ∈ pairPopulation := by
  refine ⟨reflect_mem_zeroSet h.1, ?_⟩
  intro heq
  apply h.2
  have := congrArg reflect heq
  rw [reflect_reflect, reflect_reflect] at this
  exact this

/-- On the pair population the reflection has no fixed point: its members come in pairs. -/
theorem reflect_ne_self_of_mem {ρ : ℂ} (h : ρ ∈ pairPopulation) : reflect ρ ≠ ρ := h.2

theorem re_ne_half_of_mem {ρ : ℂ} (h : ρ ∈ pairPopulation) : ρ.re ≠ 1 / 2 := by
  intro hre
  exact h.2 ((reflect_eq_self_iff ρ).mpr hre)

/-- **The Riemann hypothesis empties the pair population.** -/
theorem pairPopulation_eq_empty_of_RH (hRH : RiemannHypothesis) : pairPopulation = ∅ := by
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨h0, hne⟩
  apply hne
  rw [reflect_eq_self_iff]
  exact riemannXi_zero_re_of_RH hRH h0

/-- **An empty pair population puts every zero of `ξ` on the critical line.** -/
theorem re_eq_half_of_pairPopulation_eq_empty (h : pairPopulation = ∅) {ρ : ℂ}
    (hρ : riemannXi ρ = 0) : ρ.re = 1 / 2 := by
  rw [← reflect_eq_self_iff]
  by_contra hne
  have hmem : ρ ∈ pairPopulation := ⟨hρ, hne⟩
  rw [h] at hmem
  exact hmem

/-- The pair population is empty exactly when every zero of `ξ` lies on the critical line. -/
theorem pairPopulation_eq_empty_iff :
    pairPopulation = ∅ ↔ ∀ ρ : ℂ, riemannXi ρ = 0 → ρ.re = 1 / 2 := by
  constructor
  · intro h ρ hρ
    exact re_eq_half_of_pairPopulation_eq_empty h hρ
  · intro h
    ext ρ
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨h0, hne⟩
    exact hne ((reflect_eq_self_iff ρ).mpr (h ρ h0))

end Soma.Holonics.RH.PairPopulation

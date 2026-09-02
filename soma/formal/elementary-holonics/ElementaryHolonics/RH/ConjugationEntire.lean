import ElementaryHolonics.RH.ZeroDynamicsEntire
import ElementaryHolonics.RH.PairPopulation

/-!
# Conjugation symmetry of `H_t` and the pair population of the flow

`conj ∘ g ∘ conj` has derivative `conj g′`, so iterated derivatives commute with the conjugation
symmetry `f (conj z) = conj (f z)`, and the flow inherits it: `H_t (conj z) = conj (H_t z)`.
With reflection this gives `H_t (reflect ρ) = conj (H_t ρ)` for `reflect ρ = 1 − conj ρ`, so
the pair population of `H_t`, the zeros not fixed by `reflect`, is closed under conjugation,
`s ↦ 1 − s`, and `reflect`.  At `t = 0` it is the pair population of `Ξ`.
-/

open Complex Metric Filter Topology Set
open scoped ComplexConjugate
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiConjugation
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.HeatEquationEntire
open Soma.Holonics.RH.PairPopulation

namespace Soma.Holonics.RH.ConjugationEntire

/-- `conj ∘ g ∘ conj` has derivative `conj g′`. -/
theorem hasDerivAt_conj_conj {g : ℂ → ℂ} {g' z : ℂ} (hg : HasDerivAt g g' (conj z)) :
    HasDerivAt (fun w => conj (g (conj w))) (conj g') z := by
  have h1 : HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) z := conjCLE.hasFDerivAt
  have h2 : HasFDerivAt g
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) g').restrictScalars ℝ) (conj z) :=
    (hasDerivAt_iff_hasFDerivAt.mp hg).restrictScalars ℝ
  have h3 : HasFDerivAt (fun w : ℂ => conj w) (conjCLE : ℂ →L[ℝ] ℂ) (g (conj z)) :=
    conjCLE.hasFDerivAt
  have h4 := h3.comp z (h2.comp z h1)
  rw [hasDerivAt_iff_hasFDerivAt]
  refine hasFDerivAt_of_restrictScalars ℝ h4 ?_
  ext w
  simp [ContinuousLinearMap.smulRight_apply, conjCLE_apply, mul_comm]

theorem iteratedDeriv_conj_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n (fun w => conj (f (conj w))) = fun w => conj (iteratedDeriv n f (conj w)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    rw [iteratedDeriv_succ]
    exact (hasDerivAt_conj_conj ((differentiable_iteratedDeriv hf n) (conj w)).hasDerivAt).deriv

/-- Conjugation symmetry passes through the flow. -/
theorem heatE_conj {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hsym : ∀ s, f (conj s) = conj (f s))
    (t : ℝ) (z : ℂ) : heatE t f (conj z) = conj (heatE t f z) := by
  have hfun : (fun w => conj (f (conj w))) = f := by
    funext w
    rw [hsym, conj_conj]
  unfold heatE
  rw [conj_tsum]
  congr 1
  funext k
  unfold heatTerm
  have h1 := congrFun (iteratedDeriv_conj_conj hf (2 * k)) z
  rw [hfun] at h1
  have h2 : iteratedDeriv (2 * k) f (conj z) = conj (iteratedDeriv (2 * k) f z) := by
    rw [h1, conj_conj]
  rw [h2, map_mul]
  congr 1
  simp

/-- At `t = 0` the flow is the identity. -/
theorem heatE_zero (f : ℂ → ℂ) (z : ℂ) : heatE 0 f z = f z := by
  unfold heatE
  rw [tsum_eq_single 0]
  · exact heatTerm_zero 0 f z
  · intro k hk
    unfold heatTerm
    simp [zero_pow hk]

theorem heatE_riemannXi_conj (t : ℝ) (z : ℂ) :
    heatE t riemannXi (conj z) = conj (heatE t riemannXi z) :=
  heatE_conj differentiable_riemannXi riemannXi_conj t z

theorem heatE_riemannXi_reflect (t : ℝ) (s : ℂ) :
    heatE t riemannXi (reflect s) = conj (heatE t riemannXi s) := by
  rw [reflect, heatE_riemannXi_one_sub, heatE_riemannXi_conj]

/-- The pair population of `H_t`: zeros of `H_t` not fixed by `reflect`. -/
def pairPopulationH (t : ℝ) : Set ℂ := {ρ | heatE t riemannXi ρ = 0 ∧ reflect ρ ≠ ρ}

theorem pairPopulationH_zero : pairPopulationH 0 = pairPopulation := by
  ext ρ
  simp only [pairPopulationH, pairPopulation, Set.mem_ofPred_eq, heatE_zero]

theorem reflect_mem_pairPopulationH {t : ℝ} {ρ : ℂ} (h : ρ ∈ pairPopulationH t) :
    reflect ρ ∈ pairPopulationH t := by
  obtain ⟨h0, hne⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heatE_riemannXi_reflect, h0, map_zero]
  · rw [reflect_reflect]
    exact fun h => hne h.symm

theorem conj_mem_pairPopulationH {t : ℝ} {ρ : ℂ} (h : ρ ∈ pairPopulationH t) :
    conj ρ ∈ pairPopulationH t := by
  obtain ⟨h0, hne⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heatE_riemannXi_conj, h0, map_zero]
  · rw [Ne, reflect_eq_self_iff, conj_re]
    rw [Ne, reflect_eq_self_iff] at hne
    exact hne

theorem one_sub_mem_pairPopulationH {t : ℝ} {ρ : ℂ} (h : ρ ∈ pairPopulationH t) :
    1 - ρ ∈ pairPopulationH t := by
  obtain ⟨h0, hne⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heatE_riemannXi_one_sub, h0]
  · rw [Ne, reflect_eq_self_iff, sub_re, one_re]
    rw [Ne, reflect_eq_self_iff] at hne
    intro h
    apply hne
    linarith

end Soma.Holonics.RH.ConjugationEntire

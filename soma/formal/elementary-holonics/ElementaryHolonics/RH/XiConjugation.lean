import ElementaryHolonics.RH.ZeroComb
import ElementaryHolonics.RH.Balance

/-!
# Conjugation symmetry of the xi function and the four-member zero orbit

`ξ(s̄) = conj ξ(s)`: away from `0`, `1` and the trivial zeros of `Γ_ℝ` this is the conjugation
symmetry of `Γ_ℝ` and of `ζ` through the classical product, and the remaining points are carried
across by the reflection `ξ(1 − s) = ξ(s)`.  Hence the zero set of `ξ` is closed under both
involutions: with `ρ` the points `1 − ρ`, `ρ̄`, `1 − ρ̄` are zeros, and off the line and off the
real axis the four are distinct.  The orbit of `Balance.lean` is now an orbit of actual zeros.
-/

noncomputable section

namespace Soma.Holonics.RH.XiConjugation

open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.Balance
open Complex
open scoped ComplexConjugate

/-- **`Γ_ℝ` commutes with conjugation.** -/
theorem Gammaℝ_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul]
  congr 1
  · have hπ : ((Real.pi : ℂ)).arg ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg Real.pi_pos.le]
      exact Real.pi_ne_zero.symm
    have hexp : -conj s / 2 = conj (-s / 2) := by
      rw [map_div₀, map_neg, map_ofNat]
    rw [hexp, cpow_conj _ _ hπ, conj_ofReal]
  · have hhalf : conj s / 2 = conj (s / 2) := by
      rw [map_div₀, map_ofNat]
    rw [hhalf, Gamma_conj]

/-- Conjugation symmetry of `ξ` away from `0`, `1`, and the zeros of `Γ_ℝ`. -/
theorem riemannXi_conj_of_Gammaℝ_ne_zero {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hG : Gammaℝ s ≠ 0) : riemannXi (conj s) = conj (riemannXi s) := by
  have hc0 : conj s ≠ 0 := by
    intro h
    apply hs0
    simpa using congrArg conj h
  have hc1 : conj s ≠ 1 := by
    intro h
    apply hs1
    simpa using congrArg conj h
  have hGc : Gammaℝ (conj s) ≠ 0 := by
    rw [Gammaℝ_conj]
    exact (map_ne_zero _).mpr hG
  have hΛ : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [riemannZeta_def_of_ne_zero hs0]
    field_simp [hG]
  have hΛc : completedRiemannZeta (conj s) = Gammaℝ (conj s) * riemannZeta (conj s) := by
    rw [riemannZeta_def_of_ne_zero hc0]
    field_simp [hGc]
  rw [riemannXi_eq_classicalProduct hc0 hc1, riemannXi_eq_classicalProduct hs0 hs1, hΛc, hΛ,
    Gammaℝ_conj, riemannZeta_conj]
  simp only [map_mul, map_sub, map_one, map_div₀, map_ofNat]

/-- **`ξ` commutes with conjugation.** -/
theorem riemannXi_conj (s : ℂ) : riemannXi (conj s) = conj (riemannXi s) := by
  by_cases hs0 : s = 0
  · subst hs0
    rw [map_zero, riemannXi_zero_and_one.1, map_div₀, map_one, map_ofNat]
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one, riemannXi_zero_and_one.2, map_div₀, map_one, map_ofNat]
  by_cases hG : Gammaℝ s = 0
  · have hG' : Gammaℝ (1 - s) ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hG
      obtain ⟨m, hm⟩ := Gammaℝ_eq_zero_iff.mp h
      rw [hn] at hm
      have h2 := congrArg Complex.re hm
      simp at h2
      linarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) m]
    have h0' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h1' : (1 - s) ≠ 1 := fun h ↦ hs0 (sub_eq_self.mp h)
    have key := riemannXi_conj_of_Gammaℝ_ne_zero h0' h1' hG'
    rw [map_sub, map_one, riemannXi_one_sub, riemannXi_one_sub] at key
    exact key
  · exact riemannXi_conj_of_Gammaℝ_ne_zero hs0 hs1 hG

/-- The zero set of `ξ` is conjugation symmetric. -/
theorem riemannXi_conj_eq_zero_iff (s : ℂ) : riemannXi (conj s) = 0 ↔ riemannXi s = 0 := by
  rw [riemannXi_conj, map_eq_zero]

/-- **The zero orbit**: with `ρ`, the points `1 − ρ`, `ρ̄`, `1 − ρ̄` are zeros of `ξ`. -/
theorem zeroOrbit {ρ : ℂ} (h : riemannXi ρ = 0) :
    riemannXi (1 - ρ) = 0 ∧ riemannXi (conj ρ) = 0 ∧ riemannXi (1 - conj ρ) = 0 := by
  refine ⟨by rw [riemannXi_one_sub]; exact h, (riemannXi_conj_eq_zero_iff ρ).mpr h, ?_⟩
  rw [riemannXi_one_sub]
  exact (riemannXi_conj_eq_zero_iff ρ).mpr h

/-- **Off the line and off the real axis the orbit has four distinct members.** -/
theorem orbitDistinct {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ρ ≠ 1 - ρ ∧ ρ ≠ conj ρ ∧ ρ ≠ 1 - conj ρ ∧ (1 - ρ) ≠ conj ρ ∧
      (1 - ρ) ≠ 1 - conj ρ ∧ conj ρ ≠ 1 - conj ρ := by
  obtain ⟨h1, h2, h3⟩ := theOrbitIsFourOffTheLine hre him
  refine ⟨h1, h2, ?_, h3, ?_, ?_⟩
  · intro hc
    apply hre
    have := congrArg Complex.re hc
    simp at this
    linarith
  · intro hc
    apply him
    have := congrArg Complex.im hc
    simp at this
    linarith
  · intro hc
    apply hre
    have := congrArg Complex.re hc
    simp at this
    linarith

section Audit

#print axioms Gammaℝ_conj
#print axioms riemannXi_conj
#print axioms zeroOrbit
#print axioms orbitDistinct

end Audit

end Soma.Holonics.RH.XiConjugation

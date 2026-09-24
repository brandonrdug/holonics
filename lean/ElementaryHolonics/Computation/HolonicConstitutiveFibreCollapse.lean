import ElementaryHolonics.Computation.HolonicConstitutiveFibre
import Mathlib.Tactic

/-! A bounded collapse theorem for a rational finite return fibre. -/

namespace Soma.Holonics.Computation.HolonicConstitutiveFibreCollapse

open Soma.Holonics
open HolonicConstitutiveFibre

def verticalBasis {n : ℕ} (zero i : Fin n) : Fin n → ℚ :=
  Pi.single i 1 - Pi.single zero 1

def returnMass {n : ℕ} : (Fin n → ℚ) →ₗ[ℚ] ℚ :=
  { toFun := fun y => ∑ i, y i
    map_add' := by intro y z; simp [Finset.sum_add_distrib]
    map_smul' := by intro a y; simp [Finset.mul_sum] }

theorem verticalBasis_mem_kernel {n : ℕ} (zero : Fin n) (i : Fin n) :
    verticalBasis zero i ∈ LinearMap.ker (returnMass (n := n)) := by
  rw [LinearMap.mem_ker]
  simp [verticalBasis, returnMass, Finset.sum_sub_distrib]

theorem zero_sum_mem_span_verticalBasis {n : ℕ} (hn : 0 < n) (y : Fin n → ℚ)
    (hy : returnMass y = 0) :
    y ∈ Submodule.span ℚ (Set.range (verticalBasis (n := n) ⟨0, hn⟩)) := by
  let zero : Fin n := ⟨0, hn⟩
  have hdecomp : y = ∑ i, y i • verticalBasis zero i := by
    ext k
    classical
    simp only [verticalBasis]
    have hfirst : (∑ i, y i * (if k = i then 1 else 0)) = y k := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro b hb hbk
        rw [if_neg (Ne.symm hbk)]
        simp
      · simp
    have hsecond : (∑ i, y i * (if k = zero then 1 else 0)) =
        (if k = zero then returnMass y else 0) := by
      by_cases hk : k = zero <;> simp [hk, returnMass]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
      Pi.single_apply]
    have hsplit : (∑ i, y i * ((if k = i then 1 else 0) -
        (if k = zero then 1 else 0))) =
        (∑ i, y i * (if k = i then 1 else 0)) -
          (∑ i, y i * (if k = zero then 1 else 0)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsplit, hfirst, hsecond]
    simp [hy]
  rw [hdecomp]
  refine (Submodule.span ℚ (Set.range (verticalBasis (n := n) zero))).sum_mem (fun i hi => ?_)
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨i, rfl⟩

theorem vertical_span_eq_mass_kernel {n : ℕ} (hn : 0 < n) :
    Submodule.span ℚ (Set.range (verticalBasis (n := n) ⟨0, hn⟩)) =
      LinearMap.ker (returnMass (n := n)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact verticalBasis_mem_kernel ⟨0, hn⟩ i
  · intro y hy
    exact zero_sum_mem_span_verticalBasis hn y hy

theorem fibre_collapse
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n : ℕ} (hn : 0 < n) (R : Submodule ℚ (V × (Fin n → ℚ)))
    (vertical : ∀ i, (0, verticalBasis (n := n) ⟨0, hn⟩ i) ∈ R)
    (mass : V →ₗ[ℚ] ℚ)
    (conservation : ∀ {x : V} {y : Fin n → ℚ}, (x, y) ∈ R →
      returnMass y = mass x)
    {x : V} {y₀ : Fin n → ℚ} (base : (x, y₀) ∈ R) :
    {y : Fin n → ℚ | (x, y) ∈ R} =
      {y : Fin n → ℚ | returnMass y = mass x} := by
  ext y
  constructor
  · intro hy
    exact conservation hy
  · intro hy
    change (x, y) ∈ R
    rw [vertical_fibre_iff_zero_source_difference R base]
    have hzero : returnMass (y - y₀) = 0 := by
      rw [map_sub, hy, conservation base, sub_self]
    have hspan : y - y₀ ∈ Submodule.span ℚ (Set.range (verticalBasis (n := n) ⟨0, hn⟩)) :=
      zero_sum_mem_span_verticalBasis hn _ hzero
    revert hspan
    refine Submodule.span_induction (p := fun z _ ↦ (0, z) ∈ R) ?_ ?_ ?_ ?_
    · rintro z ⟨i, rfl⟩
      exact vertical i
    · exact R.zero_mem
    · intro a b _ _ ha hb
      simpa using R.add_mem ha hb
    · intro a z _ hz
      simpa using R.smul_mem a hz

/-- Two observed returns over the same source produce their retained vertical difference. -/
theorem same_source_outputs_vertical_difference
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n : ℕ} {R : Submodule ℚ (V × (Fin n → ℚ))}
    {x : V} {y₁ y₂ : Fin n → ℚ}
    (h₁ : (x, y₁) ∈ R) (h₂ : (x, y₂) ∈ R) :
    (0, y₂ - y₁) ∈ R := by
  simpa using R.sub_mem h₂ h₁

/-- An admitted output translates exactly by the vertical difference from a base output. -/
theorem translate_admitted_output_iff
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    {n : ℕ} {R : Submodule ℚ (V × (Fin n → ℚ))}
    {x : V} {y₀ y : Fin n → ℚ} (base : (x, y₀) ∈ R) :
    (x, y) ∈ R ↔ (0, y - y₀) ∈ R :=
  vertical_fibre_iff_zero_source_difference R base

end Soma.Holonics.Computation.HolonicConstitutiveFibreCollapse

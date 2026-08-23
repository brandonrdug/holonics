import ElementaryHolonics.Millennium.YangMills
import Mathlib.Data.Real.Archimedean

/-!
# Yang–Mills limit control — pointwise finite gaps do not produce a continuum gap

The exact finite transfer spectrum in `LatticeNet.lean` can be useful only after a scaling and
continuum-limit receipt. This file returns the sharp reason: every finite member of a family may
have a positive spectral gap while the family has no positive gap uniform in its scale.

The shrinking two-point spectra `{0, 1/(n+1)}` are an exact falsifier for the inference
"positive gap at every finite scale, therefore positive continuum mass gap." This theorem neither
constructs a Yang–Mills theory nor claims that an actual lattice gauge family behaves this way. It
names the additional uniformity consequence any lattice-to-continuum bridge must return.
-/

noncomputable section

namespace Soma.Holonics.Millennium.YangMillsLimit

/-- The spectral part of a positive mass-gap receipt. -/
def SpectrumHasMassGap (spectrum : Set ℝ) : Prop :=
  0 ∈ spectrum ∧
    (∀ μ ∈ spectrum, 0 ≤ μ) ∧
    (∃ μ ∈ spectrum, 0 < μ) ∧
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ μ ∈ spectrum, μ = 0 ∨ Δ ≤ μ

/-- One positive separator working at every admitted finite scale. -/
def HasUniformMassGap (spectrum : ℕ → Set ℝ) : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    ∀ scale μ, μ ∈ spectrum scale → μ = 0 ∨ Δ ≤ μ

/-- A two-point spectrum whose nonzero excitation approaches the vacuum. -/
def shrinkingSpectrum (scale : ℕ) : Set ℝ :=
  {0, 1 / (scale + 1 : ℝ)}

/-- Every member of the shrinking family has an exact positive gap. -/
theorem everyFiniteShrinkingSpectrumHasMassGap (scale : ℕ) :
    SpectrumHasMassGap (shrinkingSpectrum scale) := by
  have hpositive : 0 < 1 / (scale + 1 : ℝ) := by positivity
  refine ⟨by simp [shrinkingSpectrum], ?_, ?_, ?_⟩
  · intro μ hμ
    simp only [shrinkingSpectrum, Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · exact le_rfl
    · exact hpositive.le
  · exact ⟨1 / (scale + 1 : ℝ), by simp [shrinkingSpectrum], hpositive⟩
  · refine ⟨1 / (scale + 1 : ℝ), hpositive, ?_⟩
    intro μ hμ
    simp only [shrinkingSpectrum, Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr le_rfl

/-- **Finite positive gaps do not imply a positive continuum gap.** -/
theorem theShrinkingFamilyHasNoUniformMassGap :
    ¬ HasUniformMassGap shrinkingSpectrum := by
  rintro ⟨Δ, hΔ, hgap⟩
  obtain ⟨scale, hsmall⟩ := exists_nat_one_div_lt hΔ
  have hmember : 1 / (scale + 1 : ℝ) ∈ shrinkingSpectrum scale := by
    simp [shrinkingSpectrum]
  rcases hgap scale (1 / (scale + 1 : ℝ)) hmember with hzero | hlower
  · have hpositive : 0 < 1 / (scale + 1 : ℝ) := by positivity
    exact hpositive.ne' hzero
  · exact (not_le_of_gt hsmall) hlower

end Soma.Holonics.Millennium.YangMillsLimit

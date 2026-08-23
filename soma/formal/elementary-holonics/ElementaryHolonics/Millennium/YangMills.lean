import Mathlib.Data.Real.Basic

/-!
# Yang–Mills existence and mass gap — the continuum quantum-theory object

`LatticeNet.lean` is an exact finite `Z₂` transfer-matrix model and explicitly disclaims
Yang–Mills content. The Clay problem instead asks, for every compact simple gauge group, for a
nontrivial quantum Yang–Mills theory on `ℝ⁴` satisfying strong axiomatic quantum-field conditions
and carrying a positive spectral gap.

Mathlib currently has no Wightman/Osterwalder–Schrader reconstruction package or suitable
unbounded-Hamiltonian spectral owner. This file therefore imports the official quantifier and
spectral consequence while leaving compact-simple admission and continuum-QFT realization as
visible ports. It does not substitute a finite lattice spectrum for the requested theory, and no
theorem here asserts existence.
-/

noncomputable section

namespace Soma.Holonics.Millennium.YangMills

universe u v

/-- The typed boundary of the official Yang–Mills problem.

`isCompactSimple` must eventually mean compact gauge group with simple Lie algebra; Mathlib's
plain `IsSimpleGroup` is not a replacement, since standard gauge groups may have nontrivial
centre. `satisfiesAxioms` owes an axiomatic continuum quantum field theory at least as strong as
the Wightman/Osterwalder–Schrader requirements cited by the official statement. -/
structure Problem where
  /-- Addressed gauge groups. -/
  GaugeGroup : Type u
  /-- Candidate quantum theories for each gauge group. -/
  Theory : GaugeGroup → Type v
  /-- Admission as a compact simple gauge group in the Clay sense. -/
  isCompactSimple : GaugeGroup → Prop
  /-- The candidate is a quantum Yang–Mills theory on four-dimensional Euclidean space. -/
  isYangMillsOnRFour : (G : GaugeGroup) → Theory G → Prop
  /-- The candidate satisfies the required axiomatic quantum-field properties. -/
  satisfiesAxioms : (G : GaugeGroup) → Theory G → Prop
  /-- The candidate theory is nontrivial. -/
  isNontrivial : (G : GaugeGroup) → Theory G → Prop
  /-- The energy-mass spectrum above the vacuum. -/
  energySpectrum : (G : GaugeGroup) → Theory G → Set ℝ

/-- A theory has a positive mass gap when the vacuum lies at zero, the spectrum is nonnegative
and nontrivial, and every nonzero spectral value is bounded below by one positive `Δ`. -/
def HasMassGap (P : Problem) (G : P.GaugeGroup) (Q : P.Theory G) : Prop :=
  0 ∈ P.energySpectrum G Q ∧
    (∀ μ ∈ P.energySpectrum G Q, 0 ≤ μ) ∧
    (∃ μ ∈ P.energySpectrum G Q, 0 < μ) ∧
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ μ ∈ P.energySpectrum G Q, μ = 0 ∨ Δ ≤ μ

/-- **Yang–Mills existence and mass gap over an admitted continuum realization.** -/
def TheYangMillsExistenceAndMassGap (P : Problem) : Prop :=
  ∀ G, P.isCompactSimple G →
    ∃ Q : P.Theory G,
      P.isYangMillsOnRFour G Q ∧
        P.satisfiesAxioms G Q ∧
        P.isNontrivial G Q ∧
        HasMassGap P G Q

/-- A mass-gap return carries an explicit positive lower bound and its complete spectral law. -/
theorem hasMassGap_returnsPositiveSeparator
    {P : Problem} {G : P.GaugeGroup} {Q : P.Theory G}
    (h : HasMassGap P G Q) :
    ∃ Δ : ℝ, 0 < Δ ∧ ∀ μ ∈ P.energySpectrum G Q, μ = 0 ∨ Δ ≤ μ :=
  h.2.2.2

end Soma.Holonics.Millennium.YangMills

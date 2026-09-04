import ElementaryHolonics.Millennium.AdviceBar
import Mathlib.Tactic

/-!
# UniformityBar: pointwise is not uniform, and the gap is where two problems live

Three of the graph-network's edges so far are **bars** — theorems that a
plausible-looking construction cannot witness the statement it appears to witness.
This file states the species those three share and instantiates it at the two
Millennium objects where it is the standing trap.

The species is always the same failure: a family of positive quantities, one per
approximation level, whose **infimum is zero**; or a family of solutions, one per
finite horizon, whose **union does not reach the horizon**.  Pointwise holds; uniform
fails; and only the uniform statement is the Millennium one.

* **`thePositiveFamilyCanHaveZeroInfimum`** — positivity at every level does not give
  positivity in the limit.  This is the **Yang–Mills** trap exactly: a positive
  spectral gap at every lattice spacing is compatible with **no continuum mass gap**,
  which is why `LatticeNet` disclaims Yang–Mills content and why a finite lattice
  spectrum may not be substituted for the requested theory.
* **`theFiniteHorizonFamilyNeedNotReachTheHorizon`** — existence on `[0,T]` for every
  `T` below a threshold does not give existence at the threshold.  This is the
  **Navier–Stokes** trap exactly: local-in-time regularity for every finite time short
  of blow-up is precisely what a blow-up *has*, so it can never establish global
  regularity.
* **`theUniformStatementIsStrictlyStronger`** — and the two are genuinely different
  predicates, with the pointwise one implied by the uniform one and not conversely.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.UniformityBar

open Filter

/-! ## 1. Positive at every level, zero in the limit -/

/-- **A POSITIVE FAMILY CAN HAVE ZERO INFIMUM**: `1/(n+1)` is positive at every level
and tends to zero.  A gap at every approximation level is not a gap. -/
theorem thePositiveFamilyCanHaveZeroInfimum :
    ∃ g : ℕ → ℝ, (∀ n, 0 < g n) ∧ Filter.Tendsto g Filter.atTop (nhds 0) := by
  refine ⟨fun n : ℕ => 1 / ((n : ℝ) + 1), fun n => by positivity, ?_⟩
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **THE UNIFORM STATEMENT IS STRICTLY STRONGER**: a uniform positive lower bound
gives positivity at every level, and the converse fails by the family above. -/
theorem theUniformStatementIsStrictlyStronger :
    (∀ g : ℕ → ℝ, (∃ c > 0, ∀ n, c ≤ g n) → ∀ n, 0 < g n) ∧
      ¬ (∀ g : ℕ → ℝ, (∀ n, 0 < g n) → ∃ c > 0, ∀ n, c ≤ g n) := by
  constructor
  · rintro g ⟨c, hc, hcg⟩ n
    exact lt_of_lt_of_le hc (hcg n)
  · intro hbad
    obtain ⟨g, hpos, hlim⟩ := thePositiveFamilyCanHaveZeroInfimum
    obtain ⟨c, hc, hcg⟩ := hbad g hpos
    -- a positive uniform bound contradicts convergence to zero
    have hev : ∀ᶠ n in Filter.atTop, g n < c := by
      have := hlim (Iio_mem_nhds hc)
      simpa using this
    obtain ⟨n, hn⟩ := hev.exists
    exact absurd (hcg n) (not_le.mpr hn)

/-! ## 2. Every finite horizon, never the horizon -/

/-- **A FINITE-HORIZON FAMILY NEED NOT REACH THE HORIZON**: `t ↦ 1/(T − t)` is finite
on `[0,T')` for every `T' < T` and unbounded as `t → T`.  Regularity below every
finite time short of blow-up is exactly what a blow-up has. -/
theorem theFiniteHorizonFamilyNeedNotReachTheHorizon {T : ℝ} (hT : 0 < T) :
    (∀ T' : ℝ, 0 < T' → T' < T →
        ∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t ≤ T' → 1 / (T - t) ≤ M) ∧
      ¬ (∃ M : ℝ, ∀ t : ℝ, 0 ≤ t → t < T → 1 / (T - t) ≤ M) := by
  constructor
  · intro T' hT' hlt
    refine ⟨1 / (T - T'), fun t ht htT' => ?_⟩
    have h1 : 0 < T - T' := by linarith
    have h2 : 0 < T - t := by linarith
    have h3 : T - T' ≤ T - t := by linarith
    exact one_div_le_one_div_of_le h1 h3
  · rintro ⟨M, hM⟩
    -- the bound forces `T − t ≥ 1/M` for every `t < T`, which fails near `T`
    have hM0 : 0 < M := by
      have h1 : (0 : ℝ) ≤ T / 2 := by linarith
      have h2 : T / 2 < T := by linarith
      have := hM (T / 2) h1 h2
      have h3 : 0 < T - T / 2 := by linarith
      have h4 : 0 < 1 / (T - T / 2) := by positivity
      linarith
    set t : ℝ := T - min (T / 2) (1 / (2 * M)) with ht
    have hmin_pos : 0 < min (T / 2) (1 / (2 * M)) := by
      refine lt_min (by linarith) ?_
      positivity
    have hmin_le : min (T / 2) (1 / (2 * M)) ≤ T / 2 := min_le_left _ _
    have hmin_le2 : min (T / 2) (1 / (2 * M)) ≤ 1 / (2 * M) := min_le_right _ _
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have htT : t < T := by rw [ht]; linarith
    have hval := hM t ht0 htT
    have hTt : T - t = min (T / 2) (1 / (2 * M)) := by rw [ht]; ring
    rw [hTt] at hval
    have hchain : 1 / (1 / (2 * M)) ≤ 1 / min (T / 2) (1 / (2 * M)) :=
      one_div_le_one_div_of_le hmin_pos hmin_le2
    have h2M : 1 / (1 / (2 * M)) = 2 * M := by
      field_simp
    rw [h2M] at hchain
    linarith

end Soma.Holonics.Millennium.UniformityBar

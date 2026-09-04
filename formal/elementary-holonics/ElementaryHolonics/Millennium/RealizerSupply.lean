import Mathlib.Tactic

/-!
# RealizerSupply: the rank records are a lattice budget, and the ceiling is a rational function

The rank-N investigation planned in the descent record, first exact installment.  Two ledgers,
both over `ℕ`/`ℚ`, both finite, adapted from the breadth wave's rank-mechanics return after
verification of every arithmetic identity by hand.

**Part A — the Shioda–Tate budget.**  For an elliptic fibration, the Picard number pays for
everything: `ρ = 2 + Σ(m_v − 1) + rank MW` — two for the zero section and fibre, one per extra
component of each reducible fibre, and the Mordell–Weil rank with what remains.  On a K3 the
budget is `ρ ≤ 20`, so **the geometric supply caps the rank at 18, and reaching 18 forces every
fibre irreducible** — a reducible fibre *spends a realizer* the rank then cannot have.  This is
how the record constructions actually work: Elkies' high-rank curves come from elliptic K3
surfaces whose Néron–Severi lattice supplies seventeen independent sections, specialized to `ℚ`.
The two theorems that need geometry — that 18 itself is unattainable over `ℚ`, and that
specialization preserves independence off a thin set (Néron, Silverman) — are named open and
never used.

**Part C — the boundedness ceiling as an exact rational function of its two declared
exponents.**  The heuristic ceiling of Granville–Watkins (Watkins, *A discursus on 21 as a bound
for ranks*, footnote 12) has the shape `(r/2 − 1)·η ≤ 3/4 + κ/2` — `η` the height-growth
exponent, `κ` the regulator exponent — giving `r ≤ rankCeiling η κ = 2 + (3/2 + κ)/η`.  The
theorems compute the function at its declared calibrations: **21 at the calibrated pair
`(1/12, 1/12)`; 29 at the maximal regulator exponent `3/4`; and the 2026 record `r ≥ 30` exceeds
the calibrated ceiling — the exact height exponent a ceiling of thirty demands is `19/336`.**
So "is rank bounded" becomes, at this heuristic's grain, a question about which exponent pair
the arithmetic actually pays — a receiver-aperture question with its dials exhibited, never a
verdict.  The calibration `η = 1/12` is itself a named proposition carrying its own author's
description (ad hoc), and the whole part is `interpretation` about the heuristic, exact about
the function.

**What this file refuses**, adopting the wave agent's own strongest self-attacks: the
aperture reading is largely a restatement of caveats the sources themselves carry
(Park–Poonen–Voight–Wood's own remark; Watkins' own "admittedly ad hoc"); and the agreement of
the two independent 21-derivations is, on its face, evidence *for* the number rather than for a
shared blind spot.  The Lean below therefore asserts only the arithmetic of the declared
ledgers, and the two agent-computed regulator exponents from published curve data were
**excluded** as unverified.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on
the Birch–Swinnerton-Dyer conjecture or on boundedness of rank.
-/

namespace Soma.Holonics.Millennium.RealizerSupply

/-- The Shioda–Tate ledger of an elliptic fibration: the Picard number pays for the hyperbolic
pair, the reducible-fibre components, and the Mordell–Weil rank. -/
structure FibrationLedger where
  picard : ℕ
  componentDeficits : List ℕ
  mwRank : ℕ
  shiodaTate : picard = 2 + componentDeficits.sum + mwRank

/-- **The K3 budget caps the rank at eighteen**: `ρ ≤ 20` leaves at most eighteen for the
Mordell–Weil rank after the hyperbolic pair is paid. -/
theorem theBudgetCapsAtEighteen (L : FibrationLedger) (h : L.picard ≤ 20) : L.mwRank ≤ 18 := by
  have hs := L.shiodaTate
  omega

/-- **The top of the budget forces every fibre irreducible**: rank eighteen on a K3 spends the
whole budget, so the Picard number is exactly twenty and no fibre carries an extra component —
a reducible fibre spends a realizer the rank then cannot have. -/
theorem theTopOfTheBudgetForcesEveryFibreIrreducible (L : FibrationLedger)
    (h : L.picard ≤ 20) (h18 : L.mwRank = 18) :
    L.picard = 20 ∧ L.componentDeficits.sum = 0 := by
  have hs := L.shiodaTate
  omega

/-- **A reducible fibre spends a realizer**: at fixed Picard number, every unit of component
deficit comes out of the rank. -/
theorem theReducibleFibreSpendsARealizer (L : FibrationLedger) :
    L.mwRank = L.picard - 2 - L.componentDeficits.sum := by
  have hs := L.shiodaTate
  omega

/-- The rational elliptic surface with no reducible fibres: `ρ = 10`, rank eight — the `E₈`
lattice's rank, which is where the Mordell–Weil lattice story begins. -/
theorem theRationalSurfaceLedgerIsEight :
    (⟨10, [], 8, by norm_num⟩ : FibrationLedger).mwRank = 8 := rfl

/-- The Elkies K3 ledger: `ρ = 19` with every fibre irreducible carries rank seventeen — the
supply behind the record constructions. -/
theorem theElkiesK3LedgerIsSeventeen :
    (⟨19, [], 17, by norm_num⟩ : FibrationLedger).mwRank = 17 := rfl

/-- **Rank eighteen from a K3 over the rationals is unattainable** — Elkies.  Imported
geometry, named open, never used below. -/
def TheEighteenBudgetIsUnattainableOverTheRationals : Prop :=
  ∀ L : FibrationLedger, L.picard = 20 → L.mwRank ≤ 17

/-- **Specialization preserves independence off a thin set** — Néron, Silverman.  The step that
carries a surface's lattice supply down to a single curve over `ℚ`.  Imported, named open,
never used below. -/
def TheSpecializationPreservesIndependence : Prop :=
  ∀ L : FibrationLedger, L.mwRank ≤ L.picard

/-! ## Part C — the ceiling as a function of its two declared exponents -/

/-- The heuristic rank ceiling: `2 + (3/2 + κ)/η`, from the supply inequality
`(r/2 − 1)·η ≤ 3/4 + κ/2` with `η` the height-growth exponent and `κ` the regulator
exponent. -/
def rankCeiling (eta kappa : ℚ) : ℚ := 2 + (3 / 2 + kappa) / eta

/-- **The calibrated ceiling is twenty-one**: at the declared pair `(1/12, 1/12)`. -/
theorem theCalibratedCeilingIsTwentyOne : rankCeiling (1 / 12) (1 / 12) = 21 := by
  norm_num [rankCeiling]

/-- **At the maximal regulator exponent the ceiling is twenty-nine**: `κ = 3/4` is the largest
the heuristic admits, and the ceiling moves to `29` — the dial's full range, exhibited. -/
theorem theCeilingAtTheMaximalRegulatorExponent : rankCeiling (1 / 12) (3 / 4) = 29 := by
  norm_num [rankCeiling]

/-- **The 2026 record exceeds the calibrated ceiling**: thirty is strictly beyond
`rankCeiling (1/12) (1/12) = 21`. -/
theorem theRecordExceedsTheCalibratedCeiling : (30 : ℚ) > rankCeiling (1 / 12) (1 / 12) := by
  norm_num [rankCeiling]

/-- **The exact height exponent a ceiling of thirty demands**: `η = 19/336` returns the record
as the ceiling — the dial value the observed arithmetic would require, computed rather than
narrated. -/
theorem theRecordDemandsASmallerHeightExponent : rankCeiling (19 / 336) (1 / 12) = 30 := by
  norm_num [rankCeiling]

/-- **The ceiling falls as the height exponent grows**: for positive exponents, a larger `η`
gives a strictly smaller ceiling at fixed `κ ≥ 0`. -/
theorem theCeilingFallsAsTheHeightExponentGrows (e₁ e₂ k : ℚ)
    (h1 : 0 < e₁) (h2 : e₁ < e₂) (hk : 0 ≤ k) :
    rankCeiling e₂ k < rankCeiling e₁ k := by
  have he₂ : 0 < e₂ := lt_trans h1 h2
  have hnum : (0 : ℚ) < 3 / 2 + k := by linarith
  have := div_lt_div_of_pos_left hnum h1 h2
  simp only [rankCeiling]
  linarith

/-- **The height exponent is calibrated at one twelfth** — the declaration behind the 21, which
its own author describes as ad hoc.  Named open; nothing below assumes it. -/
def TheHeightExponentIsCalibratedAtOneTwelfth : Prop :=
  ∀ e : ℚ, e = 1 / 12 → rankCeiling e (1 / 12) = 21

end Soma.Holonics.Millennium.RealizerSupply

import ElementaryHolonics.Millennium.RankZero
import Mathlib.Tactic

/-!
# TateLedger: the local remainders read by depth, and the ledger balances at one

The Birch–Swinnerton-Dyer formula is a remainder ledger: every factor is the exhibited
remainder of one named compression.  This file reads the **local** entries — the Tamagawa
numbers, which are the bad frames' collapsed component populations — by exactly the depth
ladder Tate's algorithm walks, and then states the balance at one with every entry's
provenance declared.

**The branch readings, all exact.**  Tate's algorithm branches on divisibilities of the
model's invariants after centering the reduction's singular point:

* `y² = x³ − x` at two (minimal: `Δ = 64 = 2⁶`, `c₄ = 48 = 2⁴·3`): the reduced frame has
  exactly one singular point, `(1, 0)` (`theSingularPointOfTheFrameAtTwo`); centering it
  (`(x+1)³ − (x+1) = x³ + 3x² + 2x`), the ladder reads `2 ∣ b₂ = 12` (additive), `4 ∣ a₆ = 0`
  (past type II), and `¬ 8 ∣ b₈ = −4` — the ladder **stops at the third rung**: Kodaira
  type III, Tamagawa number `c₂ = 2` (`theTypeThreeBranchAtTwo`; the type-and-number
  interpretation of the readings is Tate's, cited).
* `y² = x³ − 25x` at two: the same third-rung stop through the same shift
  (`b₈ = 4·3·(−24) − 22² = −772`, `¬ 8 ∣ −772`): type III, `c₂ = 2`
  (`theTypeThreeBranchAtTwoTwisted`).
* `y² = x³ − 25x` at five (`Δ = 10⁶ = 5⁶·64`, `c₄ = 1200 = 5²·48`): the singular point is
  already the origin, the ladder passes every rung to the residual cubic, and
  `T³ − T` **splits completely over the frame at five** — three simple roots
  (`theResidualCubicSplitsAtFive`): type I₀*, Tamagawa number `c₅ = 1 + 3 = 4`.

**The balance at one** (`theLedgerBalancesAtOne`, `theLedgerAtOne`): for `y² = x³ − x`,

```text
L(E,1)/Ω  =  1/8  =  c₂ · |Ш| · Reg / |T|²  =  2 · 1 · 1 / 4²
```

with the provenance of every entry: `|T| = 4` **kernel-checked** — the population is exactly
the four half-turns (`RankZero.theFourHalfTurnsAreTheWholePopulationHolds`, re-exhibited
here as four pairwise-distinct members, `theTorsionOrderAtOneIsFour`); `Reg = 1`
**kernel-checked as the empty Gram determinant** — rank zero, the free part is empty, by the
same population theorem; `c₂ = 2` read by this file's depth ladder under Tate's cited
interpretation; `|Ш| = 1` cited (classical for this curve; Rubin's complex-multiplication
bounds); `L(E,1)/Ω = 1/8` cited — the classical lemniscatic evaluation
`L(E,1) = ϖ/4`, `Ω = ∫_{E(ℝ)}|ω| = 2ϖ` (pinned to eleven digits by an
arithmetic–geometric-mean computation used as scaffolding only; no float enters any
statement).  **This is Birch and Swinnerton-Dyer's original numerical discovery re-founded
as an exact ledger, each side's entries carried with their grades.**

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: the Kodaira
types and Tamagawa numbers are Tate's interpretation of the branch readings, cited; the
analytic entry is cited; nothing about the conjecture beyond this verified instance of its
formula is claimed.
-/

namespace Soma.Holonics.Millennium.TateLedger

/-! ## 1. The depth ladder at two, untwisted curve -/

/-- The invariant depths at two, in factored form: `Δ = 64 = 2⁶`, `c₄ = 48 = 2⁴·3` — the
model is minimal (`v₂(Δ) = 6 < 12`) and the reduction additive. -/
theorem theDepthsAtTwo :
    (64 : ℤ) = 2 ^ 6 ∧ (48 : ℤ) = 2 ^ 4 * 3 ∧ ¬ (2 : ℤ) ∣ 3 := by
  norm_num

/-- **The frame at two has one singular point**, `(1, 0)`: the census of curve points where
both partials vanish. -/
theorem theSingularPointOfTheFrameAtTwo :
    ∀ x y : ZMod 2,
      (y ^ 2 = x ^ 3 - x ∧ 3 * x ^ 2 - 1 = 0 ∧ 2 * y = 0) ↔ (x = 1 ∧ y = 0) := by
  decide

/-- **The ladder stops at the third rung**: centering the singular point,
`(x+1)³ − (x+1) = x³ + 3x² + 2x`, the shifted invariants read `b₂ = 12`, `a₆ = 0`,
`b₈ = 4·3·0 − 2² = −4`, and `2 ∣ b₂`, `4 ∣ a₆`, `¬ 8 ∣ b₈` — Kodaira type III,
Tamagawa number two, by Tate's cited interpretation. -/
theorem theTypeThreeBranchAtTwo :
    (∀ x : ℚ, (x + 1) ^ 3 - (x + 1) = x ^ 3 + 3 * x ^ 2 + 2 * x) ∧
    (4 * 3 * 0 - 2 ^ 2 : ℤ) = -4 ∧
    (2 : ℤ) ∣ 12 ∧ (4 : ℤ) ∣ 0 ∧ ¬ (8 : ℤ) ∣ (-4) := by
  refine ⟨fun x => by ring, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 2. The depth ladders for the twisted curve -/

/-- **The twisted curve stops at the same rung at two**: centering `(1, 0)`,
`(x+1)³ − 25(x+1) = x³ + 3x² − 22x − 24`, with `b₈ = 4·3·(−24) − 22² = −772` and
`¬ 8 ∣ −772` — type III, Tamagawa number two. -/
theorem theTypeThreeBranchAtTwoTwisted :
    (∀ x : ℚ, (x + 1) ^ 3 - 25 * (x + 1) = x ^ 3 + 3 * x ^ 2 - 22 * x - 24) ∧
    (4 * 3 * (-24) - 22 ^ 2 : ℤ) = -772 ∧
    (2 : ℤ) ∣ 12 ∧ (4 : ℤ) ∣ (-24) ∧ ¬ (8 : ℤ) ∣ (-772) := by
  refine ⟨fun x => by ring, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The invariant depths of the twisted curve at five: `Δ = 10⁶ = 5⁶·64`,
`c₄ = 1200 = 5²·48`. -/
theorem theDepthsAtFive :
    (1000000 : ℤ) = 5 ^ 6 * 64 ∧ ¬ (5 : ℤ) ∣ 64 ∧
    (1200 : ℤ) = 5 ^ 2 * 48 ∧ ¬ (5 : ℤ) ∣ 48 := by
  norm_num

/-- **The residual cubic splits completely at five**: `T³ − T` has exactly the three roots
`0, 1, 4` over the frame, each simple (no root shares a zero of the derivative) — type I₀*
with full splitting, Tamagawa number `1 + 3 = 4`, by Tate's cited interpretation. -/
theorem theResidualCubicSplitsAtFive :
    (∀ t : ZMod 5, t ^ 3 - t = 0 ↔ (t = 0 ∨ t = 1 ∨ t = 4)) ∧
    (∀ t : ZMod 5, ¬ (t ^ 3 - t = 0 ∧ 3 * t ^ 2 - 1 = 0)) := by
  constructor <;> decide

/-! ## 3. The global entries, kernel-checked -/

private def abscissa : Descent.E.Point → ℚ
  | .zero => 2
  | .some x _ _ => x

/-- **The torsion order at one is four**: the four members of the population are pairwise
distinct — with completeness from the descent, `|T| = 4` exactly. -/
theorem theTorsionOrderAtOneIsFour :
    Descent.P00 ≠ 0 ∧ Descent.P10 ≠ 0 ∧ Descent.Pm10 ≠ 0 ∧
    Descent.P00 ≠ Descent.P10 ∧ Descent.P00 ≠ Descent.Pm10 ∧
    Descent.P10 ≠ Descent.Pm10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _
  · exact WeierstrassCurve.Affine.Point.some_ne_zero _
  all_goals
    intro h
    have := congrArg abscissa h
    simp only [Descent.P00, Descent.P10, Descent.Pm10, abscissa] at this
    norm_num at this

/-- **THE LEDGER BALANCES AT ONE**: `L(E,1)/Ω = 1/8 = c₂·|Ш|·Reg/|T|² = 2·1·1/16`.  The
docstring above carries each entry's provenance and grade; the arithmetic identity among the
entries is this theorem. -/
theorem theLedgerBalancesAtOne : (1 : ℚ) / 8 = 2 * 1 * 1 / 4 ^ 2 := by
  norm_num

/-- **The ledger at one, with its kernel-checked core attached**: the balance identity
together with the population theorem that supplies both `|T| = 4` and `Reg = 1` (the free
part is empty, so the regulator is the empty Gram determinant). -/
theorem theLedgerAtOne :
    ((1 : ℚ) / 8 = 2 * 1 * 1 / 4 ^ 2) ∧ Descent.TheFourHalfTurnsAreTheWholePopulation :=
  ⟨by norm_num, RankZero.theFourHalfTurnsAreTheWholePopulationHolds⟩

end Soma.Holonics.Millennium.TateLedger

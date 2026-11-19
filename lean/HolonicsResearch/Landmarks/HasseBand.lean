import HolonicsResearch.Landmarks.HasseSite
import HolonicsResearch.Geometry.CellPassBand

/-!
# Every good prime of a congruent-number curve is a cell inside its pass band

At a good prime `p` the local factor of `E_n : y² = x³ − n²x` is `1 − a_p T + p T²`
(`Landmarks/HasseSite.lean`). `Geometry/CellPassBand.scaled_factor` reads a factor
`1 − (b + 1)c·T + bT²` as a cell of ratio `b` scaled by `√b`, with pass band `|c| ≤ edge b`,
`edge b = 2√b/(b + 1)`. With `b = p` and `c = a_p/(p + 1)`, Hasse's bound from the tree's own
point counts places the prime's site inside that band.

Sources. Atlas rows `bsd.hasse-site-rotation` and `rh.frobenius-cell-junction-delay`
(`docs/atlas/targets.tsv`); record
`research/records/2026-11-15_UNDER_A_CHANGE_OF_SCALE_A_MODE_IS_A_COUNT_OR_A_TURN_*.md` §5.

[proved-derived; formal-checked] What is proved.

1. **The site is in the band** (`congruent_site_in_band`): for an odd prime `p ∤ n`,
   `|a_p(E_n)/(p + 1)| ≤ edge p`, from `HasseSite.hasse_bound` and
   `CellPassBand.sq_le_iff_abs_le_edge`.
2. **The site is never on the band's edge** (`congruent_site_strictly_in_band`):
   `|a_p(E_n)/(p + 1)| < edge p`, from `SiteKind.hasse_site_is_rotation` (a prime is not a
   square) and `CellPassBand.sq_lt_iff_abs_lt_edge`.

Limits. The statement is for the congruent-number family `E_n` at odd primes `p ∤ n`, where
`HasseSite.hasse_bound` holds from the literal point count; no other curve is covered. The value
`a_p/(p + 1)` is compared with the edge; that it is the cosine of a turn `φ` of an actual cell
(the angle `arccos` of it) is not constructed here, and nothing is said about how these values
are distributed over the primes.

Computational object: the helical pair interaction. Of the winding guide's six general objects
this module touches the helix (the site's turn) and the pair (the Weil root and its conjugate);
faces and placement, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas rows `bsd.hasse-site-rotation` and `rh.frobenius-cell-junction-delay`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Landmarks.HasseBand

open Holonics.EllipticCurve.BirchSwinnertonDyer
open Holonics.Geometry.CellPassBand (edge sq_le_iff_abs_le_edge sq_lt_iff_abs_lt_edge)

variable {p : ℕ} [Fact p.Prime]

/-- [proved-derived; formal-checked] **A good prime's site lies in its cell's pass band:**
`|a_p(E_n)/(p + 1)| ≤ 2√p/(p + 1)` for every odd prime `p ∤ n`. -/
theorem congruent_site_in_band (n : ℕ) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    |((traceOfFrobenius n p : ℤ) : ℝ) / ((p : ℝ) + 1)| ≤ edge (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hb : ((traceOfFrobenius n p : ℤ) : ℝ) ^ 2 ≤ 4 * (p : ℝ) := by
    exact_mod_cast Holonics.Landmarks.HasseSite.hasse_bound n hp2 hpn
  rw [← sq_le_iff_abs_le_edge hp, mul_div_cancel₀ _ hp1]
  exact hb

/-- [proved-derived; formal-checked] **A good prime's site is never on the band's edge:**
`|a_p(E_n)/(p + 1)| < 2√p/(p + 1)`, since a prime determinant is not a square
(`SiteKind.hasse_site_is_rotation`). -/
theorem congruent_site_strictly_in_band (n : ℕ) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    |((traceOfFrobenius n p : ℤ) : ℝ) / ((p : ℝ) + 1)| < edge (p : ℝ) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hrot := Holonics.Compression.Landmark.SiteKind.hasse_site_is_rotation p Fact.out _
    (Holonics.Landmarks.HasseSite.hasse_bound n hp2 hpn)
  rw [Holonics.Compression.Landmark.SiteKind.siteKind_eq_rotation_iff] at hrot
  have hq : ((traceOfFrobenius n p : ℤ) : ℚ) ^ 2 < 4 * (p : ℚ) := hrot
  have hb : ((traceOfFrobenius n p : ℤ) : ℝ) ^ 2 < 4 * (p : ℝ) := by
    exact_mod_cast hq
  rw [← sq_lt_iff_abs_lt_edge hp, mul_div_cancel₀ _ hp1]
  exact hb

end Holonics.Landmarks.HasseBand

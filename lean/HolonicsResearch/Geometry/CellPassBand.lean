import Holonics.Compression.Landmark.SiteKind
import HolonicsResearch.HNN.CarriedRate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# A cell of a stretch `b` and a turn `φ` is a rotation where `|cos φ| < 2√b/(b + 1)`

One quadratic, `z² − (b + 1)c·z + b`, read in five places: a junction of ratio `b`, a cell (a
stretch of ratio `b` times a turn `φ`), a prime's local factor `1 − aT + bT²`, the tree with
`b + 1` branches, and the engine's junction return. In each the pass band is `|c| ≤ edge b`,
`edge b = 2√b/(b + 1) = sech(½ ln b)`.

Sources. Atlas rows `rh.frobenius-cell-junction-delay` (`docs/atlas/targets.tsv`),
`wave.junction-boost-delay-turn` (`docs/atlas/physics.tsv`), `bsd.hasse-site-rotation`,
`trace.tree-walk-floor` (`docs/atlas/geometry.tsv`) and `contact.pass-reach-gap`. Records
`research/records/2026-11-15_UNDER_A_CHANGE_OF_SCALE_A_MODE_IS_A_COUNT_OR_A_TURN_*.md` §5 and
`research/records/2026-11-13_THE_TICK_HOLDS_THE_JUNCTIONS_ANCHOR_*.md` §6 item 4 (the engine's
junction return `x^(k+1) = v^k + Γ(v^k − x^(k−1))`, whose modes solve `z² − (1 + Γ)λz + Γ = 0`).
The engine's owner is `crates/engine/src/carry.rs` (`junction_gamma`: `Γ = (ρ − 1)/(ρ + 1)`,
`ρ = 2^ℓ`). The return's own owner is `HolonicsResearch/HNN/RestitutionFamily.lean` (atlas
`junction.restitution-family`, `tower.field-tick-return`): the restitution about a junction's
anchor, its modes and their modulus `√Γ` (`turning_root_normSq`), and no own return at
`Γ = 1/(d − 1)` on `d` equal ports (`ownReturn_equal_ports`). Section E restates none of that; it
reads the return's band in this module's `edge` and on the engine's chart. The quadratic's three
kinds also stand as the companion cell with its norm form in `HolonicsResearch/Coupling/KreinForm.lean`
(atlas `trace.cell-norm-algebra`); this module's chart is the stretch and the turn, where the
band's edge is the junction's own number.

[proved-derived; formal-checked] What is proved.

1. **The junction** of ratio `b > 0`. Its reflection `reflect b = (b − 1)/(b + 1)` and its passed
   power `pass b = 4b/(b + 1)²` sum as `reflect² + pass = 1` (`reflect_sq_add_pass`); the edge
   squares to the passed power (`edge_sq`), lies in `(0, 1]` (`edge_pos`, `edge_le_one`), is `1`
   only at `b = 1` (`edge_eq_one_iff`) and is the same for `b` and `b⁻¹` (`edge_inv`). The gain in
   nats `gain b = ln((b + 1)/(2√b))` has `e^(−gain) = edge` (`exp_neg_gain`), is nonnegative
   (`gain_nonneg`) and equals `−½ ln(pass b)` (`gain_eq`), Levinson's step `−½ ln(1 − k²)` at
   `k = reflect b`.
2. **The band as a comparison of squares** (`sq_le_iff_abs_le_edge`, `sq_lt_iff_abs_lt_edge`,
   `sq_eq_iff_abs_eq_edge`): for every real `c`, `((b + 1)c)² ≤ 4b ↔ |c| ≤ edge b`, and the same
   with `<` and with `=`.
3. **The cell** `cell b φ` has determinant one (`cell_det`) and trace `(b + 1)cos φ/√b`
   (`cell_trace`, `cell_trace_sq`); `tr² ≤ 4 ↔ |cos φ| ≤ edge b` (`trace_sq_le_four_iff`); its
   site kind (`SiteKind.siteKind`) is a rotation, the null lock or a boost as `|cos φ|` is below,
   on or above the edge (`cell_rotation_iff`, `cell_null_iff`, `cell_boost_iff`). Both sides of
   the edge occur at every `b ≠ 1`: the turnless cell is a boost (`cell_zero_turn_boost`) and the
   quarter-turn cell is a rotation at every `b` (`cell_quarter_turn_rotation`).
4. **The cell scaled by the junction's half is a prime's factor** (`sqrt_smul_cell`,
   `scaled_factor`): `det(1 − T·√b·cell) = 1 − (b + 1)cos φ·T + bT²`. Its Hasse interval is the
   band (`hasse_iff`, `factor_rotation_iff`), and inside the band every root of
   `z² − (b + 1)cos φ·z + b` has squared modulus `b` (`weil_root_normSq`, through
   `CarriedRate.root_normSq`).
5. **The tree with `b + 1` branches.** The radial mode `radial b θ n = (e^{iθ}/√b)ⁿ` solves the
   tree's radial recurrence `b·f(n+2) + f(n) = 2√b cos θ · f(n+1)` (`radial_recurrence`) with
   `|f(n)|² bⁿ = 1` (`radial_normSq`), and a value `(b + 1)cos φ` is `2√b cos θ` for some real `θ`
   if and only if it is in the band (`tree_band`): Kesten's radius `2√b` read against the degree
   `b + 1`.
6. **The engine's junction return** `x' = v + Γ(v − x_prev)` on a mode `v = λx` is the step
   `(1 + Γ)λ·x − Γ·x_prev` (`return_mode`); at `Γ = 1/b` it is the recurrence of the walk
   without backtracking on the tree of `b + 1` branches (`return_tree`); for `Γ > 0` its discriminant is nonpositive if and
   only if `|λ| ≤ edge Γ` (`return_band`, `return_rotation_iff`), where every root has squared
   modulus `Γ` (`return_root_normSq`); one instance outside the band, `Γ = 1`, `λ = 5/4`, has a
   root off that circle (`root_off_circle_outside_band`), and for `Γ < 0` the mode is a
   reflection at every `λ` (`return_reflection_of_neg`). On the engine's chart
   `Γ = (ρ − 1)/(ρ + 1)`, `Γ > 0` if and only if `ρ > 1` (`chart_pos_iff`); there the edge
   squares to `1 − ρ⁻²` (`edge_chart`), so the band is `λ² ≤ 1 − ρ⁻²` (`return_band_chart`).
7. **The delay at `b = 3`** (`arcsin_edge_three`): `arcsin(edge 3) = π/3`.

Limits. Nothing here says that a given material is a cell: `cell b φ` is one chart of a
determinant-one site, a diagonal stretch times a turn, and a general site reaches it only after a
change of frame that is not constructed here. `radial_recurrence` states that the radial modes
solve the recurrence; that these are the whole spectrum of the tree's walk operator (Kesten's
theorem) is not proved here. `tree_band` is a statement about real `θ` only. `return_band` reads
one mode of the return and only where `Γ > 0`: the engine's `junction_gamma` admits `⌊ℓ⌋` from
`−31` to `30`, so `Γ` takes both signs and is `0` at the matched load `ℓ = 0`, and on `ℓ ≤ 0`
the band is no ruler. The engine's junction with its declared widths and releases is not
modelled, and the built tick adds (`F(x) = x + g(x)`, atlas `tower.field-tick-return`), so in the
engine a mode's `λ` is the tick's multiplier `1 + μ` and the return is a site's carried rate; it
is the walk without backtracking (`return_tree`) only for a tick that sets a site to a mean of
partners whose contacts carry both ways. `arcsin_edge_three` is the one delay evaluated; no table of delays is claimed.

Computational object: the helical pair interaction. Of the winding guide's six general objects
this module touches the helix (the delay, a turn), the pair (the cell's two roots, a conjugate
pair on the circle of radius `√b`) and the tower thread (a junction between two levels); faces and
placement, the cell holonomy and the tube stay attached.

Consumers: `HolonicsResearch/HNN/PumpedCarry.lean` (the band of a pumped step),
`HolonicsResearch/Landmarks/HasseBand.lean` (a good prime's site inside its band), the engine's
junction (`junction_gamma`) as a ruler on its chart, and the atlas rows named above.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.CellPassBand

open Holonics.Compression.Landmark.SiteKind

/-! ## A. The junction -/

/-- [definition] The band's edge `2√b/(b + 1)`, which is `sech(½ ln b)`. -/
def edge (b : ℝ) : ℝ := 2 * Real.sqrt b / (b + 1)

/-- [definition] The junction's passed power `4b/(b + 1)²`. -/
def pass (b : ℝ) : ℝ := 4 * b / (b + 1) ^ 2

/-- [definition] The junction's reflection `(b − 1)/(b + 1)`, which is `tanh(½ ln b)`. -/
def reflect (b : ℝ) : ℝ := (b - 1) / (b + 1)

/-- [definition] The junction's gain in nats, `ln((b + 1)/(2√b))`, which is `ln cosh(½ ln b)`. -/
def gain (b : ℝ) : ℝ := Real.log ((b + 1) / (2 * Real.sqrt b))

/-- [definition] The cell: a stretch of ratio `b` (`diag(√b, 1/√b)`) times a turn `φ`. -/
def cell (b φ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt b * Real.cos φ, -(Real.sqrt b * Real.sin φ);
     Real.sin φ / Real.sqrt b, Real.cos φ / Real.sqrt b]

/-- [proved-standard; formal-checked] **Reflected and passed power sum to one:**
`((b − 1)/(b + 1))² + 4b/(b + 1)² = 1`. -/
theorem reflect_sq_add_pass {b : ℝ} (hb : 0 < b) : reflect b ^ 2 + pass b = 1 := by
  have h : b + 1 ≠ 0 := by positivity
  unfold reflect pass
  field_simp
  ring

/-- [proved-standard; formal-checked] **The edge squares to the passed power.** -/
theorem edge_sq {b : ℝ} (hb : 0 < b) : edge b ^ 2 = pass b := by
  unfold edge pass
  rw [div_pow, mul_pow, Real.sq_sqrt hb.le]
  norm_num

/-- [proved-standard; formal-checked] The edge is positive. -/
theorem edge_pos {b : ℝ} (hb : 0 < b) : 0 < edge b :=
  div_pos (mul_pos two_pos (Real.sqrt_pos.mpr hb)) (by linarith)

/-- [proved-standard; formal-checked] **The edge is at most one:** `2√b ≤ b + 1`, from
`(√b − 1)² ≥ 0`. -/
theorem edge_le_one {b : ℝ} (hb : 0 < b) : edge b ≤ 1 := by
  unfold edge
  rw [div_le_one (by linarith)]
  nlinarith [sq_nonneg (Real.sqrt b - 1), Real.sq_sqrt hb.le]

/-- [proved-standard; formal-checked] **The edge is one only at the matched junction** `b = 1`. -/
theorem edge_eq_one_iff {b : ℝ} (hb : 0 < b) : edge b = 1 ↔ b = 1 := by
  have hs := Real.sq_sqrt hb.le
  unfold edge
  rw [div_eq_one_iff_eq (by linarith : b + 1 ≠ 0)]
  constructor
  · intro h
    have h0 : (Real.sqrt b - 1) ^ 2 = 0 := by nlinarith
    have h1 : Real.sqrt b = 1 := by
      have := (pow_eq_zero_iff (two_ne_zero)).mp h0
      linarith
    rw [← hs, h1]
    norm_num
  · rintro rfl
    rw [Real.sqrt_one]
    norm_num

/-- [proved-standard; formal-checked] **The edge does not tell `b` from `b⁻¹`:** a junction read
from either side has the same band. -/
theorem edge_inv {b : ℝ} (hb : 0 < b) : edge b⁻¹ = edge b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have h1 : b + 1 ≠ 0 := by positivity
  have h2 : b⁻¹ + 1 ≠ 0 := by positivity
  have hbi : b * b⁻¹ = 1 := mul_inv_cancel₀ hb.ne'
  unfold edge
  rw [Real.sqrt_inv, div_eq_div_iff h2 h1]
  have e : (Real.sqrt b)⁻¹ = Real.sqrt b * b⁻¹ := by
    have h3 : (Real.sqrt b)⁻¹ * b = Real.sqrt b := by
      calc (Real.sqrt b)⁻¹ * b = (Real.sqrt b)⁻¹ * (Real.sqrt b * Real.sqrt b) := by rw [hsq]
        _ = Real.sqrt b := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    calc (Real.sqrt b)⁻¹ = (Real.sqrt b)⁻¹ * (b * b⁻¹) := by rw [hbi, mul_one]
      _ = (Real.sqrt b)⁻¹ * b * b⁻¹ := by ring
      _ = Real.sqrt b * b⁻¹ := by rw [h3]
  rw [e]
  linear_combination (2 * Real.sqrt b) * hbi

/-- [proved-standard; formal-checked] **The edge is the gain's attenuation:**
`e^(−gain b) = edge b`. -/
theorem exp_neg_gain {b : ℝ} (hb : 0 < b) : Real.exp (-gain b) = edge b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hpos : 0 < (b + 1) / (2 * Real.sqrt b) := by positivity
  unfold gain edge
  rw [Real.exp_neg, Real.exp_log hpos, inv_div]

/-- [proved-standard; formal-checked] The gain is nonnegative. -/
theorem gain_nonneg {b : ℝ} (hb : 0 < b) : 0 ≤ gain b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  unfold gain
  apply Real.log_nonneg
  rw [one_le_div (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt b - 1), Real.sq_sqrt hb.le]

/-- [proved-standard; formal-checked] **Levinson's step:** `gain b = −½ ln(pass b)`, that is
`−½ ln(1 − k²)` at `k = reflect b` (`reflect_sq_add_pass`). -/
theorem gain_eq {b : ℝ} (hb : 0 < b) : gain b = -(1 / 2) * Real.log (pass b) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hg : gain b = -Real.log (edge b) := by
    unfold gain edge
    rw [← Real.log_inv, inv_div]
  rw [hg, ← edge_sq hb, Real.log_pow]
  push_cast
  ring

/-! ## The band as a comparison of squares -/

/-- [proved-derived; formal-checked] **The band, without a square root:**
`((b + 1)c)² ≤ 4b ↔ |c| ≤ edge b`. -/
theorem sq_le_iff_abs_le_edge {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ((b + 1) * c) ^ 2 ≤ 4 * b ↔ |c| ≤ edge b := by
  have hpos : (0 : ℝ) < (b + 1) ^ 2 := by positivity
  rw [← sq_le_sq₀ (abs_nonneg c) (edge_pos hb).le, sq_abs, edge_sq hb, pass, le_div_iff₀ hpos,
    mul_pow, mul_comm]

/-- [proved-derived; formal-checked] **The open band:** `((b + 1)c)² < 4b ↔ |c| < edge b`. -/
theorem sq_lt_iff_abs_lt_edge {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ((b + 1) * c) ^ 2 < 4 * b ↔ |c| < edge b := by
  have hpos : (0 : ℝ) < (b + 1) ^ 2 := by positivity
  rw [← sq_lt_sq₀ (abs_nonneg c) (edge_pos hb).le, sq_abs, edge_sq hb, pass, lt_div_iff₀ hpos,
    mul_pow, mul_comm]

/-- [proved-derived; formal-checked] **The band's edge:** `((b + 1)c)² = 4b ↔ |c| = edge b`. -/
theorem sq_eq_iff_abs_eq_edge {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ((b + 1) * c) ^ 2 = 4 * b ↔ |c| = edge b := by
  have hpos : (b + 1) ^ 2 ≠ (0 : ℝ) := by positivity
  rw [← sq_eq_sq₀ (abs_nonneg c) (edge_pos hb).le, sq_abs, edge_sq hb, pass, eq_div_iff hpos,
    mul_pow, mul_comm]

/-! ## B. The cell -/

/-- [proved-derived; formal-checked] The cell has determinant one. -/
theorem cell_det {b : ℝ} (hb : 0 < b) (φ : ℝ) : (cell b φ).det = 1 := by
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hcs := Real.cos_sq_add_sin_sq φ
  have e : Real.sqrt b * Real.cos φ * (Real.cos φ / Real.sqrt b) -
      -(Real.sqrt b * Real.sin φ) * (Real.sin φ / Real.sqrt b) =
      Real.cos φ ^ 2 + Real.sin φ ^ 2 := by
    field_simp
    ring
  rw [cell, Matrix.det_fin_two_of, e, hcs]

/-- [proved-derived; formal-checked] The cell's trace is `(b + 1)cos φ/√b`. -/
theorem cell_trace {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    (cell b φ).trace = (b + 1) * Real.cos φ / Real.sqrt b := by
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  rw [cell, Matrix.trace_fin_two_of, eq_div_iff hs, add_mul, div_mul_cancel₀ _ hs]
  linear_combination Real.cos φ * hsq

/-- [proved-derived; formal-checked] The cell's squared trace is the factor's squared trace over
its determinant face: `tr² = ((b + 1)cos φ)²/b`. -/
theorem cell_trace_sq {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    (cell b φ).trace ^ 2 = ((b + 1) * Real.cos φ) ^ 2 / b := by
  rw [cell_trace hb, div_pow, Real.sq_sqrt hb.le]

/-- [proved-derived; formal-checked] **The cell's trace is within two if and only if it is in the
band:** `tr² ≤ 4 ↔ |cos φ| ≤ edge b`. -/
theorem trace_sq_le_four_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    (cell b φ).trace ^ 2 ≤ 4 ↔ |Real.cos φ| ≤ edge b := by
  rw [cell_trace_sq hb, div_le_iff₀ hb, sq_le_iff_abs_le_edge hb]

/-- [proved-derived; formal-checked] **The cell is a rotation if and only if it is inside the
band.** -/
theorem cell_rotation_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    siteKind (cell b φ).trace (cell b φ).det = Kind.rotation ↔ |Real.cos φ| < edge b := by
  rw [siteKind_eq_rotation_iff, cell_det hb, cell_trace_sq hb, mul_one, div_lt_iff₀ hb,
    sq_lt_iff_abs_lt_edge hb]

/-- [proved-derived; formal-checked] **The cell is the null lock if and only if it is on the
band's edge.** -/
theorem cell_null_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    siteKind (cell b φ).trace (cell b φ).det = Kind.null ↔ |Real.cos φ| = edge b := by
  rw [siteKind_eq_null_iff, cell_det hb, cell_trace_sq hb, mul_one, div_eq_iff hb.ne',
    sq_eq_iff_abs_eq_edge hb]
  exact ⟨fun h => h.2, fun h => ⟨one_pos, h⟩⟩

/-- [proved-derived; formal-checked] **The cell is a boost if and only if it is outside the
band.** -/
theorem cell_boost_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    siteKind (cell b φ).trace (cell b φ).det = Kind.boost ↔ edge b < |Real.cos φ| := by
  have key : 4 * b < ((b + 1) * Real.cos φ) ^ 2 ↔ edge b < |Real.cos φ| := by
    rw [← not_le, ← not_le, sq_le_iff_abs_le_edge hb]
  rw [siteKind_eq_boost_iff, cell_det hb, cell_trace_sq hb, mul_one, lt_div_iff₀ hb, key]
  exact ⟨fun h => h.2, fun h => ⟨one_pos, h⟩⟩

/-- [counterexample; formal-checked] **A turnless cell at an unmatched junction is a boost:** at
`φ = 0` and `b ≠ 1` the cell lies outside its band, so the band is a proper condition. -/
theorem cell_zero_turn_boost {b : ℝ} (hb : 0 < b) (hb1 : b ≠ 1) :
    siteKind (cell b 0).trace (cell b 0).det = Kind.boost := by
  rw [cell_boost_iff hb, Real.cos_zero, abs_one]
  exact lt_of_le_of_ne (edge_le_one hb) (fun h => hb1 ((edge_eq_one_iff hb).mp h))

/-- [proved-derived; formal-checked] **The quarter-turn cell is a rotation at every ratio.** -/
theorem cell_quarter_turn_rotation {b : ℝ} (hb : 0 < b) :
    siteKind (cell b (Real.pi / 2)).trace (cell b (Real.pi / 2)).det = Kind.rotation := by
  rw [cell_rotation_iff hb, Real.cos_pi_div_two, abs_zero]
  exact edge_pos hb

/-! ## C. Scaled by the junction's half, the cell is a prime's factor -/

/-- [proved-derived; formal-checked] The cell scaled by `√b` has no square root in its entries. -/
theorem sqrt_smul_cell {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    Real.sqrt b • cell b φ =
      !![b * Real.cos φ, -(b * Real.sin φ); Real.sin φ, Real.cos φ] := by
  have hs : Real.sqrt b ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have e1 : Real.sqrt b * (Real.sqrt b * Real.cos φ) = b * Real.cos φ := by
    rw [← mul_assoc, hsq]
  have e2 : Real.sqrt b * (Real.sqrt b * Real.sin φ) = b * Real.sin φ := by
    rw [← mul_assoc, hsq]
  have e3 : Real.sqrt b * (Real.sin φ / Real.sqrt b) = Real.sin φ := mul_div_cancel₀ _ hs
  have e4 : Real.sqrt b * (Real.cos φ / Real.sqrt b) = Real.cos φ := mul_div_cancel₀ _ hs
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cell, e1, e2, e3, e4]

/-- [proved-derived; formal-checked] **The scaled cell's factor is `1 − aT + bT²` with
`a = (b + 1)cos φ`:** the local factor of a site with determinant face `b`. -/
theorem scaled_factor {b : ℝ} (hb : 0 < b) (φ T : ℝ) :
    (1 - T • (Real.sqrt b • cell b φ)).det =
      1 - (b + 1) * Real.cos φ * T + b * T ^ 2 := by
  have hcs := Real.cos_sq_add_sin_sq φ
  rw [sqrt_smul_cell hb, Matrix.det_fin_two]
  simp
  linear_combination (b * T ^ 2) * hcs

/-- [proved-derived; formal-checked] **The Hasse interval of the factor is the cell's band:**
`((b + 1)cos φ)² ≤ 4b ↔ |cos φ| ≤ edge b`. -/
theorem hasse_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    ((b + 1) * Real.cos φ) ^ 2 ≤ 4 * b ↔ |Real.cos φ| ≤ edge b :=
  sq_le_iff_abs_le_edge hb _

/-- [proved-derived; formal-checked] **The factor's site is a rotation if and only if it is
inside the band.** -/
theorem factor_rotation_iff {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    siteKind ((b + 1) * Real.cos φ) b = Kind.rotation ↔ |Real.cos φ| < edge b := by
  rw [siteKind_eq_rotation_iff, sq_lt_iff_abs_lt_edge hb]

/-- [proved-derived; formal-checked] **In the band every root of the factor's polynomial has
squared modulus `b`** (through `CarriedRate.root_normSq`): the Weil root's circle. -/
theorem weil_root_normSq {b : ℝ} (hb : 0 < b) {φ : ℝ} (h : |Real.cos φ| ≤ edge b) {z : ℂ}
    (hz : z * z - (((b + 1) * Real.cos φ : ℝ) : ℂ) * z + (b : ℂ) = 0) : Complex.normSq z = b :=
  Holonics.HNN.CarriedRate.root_normSq ((hasse_iff hb φ).mpr h) hz

/-! ## D. The tree with `b + 1` branches -/

/-- [definition] The radial mode of the tree with `b + 1` branches at turn `θ`:
`(e^{iθ}/√b)ⁿ`. -/
def radial (b θ : ℝ) (n : ℕ) : ℂ :=
  ((Real.sqrt b : ℂ)⁻¹ * Complex.exp (θ * Complex.I)) ^ n

/-- [proved-standard; formal-checked] **The radial mode solves the tree's radial recurrence**
`b·f(n+2) + f(n) = 2√b cos θ · f(n+1)`. -/
theorem radial_recurrence {b : ℝ} (hb : 0 < b) (θ : ℝ) (n : ℕ) :
    (b : ℂ) * radial b θ (n + 2) + radial b θ n =
      ((2 * Real.sqrt b * Real.cos θ : ℝ) : ℂ) * radial b θ (n + 1) := by
  have hs0 : (Real.sqrt b : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hb).ne'
  have hs2 : (Real.sqrt b : ℂ) ^ 2 = (b : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]
  have hinv : (Real.sqrt b : ℂ) * (Real.sqrt b : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hs0
  have hE : Complex.exp (θ * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hcos : ((2 * Real.sqrt b * Real.cos θ : ℝ) : ℂ) =
      (Real.sqrt b : ℂ) *
        (Complex.exp (θ * Complex.I) + Complex.exp (-(θ : ℂ) * Complex.I)) := by
    push_cast
    rw [Complex.cos]
    ring
  rw [hcos]
  simp only [radial, pow_succ]
  linear_combination
    (((Real.sqrt b : ℂ)⁻¹ * Complex.exp (θ * Complex.I)) ^ n) *
      ((-((Real.sqrt b : ℂ)⁻¹ ^ 2 * Complex.exp (θ * Complex.I) ^ 2)) * hs2 +
        ((Real.sqrt b : ℂ) * (Real.sqrt b : ℂ)⁻¹ * Complex.exp (θ * Complex.I) ^ 2 -
          Complex.exp (θ * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I)) * hinv - hE)

/-- [proved-standard; formal-checked] **The radial mode's power falls as `b⁻ⁿ`:**
`|f(n)|² bⁿ = 1`, the count of the `n`-th shell against the mode's power. -/
theorem radial_normSq {b : ℝ} (hb : 0 < b) (θ : ℝ) (n : ℕ) :
    Complex.normSq (radial b θ n) * b ^ n = 1 := by
  have hE : Complex.normSq (Complex.exp (θ * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hw : Complex.normSq ((Real.sqrt b : ℂ)⁻¹ * Complex.exp (θ * Complex.I)) = b⁻¹ := by
    rw [map_mul, hE, mul_one, map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt hb.le]
  rw [radial, map_pow, hw, ← mul_pow, inv_mul_cancel₀ hb.ne', one_pow]

/-- [proved-derived; formal-checked] **Kesten's radius is the band:** `(b + 1)cos φ` is
`2√b cos θ` for some real `θ` if and only if `|cos φ| ≤ edge b`. -/
theorem tree_band {b : ℝ} (hb : 0 < b) (φ : ℝ) :
    (∃ θ : ℝ, (b + 1) * Real.cos φ = 2 * Real.sqrt b * Real.cos θ) ↔
      |Real.cos φ| ≤ edge b := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  rw [← sq_le_iff_abs_le_edge hb]
  constructor
  · rintro ⟨θ, hθ⟩
    rw [hθ, mul_pow, mul_pow, hsq]
    nlinarith [Real.cos_sq_le_one θ]
  · intro h
    have h2 : (0 : ℝ) < 2 * Real.sqrt b := by positivity
    have habs : |(b + 1) * Real.cos φ| ≤ 2 * Real.sqrt b := by
      have h4 : (2 * Real.sqrt b) ^ 2 = 4 * b := by
        rw [mul_pow, hsq]
        norm_num
      apply abs_le_of_sq_le_sq _ h2.le
      rw [h4]
      exact h
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    refine ⟨Real.arccos ((b + 1) * Real.cos φ / (2 * Real.sqrt b)), ?_⟩
    rw [Real.cos_arccos, mul_div_cancel₀ _ h2.ne']
    · rw [le_div_iff₀ h2]
      linarith
    · rw [div_le_one h2]
      exact hhi

/-! ## E. The engine's junction return -/

/-- [proved-derived; formal-checked] **The junction return on a mode:** with `v = λx`, the return
`x' = v + Γ(v − x_prev)` is `(1 + Γ)λ·x − Γ·x_prev`, whose modes solve `z² − (1 + Γ)λz + Γ = 0`. -/
theorem return_mode (Γ lam xk xp : ℝ) :
    lam * xk + Γ * (lam * xk - xp) = (1 + Γ) * lam * xk - Γ * xp := by
  ring

/-- [proved-derived; formal-checked] **At `Γ = 1/b` the return is the tree's walk without
backtracking:** with `v` the pass's output and `xp` the state two ticks before,
`b·(v + b⁻¹(v − xp)) + xp = (b + 1)·v`, the recurrence `A·N_j = N_(j+1) + b·N_(j−1)` of
`Landmarks/TreeWalkFloor` in the walk's own normalization (`v` the walk's step `A/(b + 1)` applied
to the state). It is `RestitutionFamily.ownReturn_equal_ports` at `d = b + 1` ports, where
`Γ = 1/(d − 1)` leaves no own return, written as the tree's recurrence: for a tick that is a mean
of reciprocal partners the return removes what a place sent two ticks before, and `Γ` is the
reciprocal of the branching. On the engine's chart `Γ = (ρ − 1)/(ρ + 1)` that branching is
`(ρ + 1)/(ρ − 1)`, which is `3` at `ρ = 2`. -/
theorem return_tree {b : ℝ} (hb : b ≠ 0) (v xp : ℝ) :
    b * (v + b⁻¹ * (v - xp)) + xp = (b + 1) * v := by
  field_simp
  ring

/-- [proved-derived; formal-checked] **The return's pass band:** its discriminant is nonpositive
if and only if `|λ| ≤ edge Γ`. -/
theorem return_band {Γ : ℝ} (hΓ : 0 < Γ) (lam : ℝ) :
    ((1 + Γ) * lam) ^ 2 ≤ 4 * Γ ↔ |lam| ≤ edge Γ := by
  rw [add_comm 1 Γ]
  exact sq_le_iff_abs_le_edge hΓ lam

/-- [proved-derived; formal-checked] **In the band every mode of the return has squared modulus
`Γ`**: `RestitutionFamily.turning_root_normSq` with its discriminant read as `|λ| ≤ edge Γ`
(`return_band`); both rest on `CarriedRate.root_normSq`. -/
theorem return_root_normSq {Γ lam : ℝ} (hΓ : 0 < Γ) (h : |lam| ≤ edge Γ) {z : ℂ}
    (hz : z * z - (((1 + Γ) * lam : ℝ) : ℂ) * z + (Γ : ℂ) = 0) : Complex.normSq z = Γ :=
  Holonics.HNN.CarriedRate.root_normSq ((return_band hΓ lam).mpr h) hz

/-- [proved-derived; formal-checked] **A mode of the return turns if and only if it is inside the
band** (for `Γ > 0`): the site with trace face `(1 + Γ)λ` and determinant face `Γ` is a rotation
if and only if `|λ| < edge Γ`. -/
theorem return_rotation_iff {Γ : ℝ} (hΓ : 0 < Γ) (lam : ℝ) :
    siteKind ((1 + Γ) * lam) Γ = Kind.rotation ↔ |lam| < edge Γ := by
  rw [siteKind_eq_rotation_iff, add_comm 1 Γ, sq_lt_iff_abs_lt_edge hΓ]

/-- [proved-derived; formal-checked] **Below the matched load the return has no band:** for
`Γ < 0` the mode's site is a reflection at every `λ`, so `return_band` and `return_root_normSq`
read only the half `Γ > 0` of the return's chart. -/
theorem return_reflection_of_neg {Γ : ℝ} (hΓ : Γ < 0) (lam : ℝ) :
    siteKind ((1 + Γ) * lam) Γ = Kind.reflection :=
  (siteKind_eq_reflection_iff _ _).mpr hΓ

/-- [proved-derived; formal-checked] **On the engine's chart the reflection is positive if and
only if `ρ > 1`:** `0 < (ρ − 1)/(ρ + 1) ↔ 1 < ρ` for `ρ > 0`, that is `ℓ > 0` at `ρ = 2^ℓ`. -/
theorem chart_pos_iff {ρ : ℝ} (hρ : 0 < ρ) : 0 < (ρ - 1) / (ρ + 1) ↔ 1 < ρ := by
  rw [div_pos_iff_of_pos_right (add_pos hρ one_pos), sub_pos]

/-- [counterexample; formal-checked] **Outside the band a mode leaves the circle:** at `Γ = 1`
(edge `1`) and `λ = 5/4`, `z = 2` solves `z² − (1 + Γ)λz + Γ = 0` and `|z|² = 4 ≠ Γ`. The band
hypothesis of `return_root_normSq` and `weil_root_normSq` carries their conclusion. -/
theorem root_off_circle_outside_band :
    ¬ |(5 / 4 : ℝ)| ≤ edge 1 ∧
      (2 : ℂ) * 2 - (((1 + 1) * (5 / 4) : ℝ) : ℂ) * 2 + ((1 : ℝ) : ℂ) = 0 ∧
      Complex.normSq (2 : ℂ) ≠ 1 := by
  have he : edge 1 = 1 := (edge_eq_one_iff one_pos).mpr rfl
  have hn : Complex.normSq (2 : ℂ) = 4 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.normSq_ofReal]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [he, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 4)]
    norm_num
  · push_cast
    norm_num
  · rw [hn]
    norm_num

/-- [proved-derived; formal-checked] **The edge on the engine's chart:** at
`Γ = (ρ − 1)/(ρ + 1)` with `ρ > 1`, `edge Γ ² = 1 − ρ⁻²`. -/
theorem edge_chart {ρ : ℝ} (hρ : 1 < ρ) : edge ((ρ - 1) / (ρ + 1)) ^ 2 = 1 - (ρ⁻¹) ^ 2 := by
  have h1 : (0 : ℝ) < ρ - 1 := by linarith
  have h2 : (0 : ℝ) < ρ + 1 := by linarith
  have h0 : ρ ≠ 0 := by positivity
  have hΓ : 0 < (ρ - 1) / (ρ + 1) := div_pos h1 h2
  rw [edge_sq hΓ, pass]
  have h3 : (ρ - 1) / (ρ + 1) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- [proved-derived; formal-checked] **The return's band on the engine's chart:**
`|λ| ≤ edge Γ ↔ λ² ≤ 1 − ρ⁻²` at `Γ = (ρ − 1)/(ρ + 1)`, `ρ > 1`. -/
theorem return_band_chart {ρ : ℝ} (hρ : 1 < ρ) (lam : ℝ) :
    |lam| ≤ edge ((ρ - 1) / (ρ + 1)) ↔ lam ^ 2 ≤ 1 - (ρ⁻¹) ^ 2 := by
  have hΓ : 0 < (ρ - 1) / (ρ + 1) := div_pos (by linarith) (by linarith)
  rw [← edge_chart hρ, ← sq_le_sq₀ (abs_nonneg lam) (edge_pos hΓ).le, sq_abs]

/-! ## F. The delay carried at `b = 3` -/

/-- [proved-derived; formal-checked] **At `b = 3` the edge's delay is a sixth of a turn:**
`arcsin(edge 3) = π/3`. -/
theorem arcsin_edge_three : Real.arcsin (edge 3) = Real.pi / 3 := by
  have h : edge 3 = Real.sin (Real.pi / 3) := by
    rw [Real.sin_pi_div_three, edge]
    ring
  rw [h]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

end Holonics.Geometry.CellPassBand

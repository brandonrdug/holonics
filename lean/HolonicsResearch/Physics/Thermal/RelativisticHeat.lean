import Holonics.Physics.Thermal.Exchange
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.Real.Irrational

/-!
# A cell and a bath at real values, the finite-speed heat law, and its relativistic face

[definition] Source: the box of #410 "The relativistic heat law, and irrational heat into the bath (refused
today)". The box carries no more text, and its reading here is `agent-inferred`. Two owners name it.
`Physics/Spacetime`'s `[open]` paragraph owes "the relativistic (finite-speed) heat law of the thermal port".
`Physics/Thermal/Exchange` states the two-cell exchange, its first law and its production over `ℚ`, so a heat or a
temperature that is not rational is outside its statements, and it has no bath: "irrational heat into the bath" is
read as the exchange of a cell with a bath at a fixed temperature, for real heats and temperatures. The record
`2026-07-17_HEAT_IS_THE_INEXACT_BOUNDARY_CURRENT_TEMPERATURE_IS_THE_INTEGRATING_FRAME`, Card B (Eckart 1940;
Denicol et al. 2012), places relativistic heat flux in a material frame. Atlas rows: `heat.two-cell-exchange` (the
owner), `heat.telegraph-relaxation` (the finite-relaxation law with `D/τ ≤ c²`, stated in
`MASS_ENERGY_AND_CAUSAL_TRANSPORT.md` §7 with no Lean owner), `heat.second-law-receiver`,
`thermal.entropy-production`, and `lorentz.nonclosed-clock` (the static lapse `N`, here `e^Φ`). No atlas row names
Tolman–Ehrenfest or Cattaneo–Vernotte.

What is proved.

1. **A cell and a bath** (§1) [proved-derived; formal-checked]. A cell of capacity `C > 0` and energy `U > 0`, at
   temperature `T = U/C` (`temperature`), meets a bath at a fixed `T_b > 0` through a contact of conductance `κ ≥ 0`
   over a tick `h ≥ 0`. The heat `q = hκ(T − T_b)` leaves the cell into the bath (`bathHeat`), `U′ = U − q`
   (`cellNext`), and the tick's entropy is the cell's `C log(U′/U)` and the bath's `q/T_b` (`tickEntropy`).
   - The first law: the bath's energy gains what the cell loses (`first_law`).
   - The production `κ(T − T_b)(1/T_b − 1/T) = κ(T − T_b)²/(T T_b)` (`productionRate_eq`) is nonnegative
     (`productionRate_nonneg`) and zero only at `T = T_b` (`productionRate_eq_zero_iff`); in continuous time it is
     the rate of `C log U + Q/T_b` along the exchange, `Q` the heat the bath has received
     (`hasDerivAt_total_entropy`).
   - The tick's gap is `T′ − T_b = (1 − hκ/C)(T − T_b)` (`gap_after_tick`); under the tick condition `hκ/C ≤ 1`
     the cell's temperature does not cross the bath's, so `U′ > 0` (`cellNext_pos`). Through the owner's
     `cell_entropy_enclosure`, `q(1/T_b − 1/T′) ≤ ΔS ≤ q(1/T_b − 1/T)` (`tick_entropy_enclosure`); the lower
     reading is `hκ(T − T_b)²(1 − hκ/C)/(T_b T′)` (`lower_reading_eq`) and the upper is `h` times the production
     (`upper_reading_eq`). **Under the tick condition the tick's entropy is nonnegative**
     (`tick_entropy_nonneg`).
2. **The owner's rational statements are the `ℚ` face, and the bath is its second cell grown without bound**
   (§1) [proved-derived; formal-checked]. The owner's production rate is this one's on rational temperatures
   (`productionRate_ratCast`). With the owner's second cell at the bath's temperature, `U₂ = C₂ T_b`, the owner's
   heat and cell-1 update are this module's for every `C₂ ≠ 0` (`exchange_heat_at_bath`, `exchange_next₁_at_bath`);
   its temperature after the tick tends to `T_b` as `C₂ → ∞` (`tendsto_next₂_temperature`, over `ℚ`); its entropy
   change `C₂ log(U₂′/U₂)` tends to `q/T_b` (`tendsto_bath_entropy`), and the owner's two-cell entropy of the tick
   tends to this module's (`tendsto_exchange_entropy`). (The owner's gap factor `1 − hκ(1/C₁ + 1/C₂)` reaches
   `1 − hκ/C₁` in the same limit; that remark is not restated as a theorem.)
3. **The finite-speed heat law on modes** (§2) [proved-standard; formal-checked]. On a line, Cattaneo–Vernotte's
   `τ ∂ₜq + q = −κ ∂ₓT` with the balance `C ∂ₜT = −∂ₓq` (`Solves`, on `deriv`), read on the modes
   `A e^{ikx + st}` (`mode`; `hasDerivAt_mode_t`, `hasDerivAt_mode_x`), `k ≠ 0` real, `A ≠ 0`: some flux mode
   solves the system with the temperature mode exactly when `τ s² + s + D k² = 0`, `D = κ/C`
   (`solves_mode_iff`, `amplitudes_iff`, `mode_solves_iff`), which is the telegraph equation
   `τ ∂²ₜT + ∂ₜT = D ∂²ₓT` on the mode (`SolvesTelegraph`, `telegraph_mode_iff`).
   - For `τ > 0` and `4τDk² > 1` the roots are `s = −1/(2τ) ± iΩ` (`rootPlus`, `rootMinus`,
     `dispersion_factor`, `dispersion_eq_zero_iff`), `Ω² = Dk²/τ − 1/(4τ²)` (`angularFrequency`,
     `angularFrequency_sq`, `angularFrequency_pos`).
   - The phase speed `Ω/|k|` (`phaseSpeed`) is below `c_h = √(D/τ)` (`frontSpeed`, `phaseSpeed_lt_frontSpeed`) and
     tends to it as `|k| → ∞` (`tendsto_phaseSpeed_atTop`, `tendsto_phaseSpeed_cocompact`): the modes travel no
     faster than a finite speed.
     The rate per wavenumber `|s|/|k|` of either root is `c_h` (`norm_rootPlus`, `norm_rootMinus`).
   - Every root decays, `Re s < 0`, for any `τ ≥ 0` and `Dk² > 0` (`re_neg_of_dispersion_eq_zero`).
   - With `τ = 0` (Fourier's law) the one root is `s = −Dk²` (`fourier_root`), whose rate per wavenumber
     `|s|/|k| = D|k|` is unbounded in `k` (`fourier_rate_unbounded`). For `4τDk² ≤ 1` the slow root
     `−2Dk²/(1 + √(1 − 4τDk²))` (`slowRoot`, `slowRoot_isRoot`) is `−Dk²` at `τ = 0` (`slowRoot_zero`) and tends to
     it as `τ → 0⁺` (`tendsto_slowRoot`).
4. **The relativistic face** (§3) [proved-standard; formal-checked]. (a) Causality: `c_h ≤ c` iff `D ≤ τc²`
   (`frontSpeed_le_iff`), in the owner's chart `c = 1`, `D ≤ τ` (`frontSpeed_le_one_iff`); then every underdamped
   mode's phase speed is below `c` (`phaseSpeed_lt_of_causal`), while `c_h → ∞` as `τ → 0⁺`
   (`tendsto_frontSpeed`): Fourier's limit has no finite front. (b) Tolman–Ehrenfest from Eckart's law. In the
   static 1+1 chart `g_tt = −e^{2Φ(x)}`, `g_xx = 1`, the static observer `u^t = e^{−Φ}` is normalized and its
   acceleration `Γ^x_tt (u^t)² = −½ ∂ₓg_tt (u^t)²` is `Φ′` (`static_observer_acceleration`). Eckart's heat flux in
   the rest frame, `q = −κ(∂ₓT + T a)` (`eckartFlux`), is `−κ e^{−Φ} ∂ₓ(T e^Φ)` at `a = Φ′`
   (`hasDerivAt_redshifted`, `eckartFlux_mul_exp`), zero exactly when `∂ₓT = −T Φ′` (`eckartFlux_eq_zero_iff`).
   So no heat flows everywhere exactly when `T(x) = T(x₀) e^{Φ(x₀) − Φ(x)}`, that is `T e^Φ` constant
   (`tolman_ehrenfest`): at equilibrium a potential holds a temperature gradient `∂ₓT = −T Φ′ ≠ 0`
   (`equilibrium_gradient`), along which Fourier's law alone would carry heat. In a weak field `T(1 + Φ)` is
   constant to first order: `|T(1 + Φ) − T e^Φ| ≤ |T| Φ²` for `|Φ| ≤ 1` (`tolman_weak_field`), and its derivative
   at a point of no flux is `−T Φ Φ′` (`tolman_first_order`).
5. **Witnesses** (§4). A cell at `T = 3/2` against a bath at `1` with `hκ/C = 1/2` gives `q = 1/4`, `U′ = 5/4` and a
   tick's entropy of at least `1/20` (`witness_cell_three_halves`). A cell at `T = √2` gives the heat
   `(√2 − 1)/2`, irrational, so no rational heat of the owner equals it, and its tick's entropy is nonnegative
   (`witness_irrational_heat`). The Cattaneo mode `τ = 1`, `κ = 1/2`, `C = 1`, `k = 1` has the root
   `s = −1/2 + i/2`, a flux mode solving the system, phase speed `1/2 < c_h = √(1/2) ≤ 1`
   (`witness_cattaneo_mode`).

[counterexample; formal-checked] **The tick condition is load-bearing**: `C = 1`, `U = 2`, `T_b = 1`, `h = 1`,
`κ = 7/4` (`hκ/C = 7/4`) moves the cell to `U′ = 1/4`, across the bath (`T′ − T_b = −3/4`), and the tick's entropy
is `7/4 − 3 log 2 < 0` (`overshoot_destroys_entropy`).

What is not claimed. The Israel–Stewart second-order theory and the instability of Eckart's first-order theory
(Hiscock–Lindblom); the full relativistic fluid with viscosity; a bath of finite capacity with its own entropy curve
beyond the owner's two cells; the telegraph equation as a PDE with a solution theory (an initial-value problem, its
characteristics, the support of its solutions): only single modes are read, and the front speed `c_h` enters as the
high-wavenumber limit of their phase speeds, not as a proved bound on the support of a solution. Eckart's law is
taken as the constitutive law in the rest frame of a static fluid, and the acceleration is computed in the static
1+1 chart with `g_xx = 1`, not on a general metric or in three dimensions. A Fourier mode with real `k` has a real
`s` and does not travel, so the statement on Fourier's law is of its rate per wavenumber and of `c_h → ∞`, not of a
phase speed. The join to `Physics/Spacetime/StressEnergy` (whose `T⁰ⁱ` is the heat flux `q`) is named, not
imported.

The computational object is the helical pair interaction read on heat. The contact between the cell and the bath is
a pair contact whose slip is the temperature difference `T − T_b` and whose dissipation is its production; the
finite relaxation `τ` gives the contact's flux a store of its own, so that a mode's root `s` is a boost rate (the
decay `−1/(2τ)`) plus `i` times a turn rate (`Ω`), the swing's `v⁻¹v̇`; and in a static field the slip is read
after the frame transport `e^Φ`, the lapse, so that equilibrium is equal transported temperature. Of the winding
guide's six general objects this touches the pair (the contact, its slip and its relaxing flux), the tube (the tick
of the cell and the line that carries the modes) and faces and placement (temperature as the face a receiver reads
after the transport); the helix, the cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Thermal.RelativisticHeat

open Filter Topology

/-! ## 1. A cell and a bath at real values -/

/-- [definition] **The temperature** of a cell under the caloric law `U = C T`, over `ℝ`. -/
def temperature (C U : ℝ) : ℝ := U / C

/-- [definition] **The heat** `q = hκ(T − T_b)` that leaves the cell into the bath over a tick `h`. -/
def bathHeat (κ h C U Tb : ℝ) : ℝ := h * κ * (temperature C U - Tb)

/-- [definition] **The cell after the tick**, `U′ = U − q`. -/
def cellNext (κ h C U Tb : ℝ) : ℝ := U - bathHeat κ h C U Tb

/-- [definition] **The entropy of the tick**: the cell's `C log(U′/U)` and the bath's `q/T_b`. -/
def tickEntropy (κ h C U Tb : ℝ) : ℝ :=
  C * Real.log (cellNext κ h C U Tb / U) + bathHeat κ h C U Tb / Tb

/-- [definition] **The production rate of the contact** over `ℝ`: the heat current times the inverse-temperature drop.
-/
def productionRate (κ T Tb : ℝ) : ℝ := κ * (T - Tb) * (1 / Tb - 1 / T)

/-- [proved-derived; formal-checked] **The first law of the tick**: the bath's energy gains what the cell loses. -/
theorem first_law (κ h C U Tb Eb : ℝ) :
    (cellNext κ h C U Tb - U) + ((Eb + bathHeat κ h C U Tb) - Eb) = 0 := by
  unfold cellNext; ring

/-- [proved-derived; formal-checked] `κ(T − T_b)(1/T_b − 1/T) = κ(T − T_b)²/(T T_b)`. -/
theorem productionRate_eq {κ T Tb : ℝ} (hT : T ≠ 0) (hTb : Tb ≠ 0) :
    productionRate κ T Tb = κ * (T - Tb) ^ 2 / (T * Tb) := by
  unfold productionRate; field_simp

/-- [proved-derived; formal-checked] **The production rate is nonnegative.** -/
theorem productionRate_nonneg {κ T Tb : ℝ} (hκ : 0 ≤ κ) (hT : 0 < T) (hTb : 0 < Tb) :
    0 ≤ productionRate κ T Tb := by
  rw [productionRate_eq hT.ne' hTb.ne']; positivity

/-- [proved-derived; formal-checked] **The production rate vanishes only at `T = T_b`.** -/
theorem productionRate_eq_zero_iff {κ T Tb : ℝ} (hκ : 0 < κ) (hT : 0 < T) (hTb : 0 < Tb) :
    productionRate κ T Tb = 0 ↔ T = Tb := by
  rw [productionRate_eq hT.ne' hTb.ne', div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hκ.ne'
    · exact h
    · exact absurd h (mul_pos hT hTb).ne'
  · intro h; exact Or.inl (Or.inr h)

/-- [proved-derived; formal-checked] **The owner's rational production rate is this one** on rational temperatures. -/
theorem productionRate_ratCast (κ T₁ T₂ : ℚ) :
    ((Exchange.productionRate κ T₁ T₂ : ℚ) : ℝ) = productionRate κ T₁ T₂ := by
  unfold Exchange.productionRate productionRate; push_cast; ring

/-- [proved-derived; formal-checked] **The rate law**: along the exchange, `C log U + Q/T_b` rises at the production
rate. -/
theorem hasDerivAt_total_entropy (κ C Tb : ℝ) (U Q : ℝ → ℝ) (t : ℝ) (hC : C ≠ 0) (hU : 0 < U t)
    (h₁ : HasDerivAt U (-(κ * (U t / C - Tb))) t)
    (h₂ : HasDerivAt Q (κ * (U t / C - Tb)) t) :
    HasDerivAt (fun s => C * Real.log (U s) + Q s / Tb) (productionRate κ (U t / C) Tb) t := by
  have hA := (h₁.log hU.ne').const_mul C
  have hB := h₂.div_const Tb
  refine (hA.add hB).congr_deriv ?_
  unfold productionRate
  field_simp
  ring

/-- [proved-derived; formal-checked] **The tick's gap**: `T′ − T_b = (1 − hκ/C)(T − T_b)`. -/
theorem gap_after_tick {κ h C U Tb : ℝ} (hC : C ≠ 0) :
    temperature C (cellNext κ h C U Tb) - Tb = (1 - h * κ / C) * (temperature C U - Tb) := by
  unfold temperature cellNext bathHeat temperature
  field_simp
  ring

/-- [proved-derived; formal-checked] **Under the tick condition the cell's energy stays positive**: `T′` lies between
`T` and `T_b`. -/
theorem cellNext_pos {κ h C U Tb : ℝ} (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hC : 0 < C) (hU : 0 < U)
    (hTb : 0 < Tb) (htick : h * κ / C ≤ 1) : 0 < cellNext κ h C U Tb := by
  have ha : 0 ≤ h * κ / C := div_nonneg (mul_nonneg hh hκ) hC.le
  have hT : 0 < temperature C U := div_pos hU hC
  have hg := gap_after_tick (κ := κ) (h := h) (U := U) (Tb := Tb) hC.ne'
  have hT' : 0 < temperature C (cellNext κ h C U Tb) := by
    rcases le_total (temperature C U) Tb with hle | hle
    · nlinarith [mul_nonneg ha (sub_nonneg.2 hle)]
    · nlinarith [mul_nonneg (sub_nonneg.2 htick) (sub_nonneg.2 hle)]
  have : cellNext κ h C U Tb = C * temperature C (cellNext κ h C U Tb) := by
    unfold temperature; field_simp
  rw [this]; positivity

/-- [proved-derived; formal-checked] **The tick's entropy between two Clausius readings**:
`q(1/T_b − 1/T′) ≤ ΔS ≤ q(1/T_b − 1/T)`. -/
theorem tick_entropy_enclosure {κ h C U Tb : ℝ} (hC : 0 < C) (hU : 0 < U)
    (hU' : 0 < cellNext κ h C U Tb) :
    bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C (cellNext κ h C U Tb)) ≤
        tickEntropy κ h C U Tb ∧
      tickEntropy κ h C U Tb ≤ bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C U) := by
  obtain ⟨a, b⟩ := Exchange.cell_entropy_enclosure hC.le hU hU'
  have hq : cellNext κ h C U Tb - U = -bathHeat κ h C U Tb := by unfold cellNext; ring
  have e1 : C / cellNext κ h C U Tb = 1 / temperature C (cellNext κ h C U Tb) := by
    unfold temperature; rw [one_div_div]
  have e2 : C / U = 1 / temperature C U := by unfold temperature; rw [one_div_div]
  rw [hq, e1] at a
  rw [hq, e2] at b
  have l : bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C (cellNext κ h C U Tb)) =
      bathHeat κ h C U Tb / Tb + -bathHeat κ h C U Tb * (1 / temperature C (cellNext κ h C U Tb)) := by
    ring
  have u : bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C U) =
      bathHeat κ h C U Tb / Tb + -bathHeat κ h C U Tb * (1 / temperature C U) := by ring
  unfold tickEntropy
  rw [l, u]
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The lower reading**: `q(1/T_b − 1/T′) = hκ(T − T_b)²(1 − hκ/C)/(T_b T′)`. -/
theorem lower_reading_eq {κ h C U Tb : ℝ} (hC : C ≠ 0) (hTb : Tb ≠ 0)
    (hU' : cellNext κ h C U Tb ≠ 0) :
    bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C (cellNext κ h C U Tb)) =
      h * κ * (temperature C U - Tb) ^ 2 * (1 - h * κ / C) /
        (Tb * temperature C (cellNext κ h C U Tb)) := by
  have hg := gap_after_tick (κ := κ) (h := h) (U := U) (Tb := Tb) hC
  have hT' : temperature C (cellNext κ h C U Tb) ≠ 0 := div_ne_zero hU' hC
  have e : 1 / Tb - 1 / temperature C (cellNext κ h C U Tb) =
      (temperature C (cellNext κ h C U Tb) - Tb) / (Tb * temperature C (cellNext κ h C U Tb)) := by
    field_simp
  rw [e, hg]
  unfold bathHeat
  ring

/-- [proved-derived; formal-checked] **The upper reading** is the tick times the production rate. -/
theorem upper_reading_eq (κ h C U Tb : ℝ) :
    bathHeat κ h C U Tb * (1 / Tb - 1 / temperature C U) =
      h * productionRate κ (temperature C U) Tb := by
  unfold bathHeat productionRate; ring

/-- [proved-derived; formal-checked] **Under the tick condition `hκ/C ≤ 1` the tick's entropy is nonnegative.** -/
theorem tick_entropy_nonneg {κ h C U Tb : ℝ} (hκ : 0 ≤ κ) (hh : 0 ≤ h) (hC : 0 < C) (hU : 0 < U)
    (hTb : 0 < Tb) (htick : h * κ / C ≤ 1) : 0 ≤ tickEntropy κ h C U Tb := by
  have hU' := cellNext_pos hκ hh hC hU hTb htick
  have hlow := (tick_entropy_enclosure hC hU hU').1
  rw [lower_reading_eq hC.ne' hTb.ne' hU'.ne'] at hlow
  refine le_trans ?_ hlow
  have : 0 ≤ 1 - h * κ / C := by linarith
  have hT' : 0 < temperature C (cellNext κ h C U Tb) := div_pos hU' hC
  positivity

/-- [counterexample; formal-checked] **Past the tick condition** the cell crosses the bath and the tick's entropy is
`7/4 − 3 log 2 < 0`. -/
theorem overshoot_destroys_entropy :
    (1 : ℝ) * (7 / 4) / 1 = 7 / 4 ∧ cellNext (7 / 4) 1 1 2 1 = 1 / 4 ∧
      temperature 1 (cellNext (7 / 4) 1 1 2 1) - 1 = -(3 / 4) ∧
      tickEntropy (7 / 4) 1 1 2 1 = 7 / 4 - 3 * Real.log 2 ∧ tickEntropy (7 / 4) 1 1 2 1 < 0 := by
  have hn : cellNext (7 / 4) 1 1 2 1 = 1 / 4 := by norm_num [cellNext, bathHeat, temperature]
  have hS : tickEntropy (7 / 4) 1 1 2 1 = 7 / 4 - 3 * Real.log 2 := by
    unfold tickEntropy
    rw [hn]
    have hq : bathHeat (7 / 4) 1 1 2 1 = 7 / 4 := by norm_num [bathHeat, temperature]
    rw [hq, show (1 / 4 / 2 : ℝ) = ((2 : ℝ) ^ 3)⁻¹ by norm_num, Real.log_inv, Real.log_pow]
    push_cast; ring
  refine ⟨by norm_num, hn, by rw [hn]; norm_num [temperature], hS, ?_⟩
  rw [hS]
  have := Real.log_two_gt_d9
  norm_num at this ⊢
  linarith

/-! ### The bath as the owner's second cell of unbounded capacity -/

/-- [proved-derived; formal-checked] **The owner's heat with its second cell at `T_b`** is the bath's heat, for every
`C₂ ≠ 0`. -/
theorem exchange_heat_at_bath (κ h C₁ U₁ C₂ Tb : ℚ) (hC₂ : C₂ ≠ 0) :
    ((Exchange.heat κ h C₁ U₁ C₂ (C₂ * Tb) : ℚ) : ℝ) = bathHeat κ h C₁ U₁ Tb := by
  unfold Exchange.heat Exchange.temperature bathHeat temperature
  rw [show C₂ * Tb / C₂ = Tb by field_simp]
  push_cast; ring

/-- [proved-derived; formal-checked] **The owner's first cell after the tick** is the cell after the bath's tick. -/
theorem exchange_next₁_at_bath (κ h C₁ U₁ C₂ Tb : ℚ) (hC₂ : C₂ ≠ 0) :
    ((Exchange.next₁ κ h C₁ U₁ C₂ (C₂ * Tb) 0 : ℚ) : ℝ) = cellNext κ h C₁ U₁ Tb := by
  unfold Exchange.next₁ cellNext
  push_cast
  rw [exchange_heat_at_bath κ h C₁ U₁ C₂ Tb hC₂]
  ring

/-- [proved-derived; formal-checked] **The owner's second cell stays at `T_b` as `C₂ → ∞`**, over `ℚ`. -/
theorem tendsto_next₂_temperature (κ h C₁ U₁ Tb : ℚ) :
    Tendsto (fun C₂ : ℚ => Exchange.temperature C₂ (Exchange.next₂ κ h C₁ U₁ C₂ (C₂ * Tb) 0))
      atTop (𝓝 Tb) := by
  have hq : ∀ C₂ : ℚ, C₂ ≠ 0 →
      Exchange.temperature C₂ (Exchange.next₂ κ h C₁ U₁ C₂ (C₂ * Tb) 0) =
        Tb + h * κ * (U₁ / C₁ - Tb) / C₂ := by
    intro C₂ hC₂
    unfold Exchange.temperature Exchange.next₂ Exchange.heat Exchange.temperature
    rw [show C₂ * Tb / C₂ = Tb by field_simp]
    field_simp
    ring
  have hlim : Tendsto (fun C₂ : ℚ => Tb + h * κ * (U₁ / C₁ - Tb) / C₂) atTop (𝓝 (Tb + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with C₂ hC₂
  exact (hq C₂ hC₂.ne').symm

/-- [proved-derived; formal-checked] **The bath's `q/T_b` is the limit of `C₂ log(U₂′/U₂)`** with `U₂ = C₂ T_b`, as
`C₂ → ∞`. -/
theorem tendsto_bath_entropy {Tb : ℝ} (q : ℝ) (hTb : 0 < Tb) :
    Tendsto (fun C₂ : ℝ => C₂ * Real.log ((C₂ * Tb + q) / (C₂ * Tb))) atTop (𝓝 (q / Tb)) := by
  refine (Real.tendsto_mul_log_one_add_div_atTop (q / Tb)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with C₂ hC₂
  congr 2
  field_simp

/-- [proved-derived; formal-checked] **The owner's two-cell entropy of the tick tends to the bath's tick entropy.** -/
theorem tendsto_exchange_entropy {κ h C₁ U₁ Tb : ℝ} (hU₁ : 0 < U₁) (hTb : 0 < Tb)
    (hU₁' : 0 < cellNext κ h C₁ U₁ Tb) :
    Tendsto (fun C₂ : ℝ =>
        Exchange.entropy C₁ C₂ (cellNext κ h C₁ U₁ Tb) (C₂ * Tb + bathHeat κ h C₁ U₁ Tb) -
          Exchange.entropy C₁ C₂ U₁ (C₂ * Tb)) atTop (𝓝 (tickEntropy κ h C₁ U₁ Tb)) := by
  have hlim := (tendsto_bath_entropy (bathHeat κ h C₁ U₁ Tb) hTb).const_add
    (C₁ * Real.log (cellNext κ h C₁ U₁ Tb / U₁))
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (|bathHeat κ h C₁ U₁ Tb| / Tb)] with C₂ hC₂
  have hC₂pos : 0 < C₂ := lt_of_le_of_lt (div_nonneg (abs_nonneg _) hTb.le) hC₂
  have hpos : 0 < C₂ * Tb + bathHeat κ h C₁ U₁ Tb := by
    have := (div_lt_iff₀ hTb).1 hC₂
    linarith [neg_abs_le (bathHeat κ h C₁ U₁ Tb)]
  unfold Exchange.entropy
  rw [Real.log_div hU₁'.ne' hU₁.ne', Real.log_div hpos.ne' (mul_pos hC₂pos hTb).ne']
  ring

/-! ## 2. The finite-speed heat law on modes -/

/-- [definition] **A mode** on the line, `A e^{ikx + st}`, with `k` real and `s` complex. -/
def mode (A : ℂ) (k : ℝ) (s : ℂ) (x t : ℝ) : ℂ := A * Complex.exp (Complex.I * k * x + s * t)

/-- [proved-standard; formal-checked] `∂ₜ` of a mode is `s` times the mode. -/
theorem hasDerivAt_mode_t (A : ℂ) (k : ℝ) (s : ℂ) (x t : ℝ) :
    HasDerivAt (fun t' => mode A k s x t') (s * mode A k s x t) t := by
  have h1 : HasDerivAt (fun t' : ℝ => Complex.I * k * x + s * (t' : ℂ)) s t := by
    have := ((hasDerivAt_id t).ofReal_comp.const_mul s).const_add (Complex.I * k * x)
    simpa using this
  have h2 := h1.cexp.const_mul A
  unfold mode
  exact h2.congr_deriv (by ring)

/-- [proved-standard; formal-checked] `∂ₓ` of a mode is `ik` times the mode. -/
theorem hasDerivAt_mode_x (A : ℂ) (k : ℝ) (s : ℂ) (x t : ℝ) :
    HasDerivAt (fun x' => mode A k s x' t) (Complex.I * k * mode A k s x t) x := by
  have h1 : HasDerivAt (fun x' : ℝ => Complex.I * k * (x' : ℂ) + s * t) (Complex.I * k) x := by
    have := ((hasDerivAt_id x).ofReal_comp.const_mul (Complex.I * k)).add_const (s * (t : ℂ))
    simpa using this
  have h2 := h1.cexp.const_mul A
  unfold mode
  exact h2.congr_deriv (by ring)

/-- [proved-standard; formal-checked] The `deriv` form of `hasDerivAt_mode_t`. -/
theorem deriv_mode_t (A : ℂ) (k : ℝ) (s : ℂ) (x : ℝ) :
    deriv (fun t' => mode A k s x t') = fun t' => s * mode A k s x t' :=
  funext fun t => (hasDerivAt_mode_t A k s x t).deriv

/-- [proved-standard; formal-checked] The `deriv` form of `hasDerivAt_mode_x`. -/
theorem deriv_mode_x (A : ℂ) (k : ℝ) (s : ℂ) (t : ℝ) :
    deriv (fun x' => mode A k s x' t) = fun x' => Complex.I * k * mode A k s x' t :=
  funext fun x => (hasDerivAt_mode_x A k s x t).deriv

/-- [proved-standard; formal-checked] A multiple of a mode is the mode of the multiplied amplitude. -/
theorem mul_mode (c A : ℂ) (k : ℝ) (s : ℂ) (x t : ℝ) :
    c * mode A k s x t = mode (c * A) k s x t := by
  unfold mode; ring

/-- [definition] **The Cattaneo–Vernotte law with the energy balance**: `τ ∂ₜq + q = −κ ∂ₓT`, `C ∂ₜT = −∂ₓq`. -/
def Solves (τ κ C : ℝ) (T q : ℝ → ℝ → ℂ) : Prop :=
  ∀ x t, (τ : ℂ) * deriv (fun t' => q x t') t + q x t = -(κ : ℂ) * deriv (fun x' => T x' t) x ∧
    (C : ℂ) * deriv (fun t' => T x t') t = -deriv (fun x' => q x' t) x

/-- [proved-standard; formal-checked] **Two modes solve the law exactly when their amplitudes solve its algebraic
system.** -/
theorem solves_mode_iff (τ κ C k : ℝ) (s A B : ℂ) :
    Solves τ κ C (mode A k s) (mode B k s) ↔
      ((τ : ℂ) * s + 1) * B = -(κ : ℂ) * (Complex.I * k) * A ∧
        (C : ℂ) * s * A = -(Complex.I * k) * B := by
  unfold Solves
  simp only [deriv_mode_t, deriv_mode_x]
  have e1 : ∀ x t : ℝ, (τ : ℂ) * (s * mode B k s x t) + mode B k s x t =
      (((τ : ℂ) * s + 1) * B) * Complex.exp (Complex.I * k * x + s * t) := by
    intro x t; unfold mode; ring
  have e2 : ∀ x t : ℝ, -(κ : ℂ) * (Complex.I * k * mode A k s x t) =
      (-(κ : ℂ) * (Complex.I * k) * A) * Complex.exp (Complex.I * k * x + s * t) := by
    intro x t; unfold mode; ring
  have e3 : ∀ x t : ℝ, (C : ℂ) * (s * mode A k s x t) =
      ((C : ℂ) * s * A) * Complex.exp (Complex.I * k * x + s * t) := by
    intro x t; unfold mode; ring
  have e4 : ∀ x t : ℝ, -(Complex.I * k * mode B k s x t) =
      (-(Complex.I * k) * B) * Complex.exp (Complex.I * k * x + s * t) := by
    intro x t; unfold mode; ring
  simp only [e1, e2, e3, e4, mul_left_inj' (Complex.exp_ne_zero _), forall_const]

/-- [proved-standard; formal-checked] **The amplitude system has a flux solution exactly when
`τ s² + s + (κ/C)k² = 0`.** -/
theorem amplitudes_iff {τ κ C k : ℝ} (hk : k ≠ 0) (hC : C ≠ 0) {s A : ℂ} (hA : A ≠ 0) :
    (∃ B : ℂ, ((τ : ℂ) * s + 1) * B = -(κ : ℂ) * (Complex.I * k) * A ∧
        (C : ℂ) * s * A = -(Complex.I * k) * B) ↔
      (τ : ℂ) * s ^ 2 + s + (κ / C : ℝ) * (k : ℂ) ^ 2 = 0 := by
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hk
  have hC' : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hC
  push_cast
  constructor
  · rintro ⟨B, h1, h2⟩
    have h3 : (C : ℂ) * A * ((τ : ℂ) * s ^ 2 + s + κ / C * k ^ 2) = 0 := by
      have : (C : ℂ) * A * ((τ : ℂ) * s ^ 2 + s + κ / C * k ^ 2) =
          (C : ℂ) * A * s * ((τ : ℂ) * s + 1) + κ * k ^ 2 * A := by
        field_simp
      rw [this]
      linear_combination ((τ : ℂ) * s + 1) * h2 - (Complex.I * k) * h1 + (κ : ℂ) * k ^ 2 * A * Complex.I_sq
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd h (mul_ne_zero hC' hA)
    · exact h
  · intro h
    have e : (C : ℂ) * (κ / C * k ^ 2) = κ * k ^ 2 := by field_simp
    have h' : (C : ℂ) * τ * s ^ 2 + C * s + κ * k ^ 2 = 0 := by linear_combination (C : ℂ) * h - e
    have hkk : (k : ℂ) * (k : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hk'
    refine ⟨Complex.I * C * s * A / k, ?_, ?_⟩
    · linear_combination (Complex.I * A * (k : ℂ)⁻¹) * h' - ((κ : ℂ) * Complex.I * A * k) * hkk
    · linear_combination ((C : ℂ) * s * A) * Complex.I_sq + (Complex.I ^ 2 * C * s * A) * hkk

/-- [proved-standard; formal-checked] **The modes of the finite-speed law**: a temperature mode carries a flux mode
exactly at the dispersion relation `τ s² + s + (κ/C)k² = 0`. -/
theorem mode_solves_iff {τ κ C k : ℝ} (hk : k ≠ 0) (hC : C ≠ 0) {s A : ℂ} (hA : A ≠ 0) :
    (∃ B : ℂ, Solves τ κ C (mode A k s) (mode B k s)) ↔
      (τ : ℂ) * s ^ 2 + s + (κ / C : ℝ) * (k : ℂ) ^ 2 = 0 := by
  simp only [solves_mode_iff]
  exact amplitudes_iff hk hC hA

/-- [definition] **The telegraph equation** `τ ∂²ₜT + ∂ₜT = D ∂²ₓT`. -/
def SolvesTelegraph (τ D : ℝ) (T : ℝ → ℝ → ℂ) : Prop :=
  ∀ x t, (τ : ℂ) * deriv (fun t' => deriv (fun t'' => T x t'') t') t + deriv (fun t' => T x t') t =
    (D : ℂ) * deriv (fun x' => deriv (fun x'' => T x'' t) x') x

/-- [proved-standard; formal-checked] **The telegraph equation on a mode** is the same dispersion relation. -/
theorem telegraph_mode_iff (τ D k : ℝ) {s A : ℂ} (hA : A ≠ 0) :
    SolvesTelegraph τ D (mode A k s) ↔ (τ : ℂ) * s ^ 2 + s + (D : ℂ) * (k : ℂ) ^ 2 = 0 := by
  unfold SolvesTelegraph
  simp only [deriv_mode_t, deriv_mode_x, mul_mode]
  have e : ∀ x t : ℝ, mode ((τ : ℂ) * (s * (s * A))) k s x t + mode (s * A) k s x t -
      mode ((D : ℂ) * (Complex.I * k * (Complex.I * k * A))) k s x t =
      A * ((τ : ℂ) * s ^ 2 + s + (D : ℂ) * (k : ℂ) ^ 2) * Complex.exp (Complex.I * k * x + s * t) := by
    intro x t; unfold mode; linear_combination (-(D : ℂ) * k ^ 2 * A *
      Complex.exp (Complex.I * k * x + s * t)) * Complex.I_sq
  constructor
  · intro h
    have := e 0 0
    rw [h 0 0, sub_self] at this
    rcases mul_eq_zero.1 this.symm with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact absurd h2 hA
      · exact h2
    · exact absurd h1 (Complex.exp_ne_zero _)
  · intro h x t
    have := e x t
    rw [h, mul_zero, zero_mul] at this
    exact sub_eq_zero.1 this

/-! ### The roots -/

/-- [definition] **The dispersion polynomial** `τ s² + s + D k²`. -/
def dispersion (τ D k : ℝ) (s : ℂ) : ℂ := (τ : ℂ) * s ^ 2 + s + (D : ℂ) * (k : ℂ) ^ 2

/-- [definition] **The turn rate** `Ω = √(Dk²/τ − 1/(4τ²))` of an underdamped mode. -/
def angularFrequency (τ D k : ℝ) : ℝ := √(D * k ^ 2 / τ - 1 / (4 * τ ^ 2))

/-- [definition] **The root** `−1/(2τ) + iΩ`. -/
def rootPlus (τ D k : ℝ) : ℂ :=
  ((-(1 / (2 * τ)) : ℝ) : ℂ) + ((angularFrequency τ D k : ℝ) : ℂ) * Complex.I

/-- [definition] **The root** `−1/(2τ) − iΩ`. -/
def rootMinus (τ D k : ℝ) : ℂ :=
  ((-(1 / (2 * τ)) : ℝ) : ℂ) + ((-angularFrequency τ D k : ℝ) : ℂ) * Complex.I

/-- [proved-standard; formal-checked] Under `4τDk² > 1` the radicand `Dk²/τ − 1/(4τ²)` is positive. -/
theorem radicand_pos {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    0 < D * k ^ 2 / τ - 1 / (4 * τ ^ 2) := by
  have : D * k ^ 2 / τ - 1 / (4 * τ ^ 2) = (4 * τ * D * k ^ 2 - 1) / (4 * τ ^ 2) := by
    field_simp
  rw [this]
  exact div_pos (by linarith) (by positivity)

/-- [proved-standard; formal-checked] `Ω² = Dk²/τ − 1/(4τ²)`. -/
theorem angularFrequency_sq {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    angularFrequency τ D k ^ 2 = D * k ^ 2 / τ - 1 / (4 * τ ^ 2) :=
  Real.sq_sqrt (radicand_pos hτ hu).le

/-- [proved-standard; formal-checked] `Ω > 0`: an underdamped mode turns. -/
theorem angularFrequency_pos {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    0 < angularFrequency τ D k :=
  Real.sqrt_pos.2 (radicand_pos hτ hu)

/-- [proved-standard; formal-checked] **The dispersion polynomial factors** as `τ(s − s₊)(s − s₋)`. -/
theorem dispersion_factor {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) (s : ℂ) :
    dispersion τ D k s = (τ : ℂ) * (s - rootPlus τ D k) * (s - rootMinus τ D k) := by
  have hΩ : ((angularFrequency τ D k : ℝ) : ℂ) ^ 2 = (D : ℂ) * k ^ 2 / τ - 1 / (4 * τ ^ 2) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) (angularFrequency_sq hτ hu)
    push_cast at this
    exact this
  have hτinv : (τ : ℂ) * (τ : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.2 hτ.ne')
  unfold dispersion rootPlus rootMinus
  push_cast
  linear_combination ((τ : ℂ) * Complex.I ^ 2) * hΩ +
    ((τ : ℂ) * ((D : ℂ) * k ^ 2 / τ - 1 / (4 * τ ^ 2))) * Complex.I_sq - (s + (D : ℂ) * k ^ 2) * hτinv

/-- [proved-standard; formal-checked] **The roots are `−1/(2τ) ± iΩ`.** -/
theorem dispersion_eq_zero_iff {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) (s : ℂ) :
    dispersion τ D k s = 0 ↔ s = rootPlus τ D k ∨ s = rootMinus τ D k := by
  rw [dispersion_factor hτ hu, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hτ' : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hτ.ne'
  simp [hτ']

/-- [proved-standard; formal-checked] **Every mode decays**: `Re s < 0` for `τ ≥ 0` and `Dk² > 0`. -/
theorem re_neg_of_dispersion_eq_zero {τ D k : ℝ} (hτ : 0 ≤ τ) (hDk : 0 < D * k ^ 2) {s : ℂ}
    (h : dispersion τ D k s = 0) : s.re < 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [dispersion, sq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  by_contra hcon
  push Not at hcon
  have hb : s.im = 0 := by
    have : s.im * (2 * τ * s.re + 1) = 0 := by linear_combination him
    rcases mul_eq_zero.1 this with h1 | h1
    · exact h1
    · nlinarith
  rw [hb] at hre
  nlinarith [mul_nonneg hτ (mul_nonneg hcon hcon)]

/-- [definition] **The front speed** `c_h = √(D/τ)`. -/
def frontSpeed (τ D : ℝ) : ℝ := √(D / τ)

/-- [definition] **The phase speed** `Ω/|k|` of an underdamped mode. -/
def phaseSpeed (τ D k : ℝ) : ℝ := angularFrequency τ D k / |k|

/-- [proved-standard; formal-checked] `√(Dk²/τ)/|k| = c_h`. -/
theorem sqrt_div_abs {τ D k : ℝ} (hk : k ≠ 0) : √(D * k ^ 2 / τ) / |k| = frontSpeed τ D := by
  unfold frontSpeed
  rw [show D * k ^ 2 / τ = D / τ * k ^ 2 by ring, Real.sqrt_mul' _ (sq_nonneg k),
    Real.sqrt_sq_eq_abs, mul_div_assoc, div_self (abs_ne_zero.2 hk), mul_one]

/-- [proved-standard; formal-checked] **The phase speed is below the front speed**: `Ω/|k| < √(D/τ)`. -/
theorem phaseSpeed_lt_frontSpeed {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    phaseSpeed τ D k < frontSpeed τ D := by
  have hk : k ≠ 0 := by rintro rfl; norm_num at hu
  have hpos : 0 < D * k ^ 2 / τ := by
    have := radicand_pos hτ hu
    have : 0 < 1 / (4 * τ ^ 2) := by positivity
    linarith
  rw [← sqrt_div_abs (τ := τ) (D := D) hk]
  unfold phaseSpeed angularFrequency
  apply div_lt_div_of_pos_right _ (abs_pos.2 hk)
  rw [Real.sqrt_lt_sqrt_iff_of_pos hpos]
  have : 0 < 1 / (4 * τ ^ 2) := by positivity
  linarith

/-- [proved-standard; formal-checked] **The rate per wavenumber `|s₊|/|k|` is the front speed.** -/
theorem norm_rootPlus {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    ‖rootPlus τ D k‖ / |k| = frontSpeed τ D := by
  have hk : k ≠ 0 := by rintro rfl; norm_num at hu
  unfold rootPlus
  rw [Complex.norm_add_mul_I, angularFrequency_sq hτ hu, ← sqrt_div_abs hk]
  congr 2
  field_simp
  ring

/-- [proved-standard; formal-checked] **The rate per wavenumber `|s₋|/|k|` is the front speed.** -/
theorem norm_rootMinus {τ D k : ℝ} (hτ : 0 < τ) (hu : 1 < 4 * τ * D * k ^ 2) :
    ‖rootMinus τ D k‖ / |k| = frontSpeed τ D := by
  have hk : k ≠ 0 := by rintro rfl; norm_num at hu
  unfold rootMinus
  rw [Complex.norm_add_mul_I, neg_sq (angularFrequency τ D k), angularFrequency_sq hτ hu,
    ← sqrt_div_abs hk]
  congr 2
  field_simp
  ring

/-- [proved-standard; formal-checked] `Ω/|k| = √(D/τ − 1/(4τ²k²))`. -/
theorem phaseSpeed_eq_sqrt {τ D k : ℝ} (hk : k ≠ 0) :
    phaseSpeed τ D k = √(D / τ - 1 / (4 * τ ^ 2) * (k ^ 2)⁻¹) := by
  unfold phaseSpeed angularFrequency
  rw [← Real.sqrt_sq_eq_abs k, ← Real.sqrt_div' _ (sq_nonneg k)]
  congr 1
  field_simp

/-- [proved-standard; formal-checked] **The phase speed tends to `c_h` as `k → ∞`.** -/
theorem tendsto_phaseSpeed_atTop (τ D : ℝ) :
    Tendsto (phaseSpeed τ D) atTop (𝓝 (frontSpeed τ D)) := by
  have h0 : Tendsto (fun k : ℝ => (k ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop two_ne_zero)
  have hlim := ((tendsto_const_nhds (x := D / τ)).sub
    ((tendsto_const_nhds (x := 1 / (4 * τ ^ 2))).mul h0)).sqrt
  rw [mul_zero, sub_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  exact (phaseSpeed_eq_sqrt hk.ne').symm

/-- [proved-standard; formal-checked] The phase speed is even in `k`. -/
theorem phaseSpeed_neg (τ D k : ℝ) : phaseSpeed τ D (-k) = phaseSpeed τ D k := by
  simp [phaseSpeed, angularFrequency, abs_neg]

/-- [proved-standard; formal-checked] **The phase speed tends to `c_h` as `|k| → ∞`.** -/
theorem tendsto_phaseSpeed_cocompact (τ D : ℝ) :
    Tendsto (phaseSpeed τ D) (cocompact ℝ) (𝓝 (frontSpeed τ D)) := by
  rw [cocompact_eq_atBot_atTop]
  refine Tendsto.sup ?_ (tendsto_phaseSpeed_atTop τ D)
  have := (tendsto_phaseSpeed_atTop τ D).comp tendsto_neg_atBot_atTop
  refine this.congr fun k => ?_
  simp [Function.comp, phaseSpeed_neg]

/-! ### Fourier's law and the slow root -/

/-- [proved-standard; formal-checked] **Fourier's law (`τ = 0`) has the one root `s = −Dk²`.** -/
theorem fourier_root (D k : ℝ) (s : ℂ) : dispersion 0 D k s = 0 ↔ s = -((D : ℂ) * (k : ℂ) ^ 2) := by
  unfold dispersion
  push_cast
  rw [zero_mul, zero_add]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

/-- [proved-standard; formal-checked] **Fourier's rate per wavenumber `|s|/|k| = D|k|` is unbounded.** -/
theorem fourier_rate_unbounded {D : ℝ} (hD : 0 < D) :
    Tendsto (fun k : ℝ => |-(D * k ^ 2)| / |k|) atTop atTop := by
  refine (tendsto_id.const_mul_atTop hD).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  rw [abs_neg, abs_of_pos (by positivity), abs_of_pos hk]
  field_simp
  simp

/-- [definition] **The slow root** `−2Dk²/(1 + √(1 − 4τDk²))` of an overdamped mode. -/
def slowRoot (τ D k : ℝ) : ℝ := -(2 * D * k ^ 2) / (1 + √(1 - 4 * τ * D * k ^ 2))

/-- [proved-standard; formal-checked] **The slow root solves the dispersion relation** for `4τDk² ≤ 1`. -/
theorem slowRoot_isRoot {τ D k : ℝ} (ho : 4 * τ * D * k ^ 2 ≤ 1) :
    τ * slowRoot τ D k ^ 2 + slowRoot τ D k + D * k ^ 2 = 0 := by
  have hr := Real.sq_sqrt (show 0 ≤ 1 - 4 * τ * D * k ^ 2 by linarith)
  have hpos : 0 < 1 + √(1 - 4 * τ * D * k ^ 2) := by positivity
  have hs : slowRoot τ D k * (1 + √(1 - 4 * τ * D * k ^ 2)) = -(2 * D * k ^ 2) :=
    div_mul_cancel₀ _ hpos.ne'
  have hp : (1 + √(1 - 4 * τ * D * k ^ 2)) ^ 2 * (τ * slowRoot τ D k ^ 2 + slowRoot τ D k + D * k ^ 2) = 0 := by
    linear_combination (τ * (slowRoot τ D k * (1 + √(1 - 4 * τ * D * k ^ 2)) - 2 * D * k ^ 2) +
      (1 + √(1 - 4 * τ * D * k ^ 2))) * hs + (D * k ^ 2) * hr
  exact (mul_eq_zero.1 hp).resolve_left (pow_ne_zero 2 hpos.ne')

/-- [proved-standard; formal-checked] At `τ = 0` the slow root is Fourier's `−Dk²`. -/
theorem slowRoot_zero (D k : ℝ) : slowRoot 0 D k = -(D * k ^ 2) := by
  unfold slowRoot
  norm_num
  ring

/-- [proved-standard; formal-checked] **The slow root tends to `−Dk²` as `τ → 0⁺`.** -/
theorem tendsto_slowRoot (D k : ℝ) :
    Tendsto (fun τ => slowRoot τ D k) (𝓝[>] 0) (𝓝 (-(D * k ^ 2))) := by
  have hc : Continuous fun τ : ℝ => slowRoot τ D k := by
    unfold slowRoot
    refine Continuous.div continuous_const (by fun_prop) (fun τ => ?_)
    positivity
  rw [← slowRoot_zero D k]
  exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-! ## 3. The relativistic face -/

/-- [proved-standard; formal-checked] **Causality**: `c_h ≤ c` iff `D ≤ τc²`. -/
theorem frontSpeed_le_iff {τ D c : ℝ} (hτ : 0 < τ) (hc : 0 ≤ c) :
    frontSpeed τ D ≤ c ↔ D ≤ τ * c ^ 2 := by
  unfold frontSpeed
  rw [Real.sqrt_le_left hc, div_le_iff₀ hτ, mul_comm]

/-- [proved-standard; formal-checked] In the owner's chart, `c = 1`: `c_h ≤ 1` iff `D ≤ τ`. -/
theorem frontSpeed_le_one_iff {τ D : ℝ} (hτ : 0 < τ) : frontSpeed τ D ≤ 1 ↔ D ≤ τ := by
  rw [frontSpeed_le_iff hτ zero_le_one, one_pow, mul_one]

/-- [proved-standard; formal-checked] **A causal law's underdamped modes travel below `c`.** -/
theorem phaseSpeed_lt_of_causal {τ D k c : ℝ} (hτ : 0 < τ) (hc : 0 ≤ c)
    (hu : 1 < 4 * τ * D * k ^ 2) (hcausal : D ≤ τ * c ^ 2) : phaseSpeed τ D k < c :=
  lt_of_lt_of_le (phaseSpeed_lt_frontSpeed hτ hu) ((frontSpeed_le_iff hτ hc).2 hcausal)

/-- [proved-standard; formal-checked] **`c_h → ∞` as `τ → 0⁺`**: Fourier's limit has no finite front. -/
theorem tendsto_frontSpeed {D : ℝ} (hD : 0 < D) :
    Tendsto (fun τ => frontSpeed τ D) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun τ : ℝ => D / τ) (𝓝[>] 0) atTop := by
    simpa [div_eq_mul_inv] using (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hD
  exact Real.tendsto_sqrt_atTop.comp h

/-! ### Tolman–Ehrenfest from Eckart's law -/

/-- [proved-standard; formal-checked] **The static observer of `g_tt = −e^{2Φ}`** is normalized and accelerates at
`Φ′`. -/
theorem static_observer_acceleration {Φ : ℝ → ℝ} {Φ' x : ℝ} (hΦ : HasDerivAt Φ Φ' x) :
    HasDerivAt (fun y => -Real.exp (2 * Φ y)) (-(2 * Φ' * Real.exp (2 * Φ x))) x ∧
      -Real.exp (2 * Φ x) * Real.exp (-Φ x) ^ 2 = -1 ∧
      -(1 / 2) * (-(2 * Φ' * Real.exp (2 * Φ x))) * Real.exp (-Φ x) ^ 2 = Φ' := by
  have he : Real.exp (2 * Φ x) * Real.exp (-Φ x) ^ 2 = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  refine ⟨((hΦ.const_mul 2).exp).neg.congr_deriv (by ring), by linear_combination -he,
    by linear_combination Φ' * he⟩

/-- [definition] **Eckart's heat flux** of a static fluid on a line, in its rest frame: `q = −κ(∂ₓT + T a)`. -/
def eckartFlux (κ T dT a : ℝ) : ℝ := -κ * (dT + T * a)

/-- [proved-standard; formal-checked] `∂ₓ(T e^Φ) = (∂ₓT + T ∂ₓΦ) e^Φ`. -/
theorem hasDerivAt_redshifted {T Φ : ℝ → ℝ} {T' Φ' x : ℝ} (hT : HasDerivAt T T' x)
    (hΦ : HasDerivAt Φ Φ' x) :
    HasDerivAt (fun y => T y * Real.exp (Φ y)) ((T' + T x * Φ') * Real.exp (Φ x)) x := by
  exact (hT.mul hΦ.exp).congr_deriv (by ring)

/-- [proved-standard; formal-checked] **Eckart's flux is `−κ e^{−Φ} ∂ₓ(T e^Φ)`**: `q e^Φ = −κ (∂ₓT + T a) e^Φ`. -/
theorem eckartFlux_mul_exp (κ T dT a Φ : ℝ) :
    eckartFlux κ T dT a * Real.exp Φ = -κ * ((dT + T * a) * Real.exp Φ) := by
  unfold eckartFlux; ring

/-- [proved-standard; formal-checked] **No Eckart flux exactly when `∂ₓT = −T a`.** -/
theorem eckartFlux_eq_zero_iff {κ T dT a : ℝ} (hκ : κ ≠ 0) :
    eckartFlux κ T dT a = 0 ↔ dT = -(T * a) := by
  unfold eckartFlux
  rw [mul_eq_zero, neg_eq_zero, or_iff_right hκ]
  constructor <;> intro h <;> linarith

/-- [proved-standard; formal-checked] **Tolman–Ehrenfest**: no heat flows anywhere iff `T(x) = T(x₀) e^{Φ(x₀) −
Φ(x)}`. -/
theorem tolman_ehrenfest {κ : ℝ} (hκ : κ ≠ 0) {T Φ T' Φ' : ℝ → ℝ}
    (hT : ∀ x, HasDerivAt T (T' x) x) (hΦ : ∀ x, HasDerivAt Φ (Φ' x) x) :
    (∀ x, eckartFlux κ (T x) (T' x) (Φ' x) = 0) ↔
      ∀ x x₀, T x = T x₀ * Real.exp (Φ x₀ - Φ x) := by
  constructor
  · intro h x x₀
    have hd : ∀ y, HasDerivAt (fun y => T y * Real.exp (Φ y)) 0 y := by
      intro y
      have := hasDerivAt_redshifted (hT y) (hΦ y)
      have h0 : T' y + T y * Φ' y = 0 := by
        have := (eckartFlux_eq_zero_iff hκ).1 (h y); linarith
      rwa [h0, zero_mul] at this
    have hconst := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt)
      (fun y => (hd y).deriv) x x₀
    rw [Real.exp_sub, mul_div_assoc', eq_div_iff (Real.exp_pos _).ne']
    exact hconst
  · intro h x
    have hder : HasDerivAt (fun y => T x * Real.exp (Φ x - Φ y)) (-(T x * Φ' x)) x := by
      exact (((hasDerivAt_const x (Φ x)).sub (hΦ x)).exp.const_mul (T x)).congr_deriv (by simp)
    have hT' : T' x = -(T x * Φ' x) :=
      (hT x).unique (hder.congr_of_eventuallyEq (Eventually.of_forall fun y => h y x))
    exact (eckartFlux_eq_zero_iff hκ).2 hT'

/-- [proved-standard; formal-checked] **A potential holds a temperature gradient at equilibrium**: `∂ₓT = −T a ≠ 0`. -/
theorem equilibrium_gradient {κ T dT a : ℝ} (hκ : κ ≠ 0) (h0 : eckartFlux κ T dT a = 0)
    (hT : T ≠ 0) (ha : a ≠ 0) : dT = -(T * a) ∧ dT ≠ 0 := by
  have h := (eckartFlux_eq_zero_iff hκ).1 h0
  refine ⟨h, ?_⟩
  rw [h, neg_ne_zero]
  exact mul_ne_zero hT ha

/-- [proved-standard; formal-checked] **Weak field**: at `T e^Φ = K`, `|T(1 + Φ) − K| ≤ |T| Φ²` for `|Φ| ≤ 1`. -/
theorem tolman_weak_field {T Φ : ℝ → ℝ} {K : ℝ} (hK : ∀ x, T x * Real.exp (Φ x) = K) (x : ℝ)
    (hΦ : |Φ x| ≤ 1) : |T x * (1 + Φ x) - K| ≤ |T x| * Φ x ^ 2 := by
  rw [← hK x, show T x * (1 + Φ x) - T x * Real.exp (Φ x) =
    -(T x * (Real.exp (Φ x) - 1 - Φ x)) by ring, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_sub_id_le hΦ) (abs_nonneg _)

/-- [proved-standard; formal-checked] **At no flux, `∂ₓ(T(1 + Φ)) = −T Φ Φ′`**, of second order in the potential. -/
theorem tolman_first_order {κ : ℝ} (hκ : κ ≠ 0) {T Φ : ℝ → ℝ} {T' Φ' x : ℝ}
    (hT : HasDerivAt T T' x) (hΦ : HasDerivAt Φ Φ' x) (h0 : eckartFlux κ (T x) T' Φ' = 0) :
    HasDerivAt (fun y => T y * (1 + Φ y)) (-(T x * Φ x * Φ')) x := by
  have h := (eckartFlux_eq_zero_iff hκ).1 h0
  exact (hT.mul (hΦ.const_add 1)).congr_deriv (by rw [h]; ring)

/-! ## 4. Witnesses -/

/-- [proved-derived; formal-checked] **Witness**: a cell at `3/2`, a bath at `1`, `hκ/C = 1/2`; the tick's entropy is
at least `1/20`. -/
theorem witness_cell_three_halves :
    bathHeat (1 / 2) 1 1 (3 / 2) 1 = 1 / 4 ∧ cellNext (1 / 2) 1 1 (3 / 2) 1 = 5 / 4 ∧
      (1 : ℝ) * (1 / 2) / 1 ≤ 1 ∧ 1 / 20 ≤ tickEntropy (1 / 2) 1 1 (3 / 2) 1 := by
  have hq : bathHeat (1 / 2) 1 1 (3 / 2) 1 = 1 / 4 := by norm_num [bathHeat, temperature]
  have hn : cellNext (1 / 2) 1 1 (3 / 2) 1 = 5 / 4 := by norm_num [cellNext, hq]
  refine ⟨hq, hn, by norm_num, ?_⟩
  have hlow := (tick_entropy_enclosure (κ := 1 / 2) (h := 1) (C := 1) (U := 3 / 2) (Tb := 1)
    one_pos (by norm_num) (by rw [hn]; norm_num)).1
  rw [hq, hn] at hlow
  norm_num [temperature] at hlow
  linarith

/-- [proved-derived; formal-checked] **Irrational heat into the bath**: a cell at `√2` sends `(√2 − 1)/2`, no owner's
heat, with `ΔS ≥ 0`. -/
theorem witness_irrational_heat :
    Irrational (bathHeat (1 / 2) 1 1 √2 1) ∧
      (∀ κ h C₁ U₁ C₂ U₂ : ℚ, ((Exchange.heat κ h C₁ U₁ C₂ U₂ : ℚ) : ℝ) ≠ bathHeat (1 / 2) 1 1 √2 1) ∧
      0 ≤ tickEntropy (1 / 2) 1 1 √2 1 := by
  have hirr : Irrational (bathHeat (1 / 2) 1 1 √2 1) := by
    have h := (irrational_sqrt_two.sub_natCast 1).div_natCast (m := 2) two_ne_zero
    have e : bathHeat (1 / 2) 1 1 √2 1 = (√2 - ((1 : ℕ) : ℝ)) / ((2 : ℕ) : ℝ) := by
      simp [bathHeat, temperature]; ring
    rw [e]; exact h
  refine ⟨hirr, fun κ h C₁ U₁ C₂ U₂ => (hirr.ne_rat _).symm, ?_⟩
  exact tick_entropy_nonneg (by norm_num) zero_le_one one_pos (Real.sqrt_pos.2 two_pos) one_pos
    (by norm_num)

/-- [proved-standard; formal-checked] **Witness**: `τ = 1`, `D = 1/2`, `k = 1`, root `−1/2 + i/2`, phase speed `1/2 <
√(1/2) ≤ 1`. -/
theorem witness_cattaneo_mode :
    (1 : ℝ) < 4 * 1 * (1 / 2) * 1 ^ 2 ∧ angularFrequency 1 (1 / 2) 1 = 1 / 2 ∧
      rootPlus 1 (1 / 2) 1 = -(1 / 2) + (1 / 2) * Complex.I ∧
      dispersion 1 (1 / 2) 1 (-(1 / 2) + (1 / 2) * Complex.I) = 0 ∧
      (∃ B : ℂ, Solves 1 (1 / 2) 1 (mode 1 1 (-(1 / 2) + (1 / 2) * Complex.I))
        (mode B 1 (-(1 / 2) + (1 / 2) * Complex.I))) ∧
      phaseSpeed 1 (1 / 2) 1 = 1 / 2 ∧ phaseSpeed 1 (1 / 2) 1 < frontSpeed 1 (1 / 2) ∧
      frontSpeed 1 (1 / 2) ≤ 1 := by
  have hΩ : angularFrequency 1 (1 / 2) 1 = 1 / 2 := by
    unfold angularFrequency
    rw [show (1 / 2 * 1 ^ 2 / 1 - 1 / (4 * 1 ^ 2) : ℝ) = (1 / 2) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hd : dispersion 1 (1 / 2) 1 (-(1 / 2) + (1 / 2) * Complex.I) = 0 := by
    unfold dispersion
    push_cast
    linear_combination (1 / 4 : ℂ) * Complex.I_sq
  refine ⟨by norm_num, hΩ, ?_, hd, ?_, ?_, phaseSpeed_lt_frontSpeed one_pos (by norm_num),
    (frontSpeed_le_one_iff one_pos).2 (by norm_num)⟩
  · unfold rootPlus; rw [hΩ]; push_cast; ring
  · refine (mode_solves_iff one_ne_zero one_ne_zero one_ne_zero).2 ?_
    have := hd
    unfold dispersion at this
    push_cast at this ⊢
    linear_combination this
  · unfold phaseSpeed; rw [hΩ]; norm_num

end Holonics.Physics.Thermal.RelativisticHeat

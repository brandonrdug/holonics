import Holonics.Physics.TwoCellEntropyTransport

/-!
# Two thermal cells: the first law, and entropy production of certified sign

[definition] Rebuild step 6, K3 (#74), battle test 5; plan §3.6, acceptance case (2). Two cells
store internal energy `U₁, U₂` with heat capacities `C₁, C₂ > 0` under the caloric law
`U = C T` (`temperature`). A contact of conductance `κ ≥ 0` carries the heat `q = h κ (T₁ − T₂)`
from cell 1 to cell 2 over a tick `h` (`heat`, Fourier's law), and each cell may also receive the
work of an external port (`W₁`, `W₂`: the viscous work of `Physics/Thermal/ViscousPort`). The cell
entropy is `S = C log U` (up to a constant fixed by the unit chart). This supplies what
`Physics/TwoCellEntropyTransport` states it does not: a caloric law, a temperature and physical
heat. With equal capacities its flux is exactly that owner's flux on the energies
(`heat_eq_twoCell_flux`), and its energy conservation is that owner's mass conservation
(`energy_conserved_of_equal_capacity`); the entropy differs (`C log U` reads energy through the
caloric law, `−a log a` reads a mass).

[proved-derived; formal-checked] What is proved.

1. **First law, by construction of the update** (`first_law`, exact over `ℚ`): the tick moves the
   heat `q` out of one cell and into the other (`next₁`, `next₂`), so the stored energy changes by
   exactly the port work, `ΔU₁ + ΔU₂ = h (W₁ + W₂)`. This is bookkeeping of the update, not a
   derived conservation law.
2. **The production rate is an exact rational of certified sign.** The Clausius production of the
   contact, heat current times the inverse-temperature drop, is
   `κ (T₁ − T₂)(1/T₂ − 1/T₁) = κ (T₁ − T₂)²/(T₁ T₂)` (`productionRate_eq`), nonnegative
   (`productionRate_nonneg`) and zero exactly at equal temperatures (`productionRate_eq_zero_iff`).
   In continuous time it is the derivative of `C₁ log U₁ + C₂ log U₂` along the exchange, with the
   port productions `W₁/T₁ + W₂/T₂` added (`hasDerivAt_entropy`).
3. **The finite tick is enclosed by two exact Clausius readings.** For one cell,
   `ΔU · C/U' ≤ C log(U'/U) ≤ ΔU · C/U` (`cell_entropy_enclosure`); for the exchange,
   `q (1/T₂' − 1/T₁') ≤ ΔS ≤ q (1/T₂ − 1/T₁)` (`exchange_entropy_enclosure`). The temperature
   gap after the tick is the gap before times `1 − hκ(1/C₁ + 1/C₂)` (`gap_after_tick`), so the lower
   reading is `hκ (T₁ − T₂)² (1 − hκ(1/C₁ + 1/C₂))/(T₁' T₂')` (`lower_reading_eq`), and **under the
   tick condition `hκ(1/C₁ + 1/C₂) ≤ 1` the entropy of the tick is nonnegative**
   (`exchange_entropy_nonneg`). The logarithm enters only as the enclosed value; both bounds are
   rational.

[counterexample; formal-checked] **The tick condition is load-bearing**: with `C₁ = C₂ = 1`,
`U₁ = 3`, `U₂ = 1` and `hκ = 5/4` (`hκ(1/C₁ + 1/C₂) = 5/2`) the explicit tick overshoots to
`U₁' = 1/2`, `U₂' = 7/2`, and the entropy of the tick is `log(7/12) < 0`
(`overshoot_destroys_entropy`).

No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Thermal.Exchange

/-! ## 1. The first law and the exact production rate -/

/-- [definition] **The temperature** of a cell under the caloric law `U = C T`. -/
def temperature (C U : ℚ) : ℚ := U / C

/-- [definition] **The heat** carried from cell 1 to cell 2 over one tick (Fourier's law). -/
def heat (κ h C₁ U₁ C₂ U₂ : ℚ) : ℚ := h * κ * (temperature C₁ U₁ - temperature C₂ U₂)

/-- [definition] Cell 1 after one tick, with the work `W₁` of its external port. -/
def next₁ (κ h C₁ U₁ C₂ U₂ W₁ : ℚ) : ℚ := U₁ - heat κ h C₁ U₁ C₂ U₂ + h * W₁

/-- [definition] Cell 2 after one tick, with the work `W₂` of its external port. -/
def next₂ (κ h C₁ U₁ C₂ U₂ W₂ : ℚ) : ℚ := U₂ + heat κ h C₁ U₁ C₂ U₂ + h * W₂

/-- [proved-derived; formal-checked] **The first law of the tick, by construction of the
update**: `next₁` and `next₂` move the same heat out of one cell and into the other, so the stored
energy changes by exactly the port work. -/
theorem first_law (κ h C₁ U₁ C₂ U₂ W₁ W₂ : ℚ) :
    (next₁ κ h C₁ U₁ C₂ U₂ W₁ - U₁) + (next₂ κ h C₁ U₁ C₂ U₂ W₂ - U₂) = h * (W₁ + W₂) := by
  unfold next₁ next₂; ring

/-- [definition] **The production rate of the contact**: the heat current times the drop of
inverse temperature. -/
def productionRate (κ T₁ T₂ : ℚ) : ℚ := κ * (T₁ - T₂) * (1 / T₂ - 1 / T₁)

/-- [proved-derived; formal-checked] `κ (T₁ − T₂)(1/T₂ − 1/T₁) = κ (T₁ − T₂)²/(T₁ T₂)`. -/
theorem productionRate_eq {κ T₁ T₂ : ℚ} (h₁ : T₁ ≠ 0) (h₂ : T₂ ≠ 0) :
    productionRate κ T₁ T₂ = κ * (T₁ - T₂) ^ 2 / (T₁ * T₂) := by
  unfold productionRate; field_simp

/-- [proved-derived; formal-checked] **The production rate is nonnegative.** -/
theorem productionRate_nonneg {κ T₁ T₂ : ℚ} (hκ : 0 ≤ κ) (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    0 ≤ productionRate κ T₁ T₂ := by
  rw [productionRate_eq h₁.ne' h₂.ne']; positivity

/-- [proved-derived; formal-checked] **The production rate vanishes exactly at equal
temperatures.** -/
theorem productionRate_eq_zero_iff {κ T₁ T₂ : ℚ} (hκ : 0 < κ) (h₁ : 0 < T₁) (h₂ : 0 < T₂) :
    productionRate κ T₁ T₂ = 0 ↔ T₁ = T₂ := by
  rw [productionRate_eq h₁.ne' h₂.ne', div_eq_zero_iff, mul_eq_zero, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]
  constructor
  · rintro ((h | h) | h)
    · exact absurd h hκ.ne'
    · exact h
    · exact absurd h (mul_pos h₁ h₂).ne'
  · intro h; exact Or.inl (Or.inr h)

/-- [proved-derived; formal-checked] **With equal capacities the heat is the two-cell flux** of
`Physics/TwoCellEntropyTransport` on the energies, at conductance `κ/C`. -/
theorem heat_eq_twoCell_flux (κ h C U₁ U₂ : ℚ) (hC : C ≠ 0) :
    ((heat κ h C U₁ C U₂ : ℚ) : ℝ) =
      h * TwoCellEntropyTransport.flux ((κ / C : ℚ) : ℝ) (U₁ : ℝ) (U₂ : ℝ) := by
  unfold heat temperature TwoCellEntropyTransport.flux
  push_cast
  field_simp

/-! ## 2. The rate law in continuous time -/

/-- [definition] The heat current of the contact in the real chart. -/
noncomputable def heatCurrent (κ C₁ C₂ U₁ U₂ : ℝ) : ℝ := κ * (U₁ / C₁ - U₂ / C₂)

/-- [definition] **The entropy of the two cells**, `C₁ log U₁ + C₂ log U₂`. -/
noncomputable def entropy (C₁ C₂ U₁ U₂ : ℝ) : ℝ := C₁ * Real.log U₁ + C₂ * Real.log U₂

/-- [proved-derived; formal-checked] **The rate law**: along the exchange with port works, the
entropy changes at the contact's production rate plus the ports' `W/T`. -/
theorem hasDerivAt_entropy (κ C₁ C₂ W₁ W₂ : ℝ) (U₁ U₂ : ℝ → ℝ) (t : ℝ)
    (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0) (hU₁ : 0 < U₁ t) (hU₂ : 0 < U₂ t)
    (h₁ : HasDerivAt U₁ (-heatCurrent κ C₁ C₂ (U₁ t) (U₂ t) + W₁) t)
    (h₂ : HasDerivAt U₂ (heatCurrent κ C₁ C₂ (U₁ t) (U₂ t) + W₂) t) :
    HasDerivAt (fun s => entropy C₁ C₂ (U₁ s) (U₂ s))
      (κ * (U₁ t / C₁ - U₂ t / C₂) * (1 / (U₂ t / C₂) - 1 / (U₁ t / C₁)) +
        W₁ / (U₁ t / C₁) + W₂ / (U₂ t / C₂)) t := by
  have hA := (h₁.log hU₁.ne').const_mul C₁
  have hB := (h₂.log hU₂.ne').const_mul C₂
  have h := hA.add hB
  refine h.congr_deriv ?_
  unfold heatCurrent
  field_simp
  ring

/-- [proved-derived; formal-checked] **With equal capacities, energy is conserved** without port
work: this is `TwoCellEntropyTransport.hasDerivAt_mass_conservation` on the energies. -/
theorem energy_conserved_of_equal_capacity (κ C : ℝ) (U₁ U₂ : ℝ → ℝ) (t : ℝ) (hC : C ≠ 0)
    (h₁ : HasDerivAt U₁ (-heatCurrent κ C C (U₁ t) (U₂ t)) t)
    (h₂ : HasDerivAt U₂ (heatCurrent κ C C (U₁ t) (U₂ t)) t) :
    HasDerivAt (fun s => U₁ s + U₂ s) 0 t := by
  have hflux : heatCurrent κ C C (U₁ t) (U₂ t) =
      TwoCellEntropyTransport.flux (κ / C) (U₁ t) (U₂ t) := by
    unfold heatCurrent TwoCellEntropyTransport.flux; field_simp
  rw [hflux] at h₁ h₂
  exact TwoCellEntropyTransport.hasDerivAt_mass_conservation (κ / C) U₁ U₂ t h₁ h₂

/-! ## 3. The finite tick: the Clausius enclosure -/

/-- [proved-derived; formal-checked] **One cell's entropy over a tick is enclosed by two exact
Clausius readings**: `ΔU · C/U' ≤ C log(U'/U) ≤ ΔU · C/U`. -/
theorem cell_entropy_enclosure {C U U' : ℝ} (hC : 0 ≤ C) (hU : 0 < U) (hU' : 0 < U') :
    (U' - U) * (C / U') ≤ C * Real.log (U' / U) ∧ C * Real.log (U' / U) ≤ (U' - U) * (C / U) := by
  have hx : 0 < U' / U := div_pos hU' hU
  constructor
  · have := Real.one_sub_inv_le_log_of_pos hx
    rw [inv_div] at this
    have heq : (U' - U) * (C / U') = C * (1 - U / U') := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left this hC
  · have := Real.log_le_sub_one_of_pos hx
    have heq : (U' - U) * (C / U) = C * (U' / U - 1) := by field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left this hC

/-- [proved-derived; formal-checked] **The exchange's entropy over a tick** lies between the
Clausius readings at the end and at the start of the tick:
`q (C₂/U₂' − C₁/U₁') ≤ ΔS ≤ q (C₂/U₂ − C₁/U₁)`. -/
theorem exchange_entropy_enclosure {C₁ C₂ U₁ U₂ q : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hU₁ : 0 < U₁) (hU₂ : 0 < U₂) (hU₁' : 0 < U₁ - q) (hU₂' : 0 < U₂ + q) :
    q * (C₂ / (U₂ + q) - C₁ / (U₁ - q)) ≤
        entropy C₁ C₂ (U₁ - q) (U₂ + q) - entropy C₁ C₂ U₁ U₂ ∧
      entropy C₁ C₂ (U₁ - q) (U₂ + q) - entropy C₁ C₂ U₁ U₂ ≤ q * (C₂ / U₂ - C₁ / U₁) := by
  obtain ⟨a₁, b₁⟩ := cell_entropy_enclosure hC₁ hU₁ hU₁'
  obtain ⟨a₂, b₂⟩ := cell_entropy_enclosure hC₂ hU₂ hU₂'
  have hd : entropy C₁ C₂ (U₁ - q) (U₂ + q) - entropy C₁ C₂ U₁ U₂ =
      C₁ * Real.log ((U₁ - q) / U₁) + C₂ * Real.log ((U₂ + q) / U₂) := by
    unfold entropy
    rw [Real.log_div hU₁'.ne' hU₁.ne', Real.log_div hU₂'.ne' hU₂.ne']
    ring
  rw [hd]
  constructor
  · have e1 : (U₁ - q - U₁) * (C₁ / (U₁ - q)) = -q * (C₁ / (U₁ - q)) := by ring
    have e2 : (U₂ + q - U₂) * (C₂ / (U₂ + q)) = q * (C₂ / (U₂ + q)) := by ring
    rw [e1] at a₁; rw [e2] at a₂
    linarith
  · have e1 : (U₁ - q - U₁) * (C₁ / U₁) = -q * (C₁ / U₁) := by ring
    have e2 : (U₂ + q - U₂) * (C₂ / U₂) = q * (C₂ / U₂) := by ring
    rw [e1] at b₁; rw [e2] at b₂
    linarith

/-- [proved-derived; formal-checked] **The temperature gap after the tick** is the gap before times
`1 − hκ(1/C₁ + 1/C₂)`. -/
theorem gap_after_tick {κ h C₁ U₁ C₂ U₂ : ℚ} (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0) :
    temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) - temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0) =
      (temperature C₁ U₁ - temperature C₂ U₂) * (1 - h * κ * (1 / C₁ + 1 / C₂)) := by
  unfold temperature next₁ next₂ heat temperature
  field_simp
  ring

/-- [proved-derived; formal-checked] **The lower Clausius reading of the tick, exactly**:
`q (1/T₂' − 1/T₁') = hκ (T₁ − T₂)² (1 − hκ(1/C₁ + 1/C₂)) / (T₁' T₂')`. -/
theorem lower_reading_eq {κ h C₁ U₁ C₂ U₂ : ℚ} (hC₁ : C₁ ≠ 0) (hC₂ : C₂ ≠ 0)
    (h₁ : next₁ κ h C₁ U₁ C₂ U₂ 0 ≠ 0) (h₂ : next₂ κ h C₁ U₁ C₂ U₂ 0 ≠ 0) :
    heat κ h C₁ U₁ C₂ U₂ *
        (C₂ / next₂ κ h C₁ U₁ C₂ U₂ 0 - C₁ / next₁ κ h C₁ U₁ C₂ U₂ 0) =
      h * κ * (temperature C₁ U₁ - temperature C₂ U₂) ^ 2 *
          (1 - h * κ * (1 / C₁ + 1 / C₂)) /
        (temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) * temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0)) := by
  have hg := gap_after_tick (κ := κ) (h := h) (U₁ := U₁) (U₂ := U₂) hC₁ hC₂
  have hT₁ : temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) ≠ 0 := div_ne_zero h₁ hC₁
  have hT₂ : temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0) ≠ 0 := div_ne_zero h₂ hC₂
  have e : C₂ / next₂ κ h C₁ U₁ C₂ U₂ 0 - C₁ / next₁ κ h C₁ U₁ C₂ U₂ 0 =
      (temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) - temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0)) /
        (temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) * temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0)) := by
    unfold temperature; field_simp
  rw [e, hg]
  unfold heat
  ring

/-- [proved-derived; formal-checked] **Under the tick condition the entropy of the tick is
nonnegative**: `hκ(1/C₁ + 1/C₂) ≤ 1`, positive capacities and energies before and after. -/
theorem exchange_entropy_nonneg {κ h C₁ U₁ C₂ U₂ : ℚ} (hκ : 0 ≤ κ) (hh : 0 ≤ h)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hU₁ : 0 < U₁) (hU₂ : 0 < U₂)
    (h₁ : 0 < next₁ κ h C₁ U₁ C₂ U₂ 0) (h₂ : 0 < next₂ κ h C₁ U₁ C₂ U₂ 0)
    (htick : h * κ * (1 / C₁ + 1 / C₂) ≤ 1) :
    0 ≤ entropy C₁ C₂ (next₁ κ h C₁ U₁ C₂ U₂ 0) (next₂ κ h C₁ U₁ C₂ U₂ 0) -
      entropy C₁ C₂ U₁ U₂ := by
  have hq₁ : ((next₁ κ h C₁ U₁ C₂ U₂ 0 : ℚ) : ℝ) = U₁ - heat κ h C₁ U₁ C₂ U₂ := by
    unfold next₁; push_cast; ring
  have hq₂ : ((next₂ κ h C₁ U₁ C₂ U₂ 0 : ℚ) : ℝ) = U₂ + heat κ h C₁ U₁ C₂ U₂ := by
    unfold next₂; push_cast; ring
  have hlow := lower_reading_eq (κ := κ) (h := h) (U₁ := U₁) (U₂ := U₂) hC₁.ne' hC₂.ne'
    h₁.ne' h₂.ne'
  have hnn : 0 ≤ h * κ * (temperature C₁ U₁ - temperature C₂ U₂) ^ 2 *
      (1 - h * κ * (1 / C₁ + 1 / C₂)) /
        (temperature C₁ (next₁ κ h C₁ U₁ C₂ U₂ 0) * temperature C₂ (next₂ κ h C₁ U₁ C₂ U₂ 0)) := by
    have : 0 ≤ 1 - h * κ * (1 / C₁ + 1 / C₂) := by linarith
    unfold temperature
    have := div_pos h₁ hC₁
    have := div_pos h₂ hC₂
    positivity
  rw [← hlow] at hnn
  have enc := (exchange_entropy_enclosure (C₁ := C₁) (C₂ := C₂) (U₁ := U₁) (U₂ := U₂)
    (q := heat κ h C₁ U₁ C₂ U₂) (by exact_mod_cast hC₁.le) (by exact_mod_cast hC₂.le)
    (by exact_mod_cast hU₁) (by exact_mod_cast hU₂) (by rw [← hq₁]; exact_mod_cast h₁)
    (by rw [← hq₂]; exact_mod_cast h₂)).1
  rw [← hq₁, ← hq₂] at enc
  have hcast : ((heat κ h C₁ U₁ C₂ U₂ *
      (C₂ / next₂ κ h C₁ U₁ C₂ U₂ 0 - C₁ / next₁ κ h C₁ U₁ C₂ U₂ 0) : ℚ) : ℝ) =
      (heat κ h C₁ U₁ C₂ U₂ : ℝ) * ((C₂ : ℝ) / (next₂ κ h C₁ U₁ C₂ U₂ 0 : ℝ) -
        (C₁ : ℝ) / (next₁ κ h C₁ U₁ C₂ U₂ 0 : ℝ)) := by push_cast; ring
  have : (0 : ℝ) ≤ ((heat κ h C₁ U₁ C₂ U₂ *
      (C₂ / next₂ κ h C₁ U₁ C₂ U₂ 0 - C₁ / next₁ κ h C₁ U₁ C₂ U₂ 0) : ℚ) : ℝ) := by
    exact_mod_cast hnn
  rw [hcast] at this
  linarith

/-- [counterexample; formal-checked] **An overshooting tick destroys entropy.** With `C₁ = C₂ = 1`,
`U₁ = 3`, `U₂ = 1`, `h = 1`, `κ = 5/4` the tick condition fails (`hκ(1/C₁ + 1/C₂) = 5/2`), the
cells reach `1/2` and `7/2`, and the entropy of the tick is `log(7/12) < 0`. -/
theorem overshoot_destroys_entropy :
    (1 : ℚ) * (5 / 4) * (1 / 1 + 1 / 1) = 5 / 2 ∧
      next₁ (5 / 4) 1 1 3 1 1 0 = 1 / 2 ∧ next₂ (5 / 4) 1 1 3 1 1 0 = 7 / 2 ∧
      entropy 1 1 (1 / 2) (7 / 2) - entropy 1 1 3 1 = Real.log (7 / 12) ∧
      Real.log (7 / 12) < 0 := by
  refine ⟨by norm_num, by norm_num [next₁, heat, temperature],
    by norm_num [next₂, heat, temperature], ?_, Real.log_neg (by norm_num) (by norm_num)⟩
  have e : Real.log (7 / 12) = Real.log (1 / 2) + Real.log (7 / 2) - Real.log 3 := by
    rw [show (7 / 12 : ℝ) = (1 / 2) * (7 / 2) / 3 by norm_num,
      Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  unfold entropy
  rw [e, Real.log_one]
  ring

section Audit

#print axioms first_law
#print axioms productionRate_eq_zero_iff
#print axioms hasDerivAt_entropy
#print axioms energy_conserved_of_equal_capacity
#print axioms exchange_entropy_enclosure
#print axioms exchange_entropy_nonneg
#print axioms overshoot_destroys_entropy

end Audit

end Holonics.Physics.Thermal.Exchange

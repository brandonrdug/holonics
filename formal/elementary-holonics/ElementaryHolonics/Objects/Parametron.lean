import ElementaryHolonics.Physics.PhaseCarrier
import ElementaryHolonics.Physics.CoupledIncidence
import ElementaryHolonics.Millennium.HolonicMeasuredParametron
import ElementaryHolonics.Millennium.HolonicClockedPantographicSwing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The parametron object: storage↔flow exchange, the tick as a clock, the perceptron as a face

[definition] Object 5 of `docs/ELEMENTARY_OBJECTS.md`. The complex parametron is the ring whose
owners are `Physics/PhaseCarrier` (carrier `e^{iθ}`, pump, half-turn sheets, Ising lock),
`Physics/CoupledIncidence` (oriented incidence, diagonal storage, generalized modes
`K v = ω² C v`), `Millennium/HolonicMeasuredParametron` (measured coefficients) and
`Millennium/HolonicClockedPantographicSwing` (section crossings and rational clock passages).
This module joins them; it founds no second energy, mode or clock.

1. **Storage↔flow exchange.** [proved-derived; formal-checked] For `q(t) = A cos(ωt + φ)`,
   `i = q'` and `ω² L C = 1`, the sum `½q²/C + ½Li²` is the constant `A²/(2C)`
   (`lc_energy_conserved`); neither term is constant unless `A = 0`
   (`lc_storage_constant_iff`, `lc_flow_constant_iff`), and the ring's measured angular frequency
   is `ω` (`lc_measuredAngularFrequency`). Along a generalized mode `x(t) = cos(ωt) v`,
   `½⟨x', C x'⟩ + ½⟨x, K x⟩ = ω² · ½⟨v, C v⟩` (`modeEnergy_conserved`), using the mode relation
   through `Σ v · (B^T W B v) = 2 · diagonalStorage`.
2. **Tick as clock.** [proved-derived; formal-checked] A ring stepping by `1/d` of a turn is a
   `SectionedOscillator` whose section is phase `0`. For `d ≥ 2` a micro-step is an owner
   `Crossing` exactly when it lands on the section (`ringCrossing_iff`). Along the orbit of
   `n·k` micro-steps from residue `r < d` (one source tick is `n` micro-steps), the number of
   owner `Crossing` records equals the owner's `targetTicks r k = (r + n k)/d`
   (`ownerCrossings_eq_targetTicks`, `d ≥ 2`; at `d = 1` there are no crossings,
   `no_crossing_of_denominator_one`), and the carrier at the end is the carrier of the owner's
   `phaseResidue` (`ringPhase_eq_residuePhase`); the owner's reconstruction theorem joins them.
3. **Perceptron as the locked-sheet face.** [proved-derived; formal-checked] With the input drive
   represented as coupling to a reference carrier at phase `0` (`phaseCoupling (h i) θᵢ 0`), the
   driven phase energy on locked sheets is the driven Ising energy
   (`drivenPhaseEnergy_binaryPhase`). With no self-loops, the energy of site `i` on sheet `s` is
   `rest − σ(s)·(Σ_j w_ij σ_j + h_i)` (`drivenIsing_update`), so the minimizing sheet is the
   threshold `sign(Σ_j w_ij σ_j + h_i)`, strictly when the field is nonzero
   (`thresholdSheet_minimizes`, `thresholdSheet_strict`). Separation: two unlocked
   configurations with the same local field and threshold output (drive included) but different
   driven phase energy and quadrature (`perceptron_is_a_face`).
4. **Half-turn.** [proved-derived; formal-checked] Composing `pumpStorage_halfTurnSheet`: a global
   half-turn preserves every coupling energy (locked or not), every pump storage, and every Ising
   pairing energy under `σ ↦ ¬σ`, while negating every carrier (`globalHalfTurn_composite`); the
   drive is what breaks the symmetry (`drive_breaks_halfTurn`).

[open] Pump/Floquet locking dynamics (that the pump actually selects the two sheets as attracting
basins) is not proved; the locked sheets are taken as given. The oscillator here is the exact
ring micro-step; the continuous section crossing of `A cos(ωt + φ)` is not identified with it by
a theorem. No damping or hardware law is asserted.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Soma.Holonics.Objects.Parametron

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Millennium.HolonicParametron
open Soma.Holonics.Millennium.HolonicComplexParametron

/-! ## 1. Storage and flow exchange -/

section Exchange

/-- [definition] The charge of a single LC mode. -/
def lcCharge (A ω φ t : ℝ) : ℝ := A * Real.cos (ω * t + φ)

/-- [definition] Its current `i = q'`. -/
def lcCurrent (A ω φ t : ℝ) : ℝ := -(A * ω * Real.sin (ω * t + φ))

/-- [definition] Capacitive storage `½ q²/C`. -/
def capacitiveStorage (C q : ℝ) : ℝ := q ^ 2 / (2 * C)

/-- [definition] Inductive flow energy `½ L i²`. -/
def inductiveFlow (L i : ℝ) : ℝ := L * i ^ 2 / 2

/-- [proved-derived; formal-checked] The current is the derivative of the charge. -/
theorem hasDerivAt_lcCharge (A ω φ t : ℝ) :
    HasDerivAt (lcCharge A ω φ) (lcCurrent A ω φ t) t := by
  have h : HasDerivAt (fun s => ω * s + φ) ω t := by
    simpa using ((hasDerivAt_id t).const_mul ω).add_const φ
  have hc := (h.cos).const_mul A
  refine hc.congr_deriv ?_
  simp [lcCurrent]; ring

/-- [proved-derived; formal-checked] **The LC energy is conserved.** With `ω² L C = 1`, storage
plus flow is `A²/(2C)` at every time. -/
theorem lc_energy_conserved {A ω φ L C : ℝ} (hC : 0 < C) (hω : ω ^ 2 * (L * C) = 1) (t : ℝ) :
    capacitiveStorage C (lcCharge A ω φ t) + inductiveFlow L (lcCurrent A ω φ t) =
      A ^ 2 / (2 * C) := by
  have hLω : L * ω ^ 2 = 1 / C := by
    field_simp; linarith
  have htrig := Real.cos_sq_add_sin_sq (ω * t + φ)
  simp only [capacitiveStorage, inductiveFlow, lcCharge, lcCurrent]
  have : L * (-(A * ω * Real.sin (ω * t + φ))) ^ 2 / 2 =
      A ^ 2 * Real.sin (ω * t + φ) ^ 2 * (L * ω ^ 2) / 2 := by ring
  rw [this, hLω]
  field_simp
  linear_combination A ^ 2 * htrig

/-- [proved-derived; formal-checked] **Storage is not conserved on its own.** With `ω ≠ 0`, the
capacitive storage is constant in time iff `A = 0`. -/
theorem lc_storage_constant_iff {A ω φ C : ℝ} (hC : 0 < C) (hω : ω ≠ 0) :
    (∀ t s, capacitiveStorage C (lcCharge A ω φ t) = capacitiveStorage C (lcCharge A ω φ s)) ↔
      A = 0 := by
  constructor
  · intro h
    have h1 := h (-φ / ω) ((Real.pi / 2 - φ) / ω)
    have e1 : ω * (-φ / ω) + φ = 0 := by field_simp; ring
    have e2 : ω * ((Real.pi / 2 - φ) / ω) + φ = Real.pi / 2 := by field_simp; ring
    simp only [capacitiveStorage, lcCharge, e1, e2, Real.cos_zero, Real.cos_pi_div_two] at h1
    have : A ^ 2 = 0 := by
      field_simp at h1; nlinarith [h1]
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · rintro rfl t s
    simp [capacitiveStorage, lcCharge]

/-- [proved-derived; formal-checked] **Flow is not conserved on its own.** With `L > 0`,
`ω ≠ 0`, the inductive flow energy is constant iff `A = 0`. -/
theorem lc_flow_constant_iff {A ω φ L : ℝ} (hL : 0 < L) (hω : ω ≠ 0) :
    (∀ t s, inductiveFlow L (lcCurrent A ω φ t) = inductiveFlow L (lcCurrent A ω φ s)) ↔
      A = 0 := by
  constructor
  · intro h
    have h1 := h (-φ / ω) ((Real.pi / 2 - φ) / ω)
    have e1 : ω * (-φ / ω) + φ = 0 := by field_simp; ring
    have e2 : ω * ((Real.pi / 2 - φ) / ω) + φ = Real.pi / 2 := by field_simp; ring
    simp only [inductiveFlow, lcCurrent, e1, e2, Real.sin_zero, Real.sin_pi_div_two] at h1
    have hω2 : 0 < ω ^ 2 := by positivity
    have : L * ω ^ 2 * A ^ 2 = 0 := by nlinarith [h1]
    have hA : A ^ 2 = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hA
  · rintro rfl t s
    simp [inductiveFlow, lcCurrent]

open Soma.Holonics.Millennium.HolonicMeasuredParametron in
/-- [proved-derived; formal-checked] The owner's measured angular frequency of the ring phase
`ωt + φ` between any two distinct times is `ω`. -/
theorem lc_measuredAngularFrequency (ω φ : ℝ) {s t : ℝ} (hst : s ≠ t) :
    measuredAngularFrequency (fun τ : ℝ => ω * τ + φ) id s t = ω := by
  have hne : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  simp only [measuredAngularFrequency,
    Soma.Holonics.Foundation.MeasuredDifferenceReceiver.differenceRatio,
    Soma.Holonics.Foundation.MeasuredDifferenceReceiver.sectionDifference, id]
  field_simp
  ring

/-- [proved-derived; formal-checked] Witness of the exchange: `A = L = C = ω = 1, φ = 0`. At
`t = 0` all energy is capacitive storage; at `t = π/2` all of it is inductive flow. -/
theorem lc_exchange_witness :
    capacitiveStorage 1 (lcCharge 1 1 0 0) = 1 / 2 ∧ inductiveFlow 1 (lcCurrent 1 1 0 0) = 0 ∧
      capacitiveStorage 1 (lcCharge 1 1 0 (Real.pi / 2)) = 0 ∧
        inductiveFlow 1 (lcCurrent 1 1 0 (Real.pi / 2)) = 1 / 2 := by
  simp [capacitiveStorage, inductiveFlow, lcCharge, lcCurrent]

/-! ### The generalized mode -/

variable {Node Branch : Type*} [Fintype Node] [Fintype Branch]

/-- [proved-derived; formal-checked] Pairing a node state with its diagonal response returns
twice the diagonal storage: `⟨v, B^T W B v⟩ = Σ_b W_b (Bv)_b²`. -/
theorem sum_mul_diagonalResponse (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (v : Node → ℝ) :
    ∑ node, v node * diagonalResponse weight incidence v node =
      2 * diagonalStorage weight incidence v := by
  simp only [diagonalResponse, diagonalStorage, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ b, ∑ node, v node *
      (weight b * incidence b node * branchDrop incidence v b) =
        weight b * branchDrop incidence v b * branchDrop incidence v b := by
    intro b
    have hb : ∑ node, v node * (weight b * incidence b node * branchDrop incidence v b) =
        weight b * branchDrop incidence v b * ∑ node, incidence b node * v node := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro node _
      ring
    rw [hb]
    rfl
  simp only [this]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- [proved-derived; formal-checked] Diagonal storage is quadratic in the state. -/
theorem diagonalStorage_smul (weight : Branch → ℝ) (incidence : Branch → Node → ℝ)
    (c : ℝ) (v : Node → ℝ) :
    diagonalStorage weight incidence (fun node => c * v node) =
      c ^ 2 * diagonalStorage weight incidence v := by
  have hdrop : ∀ b, branchDrop incidence (fun node => c * v node) b =
      c * branchDrop incidence v b := by
    intro b
    simp only [branchDrop, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro node _
    ring
  simp only [diagonalStorage, hdrop, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- [definition] The two constitutive energies along `x(t) = cos(ωt) v`, in the node-flux chart:
`x` is the node flux, `C = BᵀW_C B` (capacitance weights) multiplies the **velocity** `x'` (the
node voltage), giving the capacitive storage `½⟨x', C x'⟩`; `K = BᵀW_K B` with `W_K` the inverse
inductances acts as the **stiffness** on `x`, giving the inductive energy `½⟨x, K x⟩`. Here
`x' = −ω sin(ωt) v`. -/
def modeEnergy (stiffnessWeight capacityWeight : Branch → ℝ)
    (incidence : Branch → Node → ℝ) (ω : ℝ) (v : Node → ℝ) (t : ℝ) : ℝ :=
  diagonalStorage capacityWeight incidence (fun node => -(ω * Real.sin (ω * t)) * v node) +
    diagonalStorage stiffnessWeight incidence (fun node => Real.cos (ω * t) * v node)

omit [Fintype Node] in
/-- [proved-derived; formal-checked] Each node of `cos(ωt) v` has velocity `−ω sin(ωt) v`. -/
theorem hasDerivAt_modeState (ω : ℝ) (v : Node → ℝ) (node : Node) (t : ℝ) :
    HasDerivAt (fun τ => Real.cos (ω * τ) * v node) (-(ω * Real.sin (ω * t)) * v node) t := by
  have h : HasDerivAt (fun τ => ω * τ) ω t := by simpa using (hasDerivAt_id t).const_mul ω
  refine (h.cos.mul_const (v node)).congr_deriv ?_
  ring

/-- [proved-derived; formal-checked] **The mode relation balances the two storages.** If
`K v = ω² C v` then `½⟨v, K v⟩ = ω² · ½⟨v, C v⟩` (pairing the relation with `v`). -/
theorem modeStorage_balance {stiffnessWeight capacityWeight : Branch → ℝ}
    {incidence : Branch → Node → ℝ} {ω : ℝ} {v : Node → ℝ}
    (hmode : IsGeneralizedMode stiffnessWeight capacityWeight incidence (ω ^ 2) v) :
    diagonalStorage stiffnessWeight incidence v =
      ω ^ 2 * diagonalStorage capacityWeight incidence v := by
  have h1 := sum_mul_diagonalResponse stiffnessWeight incidence v
  have h2 := sum_mul_diagonalResponse capacityWeight incidence v
  have hsum : ∑ node, v node * diagonalResponse stiffnessWeight incidence v node =
      ω ^ 2 * ∑ node, v node * diagonalResponse capacityWeight incidence v node := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro node _
    rw [hmode.2 node]; ring
  rw [h1, h2] at hsum
  linarith

/-- [proved-derived; formal-checked] **Energy along a generalized mode is conserved.** If
`K v = ω² C v` (`IsGeneralizedMode`), then `½⟨x', C x'⟩ + ½⟨x, K x⟩ = ω² · ½⟨v, C v⟩` at
every time. -/
theorem modeEnergy_conserved {stiffnessWeight capacityWeight : Branch → ℝ}
    {incidence : Branch → Node → ℝ} {ω : ℝ} {v : Node → ℝ}
    (hmode : IsGeneralizedMode stiffnessWeight capacityWeight incidence (ω ^ 2) v) (t : ℝ) :
    modeEnergy stiffnessWeight capacityWeight incidence ω v t =
      ω ^ 2 * diagonalStorage capacityWeight incidence v := by
  have hK := modeStorage_balance hmode
  have htrig := Real.cos_sq_add_sin_sq (ω * t)
  simp only [modeEnergy, diagonalStorage_smul, hK]
  linear_combination (ω ^ 2 * diagonalStorage capacityWeight incidence v) * htrig

/-- [proved-derived; formal-checked] The two terms exchange: at `t = 0` the capacity term is
zero and the stiffness term carries the whole energy `ω²·½⟨v,Cv⟩` (by the mode relation); at
`ωt = π/2` the reverse. -/
theorem modeEnergy_exchange {stiffnessWeight capacityWeight : Branch → ℝ}
    {incidence : Branch → Node → ℝ} {ω : ℝ} {v : Node → ℝ}
    (hmode : IsGeneralizedMode stiffnessWeight capacityWeight incidence (ω ^ 2) v)
    (hω : ω ≠ 0) :
    diagonalStorage capacityWeight incidence (fun node => -(ω * Real.sin (ω * 0)) * v node) = 0 ∧
      diagonalStorage stiffnessWeight incidence (fun node => Real.cos (ω * 0) * v node) =
        ω ^ 2 * diagonalStorage capacityWeight incidence v ∧
      diagonalStorage capacityWeight incidence
          (fun node => -(ω * Real.sin (ω * (Real.pi / 2 / ω))) * v node) =
        ω ^ 2 * diagonalStorage capacityWeight incidence v ∧
      diagonalStorage stiffnessWeight incidence
          (fun node => Real.cos (ω * (Real.pi / 2 / ω)) * v node) = 0 := by
  have e : ω * (Real.pi / 2 / ω) = Real.pi / 2 := by field_simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [diagonalStorage_smul]; simp
  · rw [diagonalStorage_smul, modeStorage_balance hmode]; simp
  · rw [diagonalStorage_smul, e, Real.sin_pi_div_two]; ring
  · rw [diagonalStorage_smul, e, Real.cos_pi_div_two]; ring

/-- The chain incidence `ground–0–1–ground`: three branches over two nodes. -/
def chainIncidence : Fin 3 → Fin 2 → ℝ := ![![1, 0], ![-1, 1], ![0, 1]]

/-- Stiffness (inverse-inductance) weights: every branch inductive, `K = [[2,−1],[−1,2]]`. -/
def chainStiffness : Fin 3 → ℝ := ![1, 1, 1]

/-- Capacity weights: only the grounded branches capacitive, `C = I`. -/
def chainCapacity : Fin 3 → ℝ := ![1, 0, 1]

/-- [proved-derived; formal-checked] **Nondegenerate witness.** On the chain, `K ≠ C` and both
are nonsingular; `(1, −1)` is a generalized mode at `ω² = 3` and `(1, 1)` one at `ω² = 1`, so
`K` is not a multiple of `C`. The antisymmetric mode has capacity storage `1`. -/
theorem modeWitness :
    IsGeneralizedMode chainStiffness chainCapacity chainIncidence 3 ![1, -1] ∧
      IsGeneralizedMode chainStiffness chainCapacity chainIncidence 1 ![1, 1] ∧
      diagonalStorage chainCapacity chainIncidence ![1, -1] = 1 ∧
      diagonalResponse chainStiffness chainIncidence ![1, 0] 0 ≠
        diagonalResponse chainCapacity chainIncidence ![1, 0] 0 := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro h; have := congrFun h 0; norm_num at this
  · intro node
    fin_cases node <;>
      simp [diagonalResponse, branchDrop, chainIncidence, chainStiffness, chainCapacity,
        Fin.sum_univ_three, Fin.sum_univ_two] <;> norm_num
  · intro h; have := congrFun h 0; norm_num at this
  · intro node
    fin_cases node <;>
      simp [diagonalResponse, branchDrop, chainIncidence, chainStiffness, chainCapacity,
        Fin.sum_univ_three, Fin.sum_univ_two]
  · simp [diagonalStorage, branchDrop, chainIncidence, chainCapacity, Fin.sum_univ_three,
      Fin.sum_univ_two]
    norm_num
  · simp [diagonalResponse, branchDrop, chainIncidence, chainStiffness, chainCapacity,
      Fin.sum_univ_three, Fin.sum_univ_two]

end Exchange

/-! ## 2. A section crossing of the ring is a clock tick -/

section Clock

open Soma.Holonics.Millennium.HolonicClockedPantographicSwing

variable {ClockAddress : Type*}

/-- [definition] The ring of a rational clock passage `n/d`: its micro-state is the exact integer
potential `a` (phase `a/d` of a turn), each micro-step advances `1/d` of a turn, the cycle count
is the completed turns `a / d`, the phase face is the carrier `e^{2πi a/d}`, and the section is
phase `0`. One source tick is `n` micro-steps. -/
def ringOscillator (passage : RationalClockPassage ClockAddress) :
    SectionedOscillator ClockAddress ℕ ℂ where
  address := passage.target
  advance a := a + 1
  cycleCount a := ((a / passage.denominator : ℕ) : ℤ)
  phase a := phaseCarrier (2 * Real.pi * (a : ℝ) / passage.denominator)
  sectionMark a := decide (a % passage.denominator = 0)

/-- [proved-derived; formal-checked] A micro-step from `a` is an owner `Crossing` exactly when it
lands on the section, for `d ≥ 2` (for `d = 1` every state is on the section, so no step
leaves it). -/
theorem ringCrossing_iff (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (a : ℕ) :
    (∃ c : (ringOscillator passage).Crossing, c.source = a) ↔
      (a + 1) % passage.denominator = 0 := by
  set d := passage.denominator with hdef
  constructor
  · rintro ⟨c, rfl⟩
    have h := c.entersSection
    rw [c.advances] at h
    simpa [ringOscillator, ← hdef] using h
  · intro h
    have hdvd : d ∣ a + 1 := Nat.dvd_of_mod_eq_zero h
    have hleave : a % d ≠ 0 := by
      intro h0
      have h1 : 1 % d = 1 := Nat.mod_eq_of_lt (by omega)
      have : (a + 1) % d = 1 := by rw [Nat.add_mod, h0, h1, zero_add, h1]
      omega
    refine ⟨⟨a, a + 1, rfl, ?_, ?_, ?_⟩, rfl⟩
    · simp only [ringOscillator, ← hdef]
      rw [Nat.succ_div, if_pos hdvd]
      push_cast; ring
    · simpa [ringOscillator, ← hdef] using hleave
    · simpa [ringOscillator, ← hdef] using h

/-- [definition] The number of section crossings among the first `N` micro-steps from `r`. -/
def ringCrossings (d r N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun j => (r + j + 1) % d = 0)).card

/-- [proved-derived; formal-checked] Starting inside the first turn (`r < d`), the crossings of
`N` micro-steps are the completed turns `(r + N)/d`. -/
theorem ringCrossings_eq (d r : ℕ) (hr : r < d) (N : ℕ) :
    ringCrossings d r N = (r + N) / d := by
  induction N with
  | zero => simp [ringCrossings, Nat.div_eq_of_lt hr]
  | succ N ih =>
    rw [ringCrossings, Finset.range_add_one, Finset.filter_insert]
    have hnot : N ∉ (Finset.range N).filter (fun j => (r + j + 1) % d = 0) := by simp
    rw [show r + (N + 1) = (r + N) + 1 by ring, Nat.succ_div, ← ih]
    split_ifs with h1 h2 h2
    · rw [Finset.card_insert_of_notMem hnot]; rfl
    · exact absurd (Nat.dvd_of_mod_eq_zero h1) h2
    · exact absurd (Nat.mod_eq_zero_of_dvd h2) h1
    · rfl

open Classical in
/-- [definition] The owner `Crossing` records along the orbit: the micro-steps `j < N` from `r`
at which a `Crossing` of `ringOscillator` starts. -/
noncomputable def ownerCrossings (passage : RationalClockPassage ClockAddress) (r N : ℕ) : ℕ :=
  ((Finset.range N).filter
    (fun j => ∃ c : (ringOscillator passage).Crossing, c.source = r + j)).card

/-- [proved-derived; formal-checked] At `d = 1` every state lies on the section, so the ring has
no owner `Crossing` at all; the arithmetic count `(r+N)/1 = N` is then not a crossing count. -/
theorem no_crossing_of_denominator_one (passage : RationalClockPassage ClockAddress)
    (hd : passage.denominator = 1) (c : (ringOscillator passage).Crossing) : False := by
  have h := c.leavesSection
  simp [ringOscillator, hd] at h
  exact h (Nat.mod_one _)

/-- [proved-derived; formal-checked] **Ticks are crossings.** For `d ≥ 2`, along the orbit of `k`
source ticks (`n·k` micro-steps) from residue `r < d`, the number of owner `Crossing` records
equals the owner's `targetTicks r k` (through `ringCrossing_iff` and the count `ringCrossings_eq`),
and the owner's reconstruction `d · ticks + residue = r + n k` holds. -/
theorem ownerCrossings_eq_targetTicks (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (r k : ℕ) (hr : r < passage.denominator) :
    ownerCrossings passage r (passage.numerator * k) = passage.targetTicks r k ∧
      passage.denominator * ownerCrossings passage r (passage.numerator * k) +
          passage.phaseResidue r k = r + passage.numerator * k := by
  have hcount : ownerCrossings passage r (passage.numerator * k) =
      ringCrossings passage.denominator r (passage.numerator * k) := by
    classical
    unfold ownerCrossings ringCrossings
    congr 1
    apply Finset.filter_congr
    intro j _
    rw [ringCrossing_iff passage hd]
  have h : ownerCrossings passage r (passage.numerator * k) = passage.targetTicks r k := by
    rw [hcount, ringCrossings_eq _ _ hr]; rfl
  exact ⟨h, h ▸ passage.denominator_mul_targetTicks_add_phaseResidue r k⟩

/-- [proved-derived; formal-checked] Whole turns are invisible to the carrier. -/
theorem phaseCarrier_add_nat_turns (θ : ℝ) (m : ℕ) :
    phaseCarrier (θ + 2 * Real.pi * m) = phaseCarrier θ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show θ + 2 * Real.pi * ((m + 1 : ℕ) : ℝ) = (θ + 2 * Real.pi * m) + 2 * Real.pi by
      push_cast; ring, phaseCarrier_fullTurn_fibre, ih]

/-- [proved-derived; formal-checked] **The residue is the phase.** The ring's carrier after `k`
source ticks is the carrier of the owner's `phaseResidue`; the completed turns (the ticks) are
exactly what the carrier forgets. -/
theorem ringPhase_eq_residuePhase (passage : RationalClockPassage ClockAddress) (r k : ℕ) :
    (ringOscillator passage).phase (r + passage.numerator * k) =
      phaseCarrier (2 * Real.pi * (passage.phaseResidue r k : ℝ) / passage.denominator) := by
  have hd : (passage.denominator : ℝ) ≠ 0 := by exact_mod_cast passage.denominator_pos.ne'
  have hrec := passage.denominator_mul_targetTicks_add_phaseResidue r k
  change phaseCarrier (2 * Real.pi * ((r + passage.numerator * k : ℕ) : ℝ) /
    passage.denominator) = _
  rw [← hrec]
  push_cast
  rw [show 2 * Real.pi * ((passage.denominator : ℝ) * (passage.targetTicks r k : ℝ) +
        (passage.phaseResidue r k : ℝ)) / passage.denominator =
      2 * Real.pi * (passage.phaseResidue r k : ℝ) / passage.denominator +
        2 * Real.pi * (passage.targetTicks r k : ℝ) by field_simp; ring]
  exact phaseCarrier_add_nat_turns _ _

/-- The passage `3/4` between one addressed clock. -/
def threeQuarterPassage : RationalClockPassage Unit where
  source := ()
  target := ()
  numerator := 3
  denominator := 4
  numerator_pos := by decide
  denominator_pos := by decide

/-- [proved-derived; formal-checked] Witness: at rate `3/4`, three source ticks from `r = 0` are
nine micro-steps with two owner `Crossing` records, residue `1`, and final carrier `i` (a quarter
turn); the micro-step from `3` is a genuine owner `Crossing`. -/
theorem threeQuarter_witness :
    ownerCrossings threeQuarterPassage 0 (3 * 3) = 2 ∧ threeQuarterPassage.targetTicks 0 3 = 2 ∧
      threeQuarterPassage.phaseResidue 0 3 = 1 ∧
      (ringOscillator threeQuarterPassage).phase (0 + 3 * 3) = Complex.I ∧
      ∃ c : (ringOscillator threeQuarterPassage).Crossing, c.source = 3 := by
  refine ⟨?_, by decide, by decide, ?_, ?_⟩
  · exact (ownerCrossings_eq_targetTicks threeQuarterPassage (by decide) 0 3 (by decide)).1.trans
      (by decide)
  · have h := ringPhase_eq_residuePhase threeQuarterPassage 0 3
    change (ringOscillator threeQuarterPassage).phase (0 + threeQuarterPassage.numerator * 3) = _
    rw [h]
    have hres : threeQuarterPassage.phaseResidue 0 3 = 1 := by decide
    rw [hres]
    have : 2 * Real.pi * ((1 : ℕ) : ℝ) / (threeQuarterPassage.denominator : ℝ) =
        Real.pi / 2 + 2 * Real.pi * ((0 : ℤ) : ℝ) := by
      simp [threeQuarterPassage]; ring
    rw [this, phaseCarrier_windingI]
  · exact (ringCrossing_iff threeQuarterPassage (by decide) 3).mpr (by decide)

end Clock

/-! ## 3. The perceptron is the locked-sheet receiver face of a coupled population -/

section Perceptron

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- [definition] Coupled population with an input drive. The drive at site `i` is the owner's
`phaseCoupling (h i)` to a reference carrier held at phase `0`. -/
def drivenPhaseEnergy (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (phase : ι → ℝ) : ℝ :=
  phaseNetworkEnergy edges weight phase + ∑ i, phaseCoupling (drive i) (phase i) 0

/-- [definition] Its locked-sheet (Ising) reading. -/
def drivenIsingEnergy (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (state : ι → Bool) : ℝ :=
  isingNetworkEnergy edges weight state + ∑ i, -(drive i) * spinFace (state i)

/-- [proved-derived; formal-checked] On locked sheets the driven phase energy is the driven
Ising energy (`phaseNetworkEnergy_binaryPhase`, `phaseCoupling_binaryPhase`). -/
theorem drivenPhaseEnergy_binaryPhase (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (drive : ι → ℝ) (state : ι → Bool) :
    drivenPhaseEnergy edges weight drive (fun i => binaryPhase (state i)) =
      drivenIsingEnergy edges weight drive state := by
  unfold drivenPhaseEnergy drivenIsingEnergy
  rw [phaseNetworkEnergy_binaryPhase]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := phaseCoupling_binaryPhase (drive i) (state i) false
  have h0 : binaryPhase false = 0 := rfl
  rw [h0] at h
  change phaseCoupling (drive i) (binaryPhase (state i)) 0 = _
  rw [h]
  simp [isingCoupling, spinFace]

/-- [definition] The local field at site `i`: `Σ_j w_ij σ_j + h_i`, summed over every admitted
edge incident to `i` in either slot. -/
def localField (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (state : ι → Bool) (i : ι) : ℝ :=
  (∑ e ∈ edges, ((if e.1 = i then weight e.1 e.2 * spinFace (state e.2) else 0) +
    (if e.2 = i then weight e.1 e.2 * spinFace (state e.1) else 0))) + drive i

/-- [definition] The part of the energy that does not involve site `i`. -/
def restEnergy (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (state : ι → Bool) (i : ι) : ℝ :=
  (∑ e ∈ edges, if e.1 = i ∨ e.2 = i then 0 else
      isingCoupling (weight e.1 e.2) (state e.1) (state e.2)) +
    ∑ j, if j = i then 0 else -(drive j) * spinFace (state j)

/-- [proved-derived; formal-checked] **The local-field reduction.** Without self-loops, putting
site `i` on sheet `s` gives energy `rest − σ(s) · localField`. -/
theorem drivenIsing_update (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (noLoop : ∀ e ∈ edges, e.1 ≠ e.2) (state : ι → Bool) (i : ι) (s : Bool) :
    drivenIsingEnergy edges weight drive (Function.update state i s) =
      restEnergy edges weight drive state i -
        spinFace s * localField edges weight drive state i := by
  have hedge : ∀ e ∈ edges,
      isingCoupling (weight e.1 e.2) (Function.update state i s e.1)
          (Function.update state i s e.2) =
        (if e.1 = i ∨ e.2 = i then 0 else
          isingCoupling (weight e.1 e.2) (state e.1) (state e.2)) -
        spinFace s * ((if e.1 = i then weight e.1 e.2 * spinFace (state e.2) else 0) +
          (if e.2 = i then weight e.1 e.2 * spinFace (state e.1) else 0)) := by
    intro e he
    have hne := noLoop e he
    by_cases h1 : e.1 = i <;> by_cases h2 : e.2 = i
    · exact absurd (h1.trans h2.symm) hne
    · simp [h1, h2, isingCoupling]; ring
    · simp [h1, h2, isingCoupling]; ring
    · simp [h1, h2, isingCoupling]
  have hsite : ∀ j, -(drive j) * spinFace (Function.update state i s j) =
      (if j = i then 0 else -(drive j) * spinFace (state j)) -
        spinFace s * (if j = i then drive j else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp; ring
    · simp [hj]
  unfold drivenIsingEnergy isingNetworkEnergy restEnergy localField
  rw [Finset.sum_congr rfl hedge, Finset.sum_congr rfl (fun j _ => hsite j),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

omit [Fintype ι] in
/-- [proved-derived; formal-checked] The local field of `i` does not read `i`'s own sheet. -/
theorem localField_update (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (noLoop : ∀ e ∈ edges, e.1 ≠ e.2) (state : ι → Bool) (i : ι) (s : Bool) :
    localField edges weight drive (Function.update state i s) i =
      localField edges weight drive state i := by
  unfold localField
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  have hne := noLoop e he
  by_cases h1 : e.1 = i <;> by_cases h2 : e.2 = i
  · exact absurd (h1.trans h2.symm) hne
  · have : e.2 ≠ i := h2
    simp [h1, this]
  · have : e.1 ≠ i := h1
    simp [h2, this]
  · simp [h1, h2]

/-- [definition] The threshold unit: the zero sheet when the field is nonnegative, the half-turn
sheet when it is negative, i.e. `spinFace = sign(field)` with the tie on `+1`. -/
def thresholdSheet (field : ℝ) : Bool := decide (field < 0)

theorem spinFace_thresholdSheet_mul (field : ℝ) :
    spinFace (thresholdSheet field) * field = |field| := by
  unfold thresholdSheet spinFace
  by_cases h : field < 0
  · simp [h, abs_of_neg h]
  · simp [h, abs_of_nonneg (not_lt.mp h)]

/-- [proved-derived; formal-checked] **The energy-minimizing sheet is the perceptron threshold.**
Given its neighbours, site `i` on `thresholdSheet (Σ_j w_ij σ_j + h_i)` has energy no larger than
on either sheet. -/
theorem thresholdSheet_minimizes (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (drive : ι → ℝ) (noLoop : ∀ e ∈ edges, e.1 ≠ e.2) (state : ι → Bool) (i : ι) (s : Bool) :
    drivenIsingEnergy edges weight drive
        (Function.update state i (thresholdSheet (localField edges weight drive state i))) ≤
      drivenIsingEnergy edges weight drive (Function.update state i s) := by
  rw [drivenIsing_update _ _ _ noLoop, drivenIsing_update _ _ _ noLoop,
    spinFace_thresholdSheet_mul]
  have : spinFace s * localField edges weight drive state i ≤
      |localField edges weight drive state i| := by
    cases s <;> simp [spinFace, le_abs_self, neg_le_abs]
  linarith

/-- [proved-derived; formal-checked] When the field is nonzero the minimizer is strict: the other
sheet has energy larger by `2|field|`. -/
theorem thresholdSheet_strict (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (drive : ι → ℝ) (noLoop : ∀ e ∈ edges, e.1 ≠ e.2) (state : ι → Bool) (i : ι)
    (hfield : localField edges weight drive state i ≠ 0) :
    drivenIsingEnergy edges weight drive
        (Function.update state i (thresholdSheet (localField edges weight drive state i))) <
      drivenIsingEnergy edges weight drive
        (Function.update state i (!thresholdSheet (localField edges weight drive state i))) := by
  rw [drivenIsing_update _ _ _ noLoop, drivenIsing_update _ _ _ noLoop,
    spinFace_thresholdSheet_mul]
  have hflip : ∀ b : Bool, spinFace (!b) = -spinFace b := by
    intro b; cases b <;> simp [spinFace]
  rw [hflip, neg_mul, spinFace_thresholdSheet_mul]
  have := abs_pos.mpr hfield
  linarith

/-- [definition] The nearest locked sheet of an unlocked phase: its sign receiver. -/
def sheetReading (θ : ℝ) : Bool := decide (Real.cos θ < 0)

theorem sheetReading_binaryPhase (b : Bool) : sheetReading (binaryPhase b) = b := by
  cases b <;> simp [sheetReading, binaryPhase]

/-- [definition] The perceptron output of a (possibly unlocked) phase configuration at site
`i`: read every neighbour's sheet, form the local field with the drive, and threshold it. -/
def perceptronOutput (edges : Finset (ι × ι)) (weight : ι → ι → ℝ) (drive : ι → ℝ)
    (phase : ι → ℝ) (i : ι) : Bool :=
  thresholdSheet (localField edges weight drive (fun k => sheetReading (phase k)) i)

/-- The two-site population of the separation witness: one unit coupling `(0, 1)` and unit drive
on both sites. -/
abbrev faceEdges : Finset (Fin 2 × Fin 2) := {((0 : Fin 2), (1 : Fin 2))}

/-- [proved-derived; formal-checked] **The perceptron is a face, not the ring.** On the two-site
population with unit coupling and unit drive, the phase configurations `(0, 0)` and `(π/3, 0)`
have the same local field `2` at both sites (neighbour sheet plus drive), hence the same
threshold output (the zero sheet), yet different driven phase energy (`−3` vs `−2`) and
different quadrature at site `0` (`Im e^{iθ₀}` is `0` vs `√3/2`). -/
theorem perceptron_is_a_face :
    (∀ i, localField faceEdges (fun _ _ => 1) (fun _ => 1)
        (fun k => sheetReading ((fun _ : Fin 2 => (0 : ℝ)) k)) i = 2) ∧
      (∀ i, localField faceEdges (fun _ _ => 1) (fun _ => 1)
        (fun k => sheetReading (![Real.pi / 3, 0] k)) i = 2) ∧
      (∀ i, perceptronOutput faceEdges (fun _ _ => 1) (fun _ => 1) (fun _ => 0) i = false) ∧
      (∀ i, perceptronOutput faceEdges (fun _ _ => 1) (fun _ => 1) ![Real.pi / 3, 0] i =
        false) ∧
      drivenPhaseEnergy faceEdges (fun _ _ => 1) (fun _ => 1) (fun _ => 0) = -3 ∧
      drivenPhaseEnergy faceEdges (fun _ _ => 1) (fun _ => 1) ![Real.pi / 3, 0] = -2 ∧
      (phaseCarrier 0).im = 0 ∧ (phaseCarrier (Real.pi / 3)).im = Real.sqrt 3 / 2 := by
  have hA : ∀ i, localField faceEdges (fun _ _ => 1) (fun _ => 1)
      (fun k => sheetReading ((fun _ : Fin 2 => (0 : ℝ)) k)) i = 2 := by
    intro i
    fin_cases i <;> simp [localField, sheetReading, spinFace] <;> norm_num
  have hB : ∀ i, localField faceEdges (fun _ _ => 1) (fun _ => 1)
      (fun k => sheetReading (![Real.pi / 3, 0] k)) i = 2 := by
    intro i
    fin_cases i <;> simp [localField, sheetReading, spinFace] <;> norm_num
  refine ⟨hA, hB, fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_⟩
  · rw [perceptronOutput, hA i]; simp [thresholdSheet]
  · rw [perceptronOutput, hB i]; simp [thresholdSheet]
  · simp [drivenPhaseEnergy, phaseNetworkEnergy, phaseCoupling]; norm_num
  · simp [drivenPhaseEnergy, phaseNetworkEnergy, phaseCoupling, Real.cos_pi_div_three]
    norm_num
  · simp [phaseCarrier]
  · rw [phaseCarrier, Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

end Perceptron

/-! ## 4. The global half-turn -/

section HalfTurn

variable {ι : Type*} [DecidableEq ι]

theorem spinFace_not (b : Bool) : spinFace (!b) = -spinFace b := by
  cases b <;> simp [spinFace]

/-- [proved-derived; formal-checked] A global half-turn of every phase leaves every coupling
energy unchanged, locked or not. -/
theorem phaseNetworkEnergy_halfTurnSheet (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (phase : ι → ℝ) :
    phaseNetworkEnergy edges weight (fun i => halfTurnSheet (phase i)) =
      phaseNetworkEnergy edges weight phase := by
  unfold phaseNetworkEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [phaseCoupling, halfTurnSheet]
  congr 2
  ring

/-- [proved-derived; formal-checked] On locked sheets the global half-turn is `σ ↦ ¬σ`, and it
preserves every Ising pairing energy. -/
theorem isingNetworkEnergy_not (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (state : ι → Bool) :
    isingNetworkEnergy edges weight (fun i => !state i) =
      isingNetworkEnergy edges weight state := by
  unfold isingNetworkEnergy
  apply Finset.sum_congr rfl
  intro e _
  simp only [isingCoupling, spinFace_not]
  ring

/-- [proved-derived; formal-checked] **The half-turn composite.** A global half-turn preserves
the coupling energy of any phase configuration and each pump storage
(`pumpStorage_halfTurnSheet`), negates each carrier (`phaseCarrier_halfTurnSheet`), and on locked
sheets acts as `σ ↦ ¬σ`, preserving the Ising energy. -/
theorem globalHalfTurn_composite (edges : Finset (ι × ι)) (weight : ι → ι → ℝ)
    (strength pumpPhase : ℝ) (phase : ι → ℝ) (state : ι → Bool) :
    phaseNetworkEnergy edges weight (fun i => halfTurnSheet (phase i)) =
        phaseNetworkEnergy edges weight phase ∧
      (∀ i, pumpStorage strength pumpPhase (halfTurnSheet (phase i)) =
        pumpStorage strength pumpPhase (phase i)) ∧
      (∀ i, phaseCarrier (halfTurnSheet (phase i)) = -phaseCarrier (phase i)) ∧
      (∀ i, phaseCarrier (binaryPhase (!state i)) =
        phaseCarrier (halfTurnSheet (binaryPhase (state i)))) ∧
      isingNetworkEnergy edges weight (fun i => !state i) =
        isingNetworkEnergy edges weight state := by
  refine ⟨phaseNetworkEnergy_halfTurnSheet edges weight phase,
    fun i => pumpStorage_halfTurnSheet _ _ _, fun i => phaseCarrier_halfTurnSheet _,
    fun i => ?_, isingNetworkEnergy_not edges weight state⟩
  rw [phaseCarrier_halfTurnSheet, phaseCarrier_binaryPhase, phaseCarrier_binaryPhase,
    spinFace_not]
  push_cast; ring

/-- [proved-derived; formal-checked] Witness: two sites, unit coupling, opposite sheets; the
Ising energy is `1` before and after the global half-turn. -/
theorem halfTurn_witness :
    isingNetworkEnergy {((0 : Fin 2), (1 : Fin 2))} (fun _ _ => 1) ![false, true] = 1 ∧
      isingNetworkEnergy {((0 : Fin 2), (1 : Fin 2))} (fun _ _ => 1)
        (fun i => !(![false, true] i)) = 1 := by
  constructor <;> simp [isingNetworkEnergy, isingCoupling, spinFace]

/-- [proved-derived; formal-checked] The drive is what breaks the half-turn: one site with unit
drive has driven energy `−1` on the zero sheet and `1` on the half-turn sheet. -/
theorem drive_breaks_halfTurn :
    drivenIsingEnergy (∅ : Finset (Unit × Unit)) (fun _ _ => 0) (fun _ => 1) (fun _ => false) =
        -1 ∧
      drivenIsingEnergy (∅ : Finset (Unit × Unit)) (fun _ _ => 0) (fun _ => 1)
        (fun _ => true) = 1 := by
  constructor <;> simp [drivenIsingEnergy, isingNetworkEnergy, spinFace]

end HalfTurn

section Audit

#print axioms lc_energy_conserved
#print axioms lc_storage_constant_iff
#print axioms lc_flow_constant_iff
#print axioms lc_measuredAngularFrequency
#print axioms lc_exchange_witness
#print axioms modeStorage_balance
#print axioms modeEnergy_conserved
#print axioms modeEnergy_exchange
#print axioms modeWitness
#print axioms ringCrossing_iff
#print axioms ringCrossings_eq
#print axioms no_crossing_of_denominator_one
#print axioms ownerCrossings_eq_targetTicks
#print axioms ringPhase_eq_residuePhase
#print axioms threeQuarter_witness
#print axioms drivenPhaseEnergy_binaryPhase
#print axioms drivenIsing_update
#print axioms localField_update
#print axioms thresholdSheet_minimizes
#print axioms thresholdSheet_strict
#print axioms perceptron_is_a_face
#print axioms globalHalfTurn_composite
#print axioms halfTurn_witness
#print axioms drive_breaks_halfTurn

end Audit

end Soma.Holonics.Objects.Parametron

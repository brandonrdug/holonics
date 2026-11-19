import Holonics.Objects.Parametron
import Holonics.Aeon.Clock.Winding
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card

/-!
# The continuous section crossing of `A cos(ωt + φ)` is the micro-step ring, sampled

[definition] Object 5 of `docs/ELEMENTARY_OBJECTS.md` (the parametron; a section crossing is a
clock tick, the winding is the carry) with the aeon, epoch and cycle of object 12. Source: #410's
box "Continuous crossing as the micro-step ring", which is the `[open]` paragraph of
`Objects/Parametron` ("the continuous section crossing of `A cos(ωt + φ)` is not identified with
it by a theorem") and the open item of `docs/ELEMENTARY_OBJECTS.md` §5 ("the continuous crossing
of `A cos(ωt + φ)` as the micro-step ring"). The owners joined: `Objects/Parametron` (the charge
`lcCharge`, its rate `lcCurrent` and `hasDerivAt_lcCharge`; `ringOscillator`, `ringCrossing_iff`,
`ringCrossings`, `ringCrossings_eq`, `ownerCrossings_eq_targetTicks`, `ringPhase_eq_residuePhase`,
`threeQuarterPassage`, `threeQuarter_witness`), `Geometry/HolonicClockedPantographicSwing`
(`SectionedOscillator`, `Crossing`, `RationalClockPassage`, `targetTicks`, `phaseResidue`) and
`Aeon/Clock/Winding` (`windings t = ⌊t⌋`, `openPhase t = t − ⌊t⌋`; its scope note leaves
continuous phase flows outside it). Record:
`2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME`. Atlas rows read:
`parametron.lc-exchange`, `parametron.ring-crossing-is-tick`, `parametron.three-quarter-witness`,
`parametron.crossings-epoch-ticks`, `aeon.split-is-div-rem`, `aeon.epoch-partition`,
`aeon.nontransversal-section`, `aeon.forward-aeon`, `hnn.ring-clock`,
`navigator.lifted-phase-jump` and `radix.carry-rhythm`.

The section is the **upward zero** `{x = 0, ẋ > 0}` of the charge `x(t) = A cos(ωt + φ)`, with
`A > 0`, `ω > 0` and rate `ẋ = −Aω sin(ωt + φ)`. The crest `{ẋ = 0, x > 0}` is the upward zero of
the same oscillator with its phase shifted by a quarter turn, `φ ↦ φ − π/2` (item 1). The lifted
phase in turns, counted from the section, is `θ(t) = (ωt + φ + π/2)/(2π)`.

What is proved.

1. [proved-standard; formal-checked] **The continuous section crossings.** In the lifted angle
   `ψ = ωt + φ + π/2` the charge is `A sin ψ` and the rate `Aω cos ψ` (`lcCharge_eq_sin`,
   `lcCurrent_eq_cos`), so `t` is an upward zero iff `cos ψ = 1` (`isUpwardZero_iff_cos`), iff
   `ωt + φ = −π/2 + 2πk` for an integer `k` (`isUpwardZero_iff`), iff `θ(t)` is an integer
   (`isUpwardZero_iff_liftedPhase`), iff `t` is the `k`-th crossing time
   `t_k = (2πk − π/2 − φ)/ω` (`isUpwardZero_iff_crossingTime`, `liftedPhase_crossingTime`). Every
   crossing is transversal: the rate there is `Aω` and it is the derivative of the charge
   (`lcCurrent_of_isUpwardZero`, `hasDerivAt_of_isUpwardZero`). The crest is the quarter-turn shift
   (`isCrest_iff_isUpwardZero_shift`, `isCrest_iff`). The crossings in `(t₀, t₁]`, `t₀ ≤ t₁`, are
   the crossing times indexed by the integers in `(⌊θ(t₀)⌋, ⌊θ(t₁)⌋]` (`upwardZerosIn_eq`): a
   finite set whose count is `⌊θ(t₁)⌋ − ⌊θ(t₀)⌋` (`upwardZerosIn_finite_ncard`), the completed
   windings of the lifted phase in the owner's chart (`upwardZerosIn_ncard_eq_windings`). The
   section is where the phase carrier `e^{2πiθ(t)}` reads `1`, the charge is `A` times its
   quadrature and the rate `Aω` times its in-phase part (`isUpwardZero_iff_carrier`,
   `lcCharge_eq_im`, `lcCurrent_eq_re`).
2. [proved-derived; formal-checked] **The micro-step ring is the sampled oscillator.** For
   `d ≥ 1` micro-steps a period, sample at `t_k = t₀ + k·2π/(dω)` (`sampleTime`); then
   `θ(t_k) = θ(t₀) + k/d` (`liftedPhase_sampleTime`). The ring's start is
   `r = ⌊d · openPhase θ(t₀)⌋ < d` and the sub-step offset `δ = d · openPhase θ(t₀) − r ∈ [0, 1)`
   (`ringStart`, `subStep`, `ringStart_lt`, `subStep_nonneg`, `subStep_lt_one`,
   `mul_openPhase_split`). The ring's micro-state at step `k` is the completed micro-steps of the
   sampled phase, `⌊d θ(t_k)⌋ = d ⌊θ(t₀)⌋ + (r + k)` (`floor_mul_liftedPhase_sampleTime`), and its
   completed turns are the completed windings, `⌊θ(t_k)⌋ = ⌊θ(t₀)⌋ + (r + k)/d`
   (`floor_liftedPhase_sampleTime`, through the division with remainder
   `floor_add_div_of_split`). The continuous crossings over `N` micro-steps, `(t₀, t_N]`, number
   `ringCrossings d r N = (r + N)/d` for every `φ` and `t₀` (`upwardZeros_sampled_ncard`): the
   count does not see `δ`, and two starts with one ring start count alike at every `N`
   (`sampled_ncard_eq_of_ringStart_eq`). The micro-step `(t_k, t_(k+1)]` holds one crossing when
   the ring's micro-step from `r + k` lands on the section, `(r + k + 1) % d = 0`, and none
   otherwise (`microStep_ncard`); for `d ≥ 2` this is the owner's `Crossing` through
   `ringCrossing_iff` (`microStep_crossing_iff_ownerCrossing`). At `d = 1` every micro-step holds
   one continuous crossing (`microStep_ncard_denominator_one`), while the owner's ring at `d = 1`
   marks every state on its section and has no `Crossing` (`no_crossing_of_denominator_one`): the
   count `(r + N)/1 = N` is then the continuous crossings' and not the owner's records'.
3. [proved-derived; formal-checked] **Joined to the clock passage.** For a `RationalClockPassage`
   with numerator `n` and denominator `d`, the oscillator sampled over `N = n·k` micro-steps crosses
   `targetTicks r k` times (`sampled_crossings_eq_targetTicks`), and for `d ≥ 2` that is the
   owner's count of `Crossing` records (`sampled_crossings_eq_ownerCrossings`, through
   `ownerCrossings_eq_targetTicks`). Its carrier at `t_N` is the ring's phase at `r + N` advanced by
   the offset, `e^{2πiθ(t_N)} = e^{2πi(r + N)/d} · e^{2πiδ/d}` (`oscillatorCarrier_sampleTime`),
   hence the owner's residue phase advanced by `2πδ/d`,
   `e^{2πiθ(t_N)} = (ringOscillator passage).phase (r + n k) · e^{2πiδ/d}
   = e^{2πi · phaseResidue r k / d} · e^{2πiδ/d}` (`sampled_carrier_eq_residuePhase`, through
   `ringPhase_eq_residuePhase`; `phaseCarrier_add`, `phaseCarrier_add_int_turns`). The count is
   the ring's; the sub-step offset survives only in the carrier.
4. [proved-derived; formal-checked] **Witnesses.** The owner's three-quarter passage read from the
   continuous oscillator: `φ = −π/2`, `t₀ = 0`, `d = 4` give `r = 0`, `δ = 0`, two crossings in
   `(0, 9·2π/(4ω)]`, the owner's `ownerCrossings threeQuarterPassage 0 9`, and carrier `i` at the
   end (`threeQuarter_continuous_witness`). The start `φ = −π/4` has `θ(0) = 1/8`, `r = 0`,
   `δ = 1/2 ≠ 0` and the same two crossings, with carrier `i · e^{iπ/4}` at the end
   (`threeQuarter_offset_witness`).

What is not claimed.

- A damped, pumped or driven oscillator: the parametron's Mathieu equation, a time-varying `ω`,
  the pump's Floquet growth (`HNN/Floquet`). The oscillator here is the free `A cos(ωt + φ)`.
- A nonuniform sampling clock: the samples are `d` a period, equally spaced in time.
- The energy exchange of the LC pair (`Objects/Parametron` item 1 holds it; nothing here uses it),
  and crossings of a general periodic orbit or of any section other than the upward zero and its
  quarter-turn shift, the crest. The downward zero is the upward zero of `φ + π`, not stated.
- `A ≤ 0` or `ω ≤ 0`: the orientation of the section reverses there, and those cases are excluded
  by hypothesis.
- That the owner's `Crossing` at `d = 1` counts the continuous crossings: it does not (item 2).
- Any precision law for the sample times or the lifted phase: they are read in `ℝ`, the chart of
  the classical statement, and no carrier width is asserted.

The computational object is the helical pair interaction read as a clock: the oscillator's lifted
phase `θ` is the helix over the carrier's circle, its whole windings are the carry, and the
receiver's section (the upward zero) is the face at which the helix pairs with the receiver, one
transversal crossing for each completed winding. The micro-step ring is that helix read at `d`
equally spaced places a turn: its micro-state is the completed micro-steps of the sampled phase,
its crossings are the helix's windings, and the sub-step offset is the placement of the samples
inside a micro-step, which the count forgets and the carrier keeps. Of the winding guide's six
general objects this touches the helix (lifted phase, windings and carry, `⌊θ(t₁)⌋ − ⌊θ(t₀)⌋`),
faces and placement (the section as the carrier's face at `1`, the sample placement `δ`, the
carrier at `t_N` as the residue face advanced by `2πδ/d`) and the tube (the clocked span
`(t₀, t_N]` cut into micro-steps, whose epochs are the ring's). The pair's modular address, the
cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.ContinuousCrossing

open scoped Real
open Holonics.Objects.Parametron
open Holonics.Physics.HolonicParametron
open Holonics.Geometry.HolonicClockedPantographicSwing
open Holonics.Aeon.Clock.Winding (windings openPhase)

/-! ## 1. The continuous section crossings -/

section Continuous

variable {A ω φ t : ℝ}

/-- [definition] The upward zero of the charge `x = A cos(ωt + φ)`: the charge is zero and its
rate `ẋ = lcCurrent` is positive. -/
def IsUpwardZero (A ω φ t : ℝ) : Prop :=
  lcCharge A ω φ t = 0 ∧ 0 < lcCurrent A ω φ t

/-- [definition] The crest: the rate is zero and the charge is positive. -/
def IsCrest (A ω φ t : ℝ) : Prop :=
  lcCurrent A ω φ t = 0 ∧ 0 < lcCharge A ω φ t

/-- [definition] The lifted phase in turns, counted from the section:
`θ(t) = (ωt + φ + π/2)/(2π)`. -/
def liftedPhase (ω φ t : ℝ) : ℝ := (ω * t + φ + π / 2) / (2 * π)

/-- [definition] The time of the `k`-th upward zero, where `ωt + φ = −π/2 + 2πk`. -/
def crossingTime (ω φ : ℝ) (k : ℤ) : ℝ := (2 * π * k - π / 2 - φ) / ω

/-- [definition] The upward zeros in `(t₀, t₁]`. -/
def upwardZerosIn (A ω φ t₀ t₁ : ℝ) : Set ℝ :=
  {t | t₀ < t ∧ t ≤ t₁ ∧ IsUpwardZero A ω φ t}

/-- [definition] The crossing times indexed by the windings completed in `(t₀, t₁]`. -/
def crossingTimesIn (ω φ t₀ t₁ : ℝ) : Finset ℝ :=
  (Finset.Ioc ⌊liftedPhase ω φ t₀⌋ ⌊liftedPhase ω φ t₁⌋).image (crossingTime ω φ)

/-- [definition] The oscillator's phase carrier read from the section, `e^{2πiθ(t)}`. -/
def oscillatorCarrier (ω φ t : ℝ) : ℂ := phaseCarrier (2 * π * liftedPhase ω φ t)

/-- [proved-standard; formal-checked] `2π θ(t) = ωt + φ + π/2`. -/
theorem two_pi_mul_liftedPhase (ω φ t : ℝ) :
    2 * π * liftedPhase ω φ t = ω * t + φ + π / 2 := by
  have := Real.pi_pos
  unfold liftedPhase
  field_simp

/-- [proved-standard; formal-checked] The charge in the lifted angle: `A cos(ψ − π/2) = A sin ψ`. -/
theorem lcCharge_eq_sin (A ω φ t : ℝ) :
    lcCharge A ω φ t = A * Real.sin (ω * t + φ + π / 2) := by
  have h := Real.cos_sub_pi_div_two (ω * t + φ + π / 2)
  rw [add_sub_cancel_right] at h
  rw [lcCharge, h]

/-- [proved-standard; formal-checked] The rate in the lifted angle: `ẋ = Aω cos ψ`. -/
theorem lcCurrent_eq_cos (A ω φ t : ℝ) :
    lcCurrent A ω φ t = A * ω * Real.cos (ω * t + φ + π / 2) := by
  have h := Real.sin_sub_pi_div_two (ω * t + φ + π / 2)
  rw [add_sub_cancel_right] at h
  rw [lcCurrent, h]
  ring

/-- [proved-standard; formal-checked] A zero sine with a positive cosine is a whole turn. -/
theorem sin_eq_zero_and_cos_pos_iff (ψ : ℝ) :
    (Real.sin ψ = 0 ∧ 0 < Real.cos ψ) ↔ Real.cos ψ = 1 := by
  constructor
  · rintro ⟨hs, hc⟩
    have h := Real.sin_sq_add_cos_sq ψ
    rw [hs] at h
    have h1 : (Real.cos ψ - 1) * (Real.cos ψ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · linarith
    · linarith
  · intro hc
    have h := Real.sin_sq_add_cos_sq ψ
    rw [hc] at h
    have hs : Real.sin ψ ^ 2 = 0 := by linarith
    exact ⟨pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hs, by rw [hc]; norm_num⟩

/-- [proved-standard; formal-checked] `t` is an upward zero iff `cos(ωt + φ + π/2) = 1`. -/
theorem isUpwardZero_iff_cos (hA : 0 < A) (hω : 0 < ω) :
    IsUpwardZero A ω φ t ↔ Real.cos (ω * t + φ + π / 2) = 1 := by
  unfold IsUpwardZero
  rw [lcCharge_eq_sin, lcCurrent_eq_cos, ← sin_eq_zero_and_cos_pos_iff]
  have hAω : 0 < A * ω := mul_pos hA hω
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_eq_zero.mp h1).resolve_left hA.ne', pos_of_mul_pos_right h2 hAω.le⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [h1, mul_zero], mul_pos hAω h2⟩

/-- [proved-standard; formal-checked] **The upward zeros:** `ωt + φ = −π/2 + 2πk`, `k ∈ ℤ`. -/
theorem isUpwardZero_iff (hA : 0 < A) (hω : 0 < ω) :
    IsUpwardZero A ω φ t ↔ ∃ k : ℤ, ω * t + φ = -(π / 2) + 2 * π * k := by
  rw [isUpwardZero_iff_cos hA hω, Real.cos_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linear_combination -hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linear_combination -hk⟩

/-- [proved-standard; formal-checked] `t` is an upward zero iff its lifted phase is an integer. -/
theorem isUpwardZero_iff_liftedPhase (hA : 0 < A) (hω : 0 < ω) :
    IsUpwardZero A ω φ t ↔ ∃ k : ℤ, liftedPhase ω φ t = k := by
  rw [isUpwardZero_iff_cos hA hω, Real.cos_eq_one_iff]
  have hπ : (2 * π) ≠ 0 := by positivity
  unfold liftedPhase
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [div_eq_iff hπ]; linarith⟩
  · rintro ⟨k, hk⟩
    rw [div_eq_iff hπ] at hk
    exact ⟨k, by linarith⟩

/-- [proved-standard; formal-checked] **Each crossing is transversal:** the rate there is `Aω`. -/
theorem lcCurrent_of_isUpwardZero (hA : 0 < A) (hω : 0 < ω) (h : IsUpwardZero A ω φ t) :
    lcCurrent A ω φ t = A * ω := by
  rw [lcCurrent_eq_cos, (isUpwardZero_iff_cos hA hω).mp h, mul_one]

/-- [proved-standard; formal-checked] At a crossing the charge has derivative `Aω > 0`. -/
theorem hasDerivAt_of_isUpwardZero (hA : 0 < A) (hω : 0 < ω) (h : IsUpwardZero A ω φ t) :
    HasDerivAt (lcCharge A ω φ) (A * ω) t := by
  rw [← lcCurrent_of_isUpwardZero hA hω h]
  exact hasDerivAt_lcCharge A ω φ t

/-- [proved-standard; formal-checked] **The crest is the quarter-turn shift** of the upward zero:
`φ ↦ φ − π/2`. -/
theorem isCrest_iff_isUpwardZero_shift (hA : 0 < A) (hω : 0 < ω) :
    IsCrest A ω φ t ↔ IsUpwardZero A ω (φ - π / 2) t := by
  unfold IsCrest IsUpwardZero lcCharge lcCurrent
  rw [show ω * t + (φ - π / 2) = (ω * t + φ) - π / 2 by ring, Real.cos_sub_pi_div_two,
    Real.sin_sub_pi_div_two]
  have hAω : 0 < A * ω := mul_pos hA hω
  constructor
  · rintro ⟨h1, h2⟩
    have hs : Real.sin (ω * t + φ) = 0 := by
      have h3 : A * ω * Real.sin (ω * t + φ) = 0 := by linarith
      exact (mul_eq_zero.mp h3).resolve_left hAω.ne'
    have hc : 0 < Real.cos (ω * t + φ) := pos_of_mul_pos_right h2 hA.le
    refine ⟨by rw [hs, mul_zero], ?_⟩
    have := mul_pos hAω hc
    linarith
  · rintro ⟨h1, h2⟩
    have hs : Real.sin (ω * t + φ) = 0 := (mul_eq_zero.mp h1).resolve_left hA.ne'
    have hc : 0 < Real.cos (ω * t + φ) := pos_of_mul_pos_right (by linarith) hAω.le
    exact ⟨by rw [hs, mul_zero, neg_zero], mul_pos hA hc⟩

/-- [proved-standard; formal-checked] The crests: `ωt + φ = 2πk`, `k ∈ ℤ`. -/
theorem isCrest_iff (hA : 0 < A) (hω : 0 < ω) :
    IsCrest A ω φ t ↔ ∃ k : ℤ, ω * t + φ = 2 * π * k := by
  rw [isCrest_iff_isUpwardZero_shift hA hω, isUpwardZero_iff hA hω]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩

/-- [proved-standard; formal-checked] The lifted phase is strictly increasing in time. -/
theorem liftedPhase_strictMono (hω : 0 < ω) (φ : ℝ) : StrictMono (liftedPhase ω φ) := by
  intro s u hsu
  unfold liftedPhase
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  have := mul_lt_mul_of_pos_left hsu hω
  linarith

/-- [proved-standard; formal-checked] The `k`-th crossing time has lifted phase `k`. -/
theorem liftedPhase_crossingTime (hω : ω ≠ 0) (φ : ℝ) (k : ℤ) :
    liftedPhase ω φ (crossingTime ω φ k) = k := by
  have := Real.pi_pos
  unfold liftedPhase crossingTime
  field_simp
  ring

/-- [proved-standard; formal-checked] Distinct windings give distinct crossing times. -/
theorem crossingTime_injective (hω : ω ≠ 0) (φ : ℝ) : Function.Injective (crossingTime ω φ) := by
  intro j k h
  have h' := congrArg (liftedPhase ω φ) h
  rw [liftedPhase_crossingTime hω, liftedPhase_crossingTime hω] at h'
  exact_mod_cast h'

/-- [proved-standard; formal-checked] The upward zeros are the crossing times `t_k`, `k ∈ ℤ`. -/
theorem isUpwardZero_iff_crossingTime (hA : 0 < A) (hω : 0 < ω) :
    IsUpwardZero A ω φ t ↔ ∃ k : ℤ, crossingTime ω φ k = t := by
  rw [isUpwardZero_iff_liftedPhase hA hω]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, (liftedPhase_strictMono hω φ).injective ?_⟩
    rw [liftedPhase_crossingTime hω.ne', hk]
  · rintro ⟨k, rfl⟩
    exact ⟨k, liftedPhase_crossingTime hω.ne' φ k⟩

/-- [proved-standard; formal-checked] The crossings in `(t₀, t₁]` are the crossing times indexed
by the integers in `(⌊θ(t₀)⌋, ⌊θ(t₁)⌋]`. -/
theorem upwardZerosIn_eq (hA : 0 < A) (hω : 0 < ω) (t₀ t₁ : ℝ) :
    upwardZerosIn A ω φ t₀ t₁ = ↑(crossingTimesIn ω φ t₀ t₁) := by
  have hmono := liftedPhase_strictMono hω φ
  ext s
  simp only [upwardZerosIn, crossingTimesIn, Set.mem_ofPred_eq, Finset.coe_image, Set.mem_image,
    Finset.mem_coe, Finset.mem_Ioc]
  rw [isUpwardZero_iff_crossingTime hA hω]
  constructor
  · rintro ⟨h0, h1, k, rfl⟩
    have hk := liftedPhase_crossingTime hω.ne' φ k
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rw [Int.floor_lt, ← hk]
      exact hmono h0
    · rw [Int.le_floor, ← hk]
      exact hmono.monotone h1
  · rintro ⟨k, ⟨h0, h1⟩, rfl⟩
    have hk := liftedPhase_crossingTime hω.ne' φ k
    rw [Int.floor_lt, ← hk] at h0
    rw [Int.le_floor, ← hk] at h1
    exact ⟨hmono.lt_iff_lt.mp h0, hmono.le_iff_le.mp h1, k, rfl⟩

/-- [proved-standard; formal-checked] The enumeration has `⌊θ(t₁)⌋ − ⌊θ(t₀)⌋` elements. -/
theorem card_crossingTimesIn (hω : 0 < ω) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
    ((crossingTimesIn ω φ t₀ t₁).card : ℤ) = ⌊liftedPhase ω φ t₁⌋ - ⌊liftedPhase ω φ t₀⌋ := by
  unfold crossingTimesIn
  rw [Finset.card_image_of_injective _ (crossingTime_injective hω.ne' φ), Int.card_Ioc,
    Int.toNat_of_nonneg]
  exact sub_nonneg.mpr (Int.floor_le_floor ((liftedPhase_strictMono hω φ).monotone h))

/-- [proved-standard; formal-checked] **The count of crossings:** the upward zeros in `(t₀, t₁]`
are finite and number `⌊θ(t₁)⌋ − ⌊θ(t₀)⌋`. -/
theorem upwardZerosIn_finite_ncard (hA : 0 < A) (hω : 0 < ω) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
    (upwardZerosIn A ω φ t₀ t₁).Finite ∧
      ((upwardZerosIn A ω φ t₀ t₁).ncard : ℤ) =
        ⌊liftedPhase ω φ t₁⌋ - ⌊liftedPhase ω φ t₀⌋ := by
  rw [upwardZerosIn_eq hA hω]
  exact ⟨Finset.finite_toSet _, by rw [Set.ncard_coe_finset]; exact card_crossingTimesIn hω h⟩

/-- [proved-derived; formal-checked] The count is the completed windings of the lifted phase in
the owner's chart `Aeon/Clock/Winding`. -/
theorem upwardZerosIn_ncard_eq_windings (hA : 0 < A) (hω : 0 < ω) {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) :
    ((upwardZerosIn A ω φ t₀ t₁).ncard : ℤ) =
      windings (liftedPhase ω φ t₁) - windings (liftedPhase ω φ t₀) :=
  (upwardZerosIn_finite_ncard hA hω h).2

/-- [proved-standard; formal-checked] The charge is `A` times the carrier's quadrature. -/
theorem lcCharge_eq_im (A ω φ t : ℝ) :
    lcCharge A ω φ t = A * (oscillatorCarrier ω φ t).im := by
  rw [oscillatorCarrier, phaseCarrier, Complex.exp_ofReal_mul_I_im, two_pi_mul_liftedPhase,
    lcCharge_eq_sin]

/-- [proved-standard; formal-checked] The rate is `Aω` times the carrier's in-phase part. -/
theorem lcCurrent_eq_re (A ω φ t : ℝ) :
    lcCurrent A ω φ t = A * ω * (oscillatorCarrier ω φ t).re := by
  rw [oscillatorCarrier, phaseCarrier, Complex.exp_ofReal_mul_I_re, two_pi_mul_liftedPhase,
    lcCurrent_eq_cos]

/-- [proved-standard; formal-checked] The section is where the carrier reads `1`. -/
theorem isUpwardZero_iff_carrier (hA : 0 < A) (hω : 0 < ω) :
    IsUpwardZero A ω φ t ↔ oscillatorCarrier ω φ t = 1 := by
  rw [isUpwardZero_iff_cos hA hω, ← two_pi_mul_liftedPhase]
  constructor
  · intro h
    have hs := ((sin_eq_zero_and_cos_pos_iff _).mpr h).1
    apply Complex.ext
    · rw [oscillatorCarrier, phaseCarrier, Complex.exp_ofReal_mul_I_re, h, Complex.one_re]
    · rw [oscillatorCarrier, phaseCarrier, Complex.exp_ofReal_mul_I_im, hs, Complex.one_im]
  · intro h
    have h' := congrArg Complex.re h
    rwa [oscillatorCarrier, phaseCarrier, Complex.exp_ofReal_mul_I_re, Complex.one_re] at h'

end Continuous

/-! ## 2. The micro-step ring is the sampled oscillator -/

section Sampled

variable {A ω : ℝ}

/-- [definition] The sample times, `d` micro-steps a period `2π/ω`: `t_k = t₀ + k·2π/(dω)`. -/
def sampleTime (ω t₀ : ℝ) (d k : ℕ) : ℝ := t₀ + k * (2 * π / (d * ω))

/-- [definition] The ring's start: `r = ⌊d · openPhase θ⌋`, the micro-steps completed in the open
phase. -/
def ringStart (d : ℕ) (θ : ℝ) : ℕ := ⌊(d : ℝ) * openPhase θ⌋₊

/-- [definition] The sub-step offset `δ = d · openPhase θ − r`. -/
def subStep (d : ℕ) (θ : ℝ) : ℝ := d * openPhase θ - ringStart d θ

/-- [proved-derived; formal-checked] Each sample advances the lifted phase by `1/d` of a turn. -/
theorem liftedPhase_sampleTime (hω : ω ≠ 0) {d : ℕ} (hd : d ≠ 0) (φ t₀ : ℝ) (k : ℕ) :
    liftedPhase ω φ (sampleTime ω t₀ d k) = liftedPhase ω φ t₀ + k / d := by
  have := Real.pi_pos
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  unfold liftedPhase sampleTime
  field_simp
  ring

/-- [proved-derived; formal-checked] Later samples are later in time. -/
theorem sampleTime_mono (hω : 0 < ω) (t₀ : ℝ) (d : ℕ) {j k : ℕ} (h : j ≤ k) :
    sampleTime ω t₀ d j ≤ sampleTime ω t₀ d k := by
  have := Real.pi_pos
  unfold sampleTime
  have hstep : 0 ≤ 2 * π / (d * ω) := by positivity
  have hjk : (j : ℝ) ≤ k := by exact_mod_cast h
  have := mul_le_mul_of_nonneg_right hjk hstep
  linarith

/-- [proved-derived; formal-checked] The ring starts inside its first turn: `r < d`. -/
theorem ringStart_lt {d : ℕ} (hd : 0 < d) (θ : ℝ) : ringStart d θ < d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold ringStart openPhase
  rw [Nat.floor_lt (mul_nonneg hdR.le (Int.fract_nonneg θ))]
  calc (d : ℝ) * Int.fract θ < d * 1 := mul_lt_mul_of_pos_left (Int.fract_lt_one θ) hdR
    _ = d := mul_one _

/-- [proved-derived; formal-checked] The sub-step offset is nonnegative. -/
theorem subStep_nonneg (d : ℕ) (θ : ℝ) : 0 ≤ subStep d θ := by
  unfold subStep ringStart openPhase
  have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg d) (Int.fract_nonneg θ))
  linarith

/-- [proved-derived; formal-checked] The sub-step offset is less than one micro-step. -/
theorem subStep_lt_one (d : ℕ) (θ : ℝ) : subStep d θ < 1 := by
  unfold subStep ringStart
  have := Nat.lt_floor_add_one ((d : ℝ) * openPhase θ)
  linarith

/-- [proved-derived; formal-checked] `d · openPhase θ = r + δ`. -/
theorem mul_openPhase_split (d : ℕ) (θ : ℝ) :
    (d : ℝ) * openPhase θ = ringStart d θ + subStep d θ := by
  unfold subStep
  ring

/-- [proved-derived; formal-checked] **Division with remainder under the offset:** with
`d x = r + δ`, `0 ≤ δ < 1`, `⌊x + N/d⌋ = (r + N)/d`. -/
theorem floor_add_div_of_split {x δ : ℝ} {d r : ℕ} (hd : 0 < d) (hx : (d : ℝ) * x = r + δ)
    (h0 : 0 ≤ δ) (h1 : δ < 1) (N : ℕ) : ⌊x + (N : ℝ) / d⌋ = (((r + N) / d : ℕ) : ℤ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqs := Nat.div_add_mod (r + N) d
  have hlt := Nat.mod_lt (r + N) hd
  generalize (r + N) / d = q at hqs ⊢
  generalize (r + N) % d = s at hqs hlt
  have hqsR : (d : ℝ) * q + s = r + N := by exact_mod_cast hqs
  have hsR : (s : ℝ) + 1 ≤ d := by exact_mod_cast hlt
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have hxN : x + (N : ℝ) / d = ((r : ℝ) + δ + N) / d := by
    field_simp
    linarith
  rw [Int.floor_eq_iff, Int.cast_natCast, hxN, le_div_iff₀ hdR, div_lt_iff₀ hdR]
  constructor
  · nlinarith
  · nlinarith

/-- [proved-derived; formal-checked] **The ring's completed turns are the completed windings:**
`⌊θ(t_N)⌋ = ⌊θ(t₀)⌋ + (r + N)/d`. -/
theorem floor_liftedPhase_sampleTime (hω : ω ≠ 0) {d : ℕ} (hd : 0 < d) (φ t₀ : ℝ) (N : ℕ) :
    ⌊liftedPhase ω φ (sampleTime ω t₀ d N)⌋ =
      ⌊liftedPhase ω φ t₀⌋ + (((ringStart d (liftedPhase ω φ t₀) + N) / d : ℕ) : ℤ) := by
  rw [liftedPhase_sampleTime hω hd.ne']
  have hθ : liftedPhase ω φ t₀ + (N : ℝ) / d =
      (openPhase (liftedPhase ω φ t₀) + (N : ℝ) / d) + (⌊liftedPhase ω φ t₀⌋ : ℝ) := by
    have := Int.floor_add_fract (liftedPhase ω φ t₀)
    unfold openPhase
    linarith
  rw [hθ, Int.floor_add_intCast,
    floor_add_div_of_split hd (mul_openPhase_split d _) (subStep_nonneg d _)
      (subStep_lt_one d _) N, add_comm]

/-- [proved-derived; formal-checked] **The ring's micro-state is the sampled phase's completed
micro-steps:** `⌊d θ(t_k)⌋ = d ⌊θ(t₀)⌋ + (r + k)`. -/
theorem floor_mul_liftedPhase_sampleTime (hω : ω ≠ 0) {d : ℕ} (hd : 0 < d) (φ t₀ : ℝ) (k : ℕ) :
    ⌊(d : ℝ) * liftedPhase ω φ (sampleTime ω t₀ d k)⌋ =
      d * ⌊liftedPhase ω φ t₀⌋ + ((ringStart d (liftedPhase ω φ t₀) + k : ℕ) : ℤ) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [liftedPhase_sampleTime hω hd.ne']
  have hsplit := mul_openPhase_split d (liftedPhase ω φ t₀)
  have hθ := Int.floor_add_fract (liftedPhase ω φ t₀)
  have h0 := subStep_nonneg d (liftedPhase ω φ t₀)
  have h1 := subStep_lt_one d (liftedPhase ω φ t₀)
  unfold openPhase at hsplit
  have hexp : (d : ℝ) * (liftedPhase ω φ t₀ + k / d) =
      d * ⌊liftedPhase ω φ t₀⌋ + ringStart d (liftedPhase ω φ t₀) +
        subStep d (liftedPhase ω φ t₀) + k := by
    have hk : (d : ℝ) * (liftedPhase ω φ t₀ + k / d) = d * liftedPhase ω φ t₀ + k := by
      field_simp
    rw [hk]
    linear_combination (-(d : ℝ)) * hθ + hsplit
  rw [Int.floor_eq_iff, hexp]
  push_cast
  constructor
  · linarith
  · linarith

/-- [proved-derived; formal-checked] **The continuous crossings over `N` micro-steps are the
ring's:** `#(t₀, t_N] = ringCrossings d r N = (r + N)/d`, for every `φ` and `t₀`. -/
theorem upwardZeros_sampled_ncard (hA : 0 < A) (hω : 0 < ω) {d : ℕ} (hd : 0 < d) (φ t₀ : ℝ)
    (N : ℕ) :
    (upwardZerosIn A ω φ t₀ (sampleTime ω t₀ d N)).ncard =
      ringCrossings d (ringStart d (liftedPhase ω φ t₀)) N := by
  have hle : t₀ ≤ sampleTime ω t₀ d N := by
    simpa [sampleTime] using sampleTime_mono hω t₀ d (Nat.zero_le N)
  have h := (upwardZerosIn_finite_ncard (φ := φ) hA hω hle).2
  rw [floor_liftedPhase_sampleTime hω.ne' hd, add_sub_cancel_left] at h
  rw [ringCrossings_eq _ _ (ringStart_lt hd _)]
  exact_mod_cast h

/-- [proved-derived; formal-checked] The count does not see the sub-step offset: two starts with
one ring start count alike over every number of micro-steps. -/
theorem sampled_ncard_eq_of_ringStart_eq (hA : 0 < A) (hω : 0 < ω) {d : ℕ} (hd : 0 < d)
    {φ φ' t₀ t₀' : ℝ}
    (h : ringStart d (liftedPhase ω φ t₀) = ringStart d (liftedPhase ω φ' t₀')) (N : ℕ) :
    (upwardZerosIn A ω φ t₀ (sampleTime ω t₀ d N)).ncard =
      (upwardZerosIn A ω φ' t₀' (sampleTime ω t₀' d N)).ncard := by
  rw [upwardZeros_sampled_ncard hA hω hd, upwardZeros_sampled_ncard hA hω hd, h]

/-- [proved-derived; formal-checked] **One micro-step holds one crossing or none:** one when the
ring's micro-step from `r + k` lands on the section, `(r + k + 1) % d = 0`, and none otherwise. -/
theorem microStep_ncard (hA : 0 < A) (hω : 0 < ω) {d : ℕ} (hd : 0 < d) (φ t₀ : ℝ) (k : ℕ) :
    (upwardZerosIn A ω φ (sampleTime ω t₀ d k) (sampleTime ω t₀ d (k + 1))).ncard =
      if (ringStart d (liftedPhase ω φ t₀) + k + 1) % d = 0 then 1 else 0 := by
  have hle := sampleTime_mono hω t₀ d (Nat.le_add_right k 1)
  have h := (upwardZerosIn_finite_ncard (φ := φ) hA hω hle).2
  rw [floor_liftedPhase_sampleTime hω.ne' hd, floor_liftedPhase_sampleTime hω.ne' hd] at h
  generalize (upwardZerosIn A ω φ (sampleTime ω t₀ d k) (sampleTime ω t₀ d (k + 1))).ncard = n
    at h ⊢
  generalize ringStart d (liftedPhase ω φ t₀) = r at h ⊢
  rw [← add_assoc, Nat.succ_div] at h
  by_cases hm : (r + k + 1) % d = 0
  · rw [if_pos hm]
    rw [if_pos (Nat.dvd_of_mod_eq_zero hm)] at h
    push_cast at h
    have h' : (n : ℤ) = 1 := by linarith
    exact_mod_cast h'
  · rw [if_neg hm]
    rw [if_neg (fun hdvd => hm (Nat.mod_eq_zero_of_dvd hdvd))] at h
    push_cast at h
    have h' : (n : ℤ) = 0 := by linarith
    exact_mod_cast h'

variable {ClockAddress : Type*}

/-- [proved-derived; formal-checked] **For `d ≥ 2` a micro-step's crossing is the owner's
`Crossing`:** the micro-step `(t_k, t_(k+1)]` holds one crossing iff a `Crossing` of
`ringOscillator` starts at `r + k`, and none iff no `Crossing` starts there. -/
theorem microStep_crossing_iff_ownerCrossing (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (hA : 0 < A) (hω : 0 < ω) (φ t₀ : ℝ) (k : ℕ) :
    ((upwardZerosIn A ω φ (sampleTime ω t₀ passage.denominator k)
        (sampleTime ω t₀ passage.denominator (k + 1))).ncard = 1 ↔
      ∃ c : (ringOscillator passage).Crossing,
        c.source = ringStart passage.denominator (liftedPhase ω φ t₀) + k) ∧
    ((upwardZerosIn A ω φ (sampleTime ω t₀ passage.denominator k)
        (sampleTime ω t₀ passage.denominator (k + 1))).ncard = 0 ↔
      ¬ ∃ c : (ringOscillator passage).Crossing,
        c.source = ringStart passage.denominator (liftedPhase ω φ t₀) + k) := by
  rw [microStep_ncard hA hω (by omega) φ t₀ k, ringCrossing_iff passage hd]
  by_cases hm : (ringStart passage.denominator (liftedPhase ω φ t₀) + k + 1) %
      passage.denominator = 0
  · simp [hm]
  · simp [hm]

/-- [proved-derived; formal-checked] At `d = 1` every micro-step holds one continuous crossing,
where the owner's ring has no `Crossing` (`no_crossing_of_denominator_one`). -/
theorem microStep_ncard_denominator_one (hA : 0 < A) (hω : 0 < ω) (φ t₀ : ℝ) (k : ℕ) :
    (upwardZerosIn A ω φ (sampleTime ω t₀ 1 k) (sampleTime ω t₀ 1 (k + 1))).ncard = 1 := by
  rw [microStep_ncard hA hω one_pos, if_pos (Nat.mod_one _)]

end Sampled

/-! ## 3. Joined to the clock passage -/

section Passage

variable {A ω : ℝ} {ClockAddress : Type*}

/-- [proved-derived; formal-checked] **The sampled oscillator crosses `targetTicks r k` times**
over `n·k` micro-steps of a rational clock passage `n/d`. -/
theorem sampled_crossings_eq_targetTicks (passage : RationalClockPassage ClockAddress)
    (hA : 0 < A) (hω : 0 < ω) (φ t₀ : ℝ) (k : ℕ) :
    (upwardZerosIn A ω φ t₀
        (sampleTime ω t₀ passage.denominator (passage.numerator * k))).ncard =
      passage.targetTicks (ringStart passage.denominator (liftedPhase ω φ t₀)) k := by
  rw [upwardZeros_sampled_ncard hA hω passage.denominator_pos,
    ringCrossings_eq _ _ (ringStart_lt passage.denominator_pos _)]
  rfl

/-- [proved-derived; formal-checked] For `d ≥ 2` the continuous crossings are the owner's count of
`Crossing` records. -/
theorem sampled_crossings_eq_ownerCrossings (passage : RationalClockPassage ClockAddress)
    (hd : 2 ≤ passage.denominator) (hA : 0 < A) (hω : 0 < ω) (φ t₀ : ℝ) (k : ℕ) :
    (upwardZerosIn A ω φ t₀
        (sampleTime ω t₀ passage.denominator (passage.numerator * k))).ncard =
      ownerCrossings passage (ringStart passage.denominator (liftedPhase ω φ t₀))
        (passage.numerator * k) := by
  rw [sampled_crossings_eq_targetTicks passage hA hω,
    (ownerCrossings_eq_targetTicks passage hd _ k (ringStart_lt passage.denominator_pos _)).1]

/-- [proved-standard; formal-checked] The carrier turns additively. -/
theorem phaseCarrier_add (a b : ℝ) : phaseCarrier (a + b) = phaseCarrier a * phaseCarrier b := by
  unfold phaseCarrier
  push_cast
  rw [add_mul, Complex.exp_add]

/-- [proved-standard; formal-checked] Whole turns, of either orientation, are invisible to the
carrier. -/
theorem phaseCarrier_add_int_turns (a : ℝ) (m : ℤ) :
    phaseCarrier (a + 2 * π * m) = phaseCarrier a := by
  rw [phaseCarrier_add]
  have h : ((2 * π * m : ℝ) : ℂ) * Complex.I = m * (2 * π * Complex.I) := by
    push_cast
    ring
  change phaseCarrier a * Complex.exp (((2 * π * m : ℝ) : ℂ) * Complex.I) = phaseCarrier a
  rw [h, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- [proved-derived; formal-checked] The phase split at a sample: with `θ = m + (r + δ)/d`,
`2π(θ + N/d) = 2π(r + N)/d + 2πδ/d + 2πm`. -/
theorem two_pi_split {θ δ : ℝ} {m : ℤ} {d r : ℕ} (hd : (d : ℝ) ≠ 0)
    (hθ : θ = m + (r + δ) / d) (N : ℕ) :
    2 * π * (θ + N / d) =
      (2 * π * ((r + N : ℕ) : ℝ) / d + 2 * π * δ / d) + 2 * π * m := by
  subst hθ
  push_cast
  field_simp
  ring

/-- [proved-derived; formal-checked] **The carrier at a sample** is the ring's phase at `r + N`
advanced by the offset: `e^{2πiθ(t_N)} = e^{2πi(r + N)/d} · e^{2πiδ/d}`. -/
theorem oscillatorCarrier_sampleTime (hω : ω ≠ 0) {d : ℕ} (hd : 0 < d) (φ t₀ : ℝ) (N : ℕ) :
    oscillatorCarrier ω φ (sampleTime ω t₀ d N) =
      phaseCarrier (2 * π * ((ringStart d (liftedPhase ω φ t₀) + N : ℕ) : ℝ) / d) *
        phaseCarrier (2 * π * subStep d (liftedPhase ω φ t₀) / d) := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hθ : liftedPhase ω φ t₀ = (⌊liftedPhase ω φ t₀⌋ : ℝ) +
      ((ringStart d (liftedPhase ω φ t₀) : ℝ) + subStep d (liftedPhase ω φ t₀)) / d := by
    rw [← mul_openPhase_split, mul_div_cancel_left₀ _ hdR]
    exact (Int.floor_add_fract _).symm
  unfold oscillatorCarrier
  rw [liftedPhase_sampleTime hω hd.ne', two_pi_split hdR hθ N, phaseCarrier_add_int_turns,
    phaseCarrier_add]

/-- [proved-derived; formal-checked] **The carrier at `t_(n k)` is the owner's residue phase
advanced by `2πδ/d`:** `(ringOscillator passage).phase (r + n k) · e^{2πiδ/d}`, which is
`e^{2πi · phaseResidue r k / d} · e^{2πiδ/d}`. -/
theorem sampled_carrier_eq_residuePhase (passage : RationalClockPassage ClockAddress)
    (hω : 0 < ω) (φ t₀ : ℝ) (k : ℕ) :
    oscillatorCarrier ω φ (sampleTime ω t₀ passage.denominator (passage.numerator * k)) =
        (ringOscillator passage).phase
            (ringStart passage.denominator (liftedPhase ω φ t₀) + passage.numerator * k) *
          phaseCarrier (2 * π * subStep passage.denominator (liftedPhase ω φ t₀) /
            passage.denominator) ∧
      oscillatorCarrier ω φ (sampleTime ω t₀ passage.denominator (passage.numerator * k)) =
        phaseCarrier (2 * π *
            (passage.phaseResidue (ringStart passage.denominator (liftedPhase ω φ t₀)) k : ℝ) /
              passage.denominator) *
          phaseCarrier (2 * π * subStep passage.denominator (liftedPhase ω φ t₀) /
            passage.denominator) := by
  have h1 := oscillatorCarrier_sampleTime (φ := φ) (t₀ := t₀) hω.ne' passage.denominator_pos
    (passage.numerator * k)
  refine ⟨h1, ?_⟩
  rw [← ringPhase_eq_residuePhase passage]
  exact h1

end Passage

/-! ## 4. Witnesses -/

section Witness

variable {A ω : ℝ}

/-- [proved-derived; formal-checked] At `φ = −π/2`, `t₀ = 0` the lifted phase starts at `0`. -/
theorem liftedPhase_quarter_zero (ω : ℝ) : liftedPhase ω (-(π / 2)) 0 = 0 := by
  unfold liftedPhase
  ring_nf

/-- [proved-derived; formal-checked] Nine quarter-period samples from `0` end at `9·2π/(4ω)`. -/
theorem sampleTime_four_nine (ω : ℝ) : sampleTime ω 0 4 9 = 9 * (2 * π / (4 * ω)) := by
  simp [sampleTime]

/-- [proved-derived; formal-checked] **The three-quarter passage read from the continuous
oscillator:** `φ = −π/2`, `t₀ = 0`, `d = 4`: `r = 0`, `δ = 0`, two crossings in `(0, 9·2π/(4ω)]`,
equal to the owner's `ownerCrossings threeQuarterPassage 0 9`, and carrier `i` at the end. -/
theorem threeQuarter_continuous_witness (hA : 0 < A) (hω : 0 < ω) :
    ringStart 4 (liftedPhase ω (-(π / 2)) 0) = 0 ∧ subStep 4 (liftedPhase ω (-(π / 2)) 0) = 0 ∧
      (upwardZerosIn A ω (-(π / 2)) 0 (9 * (2 * π / (4 * ω)))).ncard = 2 ∧
      (upwardZerosIn A ω (-(π / 2)) 0 (9 * (2 * π / (4 * ω)))).ncard =
        ownerCrossings threeQuarterPassage 0 (3 * 3) ∧
      oscillatorCarrier ω (-(π / 2)) (9 * (2 * π / (4 * ω))) = Complex.I := by
  have hr : ringStart 4 (liftedPhase ω (-(π / 2)) 0) = 0 := by
    rw [liftedPhase_quarter_zero]
    simp [ringStart, openPhase]
  have hδ : subStep 4 (liftedPhase ω (-(π / 2)) 0) = 0 := by
    rw [subStep, hr, liftedPhase_quarter_zero]
    simp [openPhase]
  have hcount : (upwardZerosIn A ω (-(π / 2)) 0 (9 * (2 * π / (4 * ω)))).ncard = 2 := by
    rw [← sampleTime_four_nine, upwardZeros_sampled_ncard hA hω (by norm_num), hr,
      ringCrossings_eq _ _ (by norm_num)]
  refine ⟨hr, hδ, hcount, ?_, ?_⟩
  · rw [hcount, threeQuarter_witness.1]
  · have h := (sampled_carrier_eq_residuePhase threeQuarterPassage hω (-(π / 2)) 0 3).1
    have ht : sampleTime ω 0 threeQuarterPassage.denominator (threeQuarterPassage.numerator * 3) =
        9 * (2 * π / (4 * ω)) := sampleTime_four_nine ω
    have hden : threeQuarterPassage.denominator = 4 := rfl
    have hnum : threeQuarterPassage.numerator = 3 := rfl
    rw [ht, hden, hnum, hr, hδ] at h
    rw [h, threeQuarter_witness.2.2.2.1]
    simp [phaseCarrier]

/-- [proved-derived; formal-checked] **A start inside a micro-step counts alike:** `φ = −π/4`,
`t₀ = 0`, `d = 4` give `θ(0) = 1/8`, `r = 0`, `δ = 1/2 ≠ 0`, the same two crossings in
`(0, 9·2π/(4ω)]`, and carrier `i · e^{iπ/4}` at the end. -/
theorem threeQuarter_offset_witness (hA : 0 < A) (hω : 0 < ω) :
    liftedPhase ω (-(π / 4)) 0 = 1 / 8 ∧ ringStart 4 (1 / 8) = 0 ∧ subStep 4 (1 / 8) = 1 / 2 ∧
      (upwardZerosIn A ω (-(π / 4)) 0 (9 * (2 * π / (4 * ω)))).ncard = 2 ∧
      oscillatorCarrier ω (-(π / 4)) (9 * (2 * π / (4 * ω))) =
        Complex.I * phaseCarrier (π / 4) := by
  have hθ : liftedPhase ω (-(π / 4)) 0 = 1 / 8 := by
    have := Real.pi_pos
    unfold liftedPhase
    field_simp
    ring
  have hfr : openPhase (1 / 8 : ℝ) = 1 / 8 := by
    unfold openPhase
    rw [Int.fract_eq_self]
    norm_num
  have hr : ringStart 4 (1 / 8) = 0 := by
    unfold ringStart
    rw [hfr, Nat.floor_eq_zero]
    norm_num
  have hδ : subStep 4 (1 / 8) = 1 / 2 := by
    rw [subStep, hr, hfr]
    norm_num
  refine ⟨hθ, hr, hδ, ?_, ?_⟩
  · rw [← sampleTime_four_nine, upwardZeros_sampled_ncard hA hω (by norm_num), hθ, hr,
      ringCrossings_eq _ _ (by norm_num)]
  · have h := (sampled_carrier_eq_residuePhase threeQuarterPassage hω (-(π / 4)) 0 3).1
    have ht : sampleTime ω 0 threeQuarterPassage.denominator (threeQuarterPassage.numerator * 3) =
        9 * (2 * π / (4 * ω)) := sampleTime_four_nine ω
    have hden : threeQuarterPassage.denominator = 4 := rfl
    have hnum : threeQuarterPassage.numerator = 3 := rfl
    rw [ht, hden, hnum, hθ, hr, hδ] at h
    rw [h, threeQuarter_witness.2.2.2.1]
    congr 2
    ring

end Witness

end Holonics.Objects.ContinuousCrossing

import HolonicsResearch.Zeta.FosterTanks

/-!
# The Foster return: a zero's tank is a lossless one-port, and the comb is their series port

The box of #410: "The Foster return: `flux_eq_tankSum` (`Zeta/FosterTanks`) as a
contact-form/receiver construction, with sign, frequency, frame and clock normalization."

The owner `Zeta/FosterTanks` proves the tank algebra over `ℂ` and closes its opening paragraph on
"RH is Foster's reactance theorem for this one function: every tank has positive inductance."
This module builds the circuit behind that algebra. A tank is a storage element with a port whose
flow/effort pairing is power (the Holon's ports and storage elements); its response to a Laplace
mode is the owner's `tank`; the comb is the series interconnection of its tanks, read by a
receiver at the one port; and the normalizations (frame `w = z − ½`, frequency `(LC)^{−1/2}`,
clock `2π/γ`, sign `Re ≥ 0`) are the ones that make the owner's identities readings of it.

Sources: the box above; the owner's opening paragraph and the record
`research/records/2026-09-03_FT0_THE_ZEROS_ARE_FOSTER_TANKS_AND_THE_PAIRED_LANDAU_FORM_CARRIES_THE_REMAINDER.md`;
the atlas rows `rh.foster-pair-tank`, `rh.foster-inductance-seam`, `rh.foster-seam-resonance`,
`rh.foster-paired-flux`, `rh.zero-pair-lock-foster`, `rh.foster-tank-site` (the tank as the site
`companion(0, −ρ′²)` of `Landmarks/ZeroPairSite`) and `parametron.lc-exchange` (the storage↔flow
exchange of `Objects/Parametron`, item 1).

## What is proved

1. **The tank as a one-port (the contact form).** [proved-standard; formal-checked] A parallel LC
   tank (`IsTankSolution`: `C v̇ = i − i_L`, `L i̇_L = v`, port current `i`) has stored energy
   `H = ½Cv² + ½L i_L²` (`tankEnergy`) with `Ḣ = v·i` along every solution (`tank_power_balance`):
   effort times flow at the port, no dissipation. For `C, L ≥ 0` the storage is nonnegative
   (`tankEnergy_nonneg`).
2. **Its impedance is the tank (frame normalization).** [proved-standard; formal-checked] The
   Laplace mode `t ↦ A e^{wt}` (`mode`, `mode_hasDerivAt`) solves the tank's equations iff its
   amplitudes satisfy `C w V̂ = Î − Î_L`, `L w Î_L = V̂` (`mode_solution_iff`); with
   `w²LC + 1 ≠ 0` this gives `V̂ = Z(w) Î`, `Z(w) = wL/(w²LC + 1)` (`parallelImpedance`,
   `mode_response`), and the mode with that amplitude is a solution (`mode_solves`). For the
   amplitudes' power pairing, `Re(V̂ Î*) = Re Z · |Î|²` (`mode_power`): the sign of `Re Z` is the
   sign of that pairing at the port. [proved-derived; formal-checked] At the owner's `C = ½`,
   `L = −2/ρ′²` the impedance is `tank ρ′ w` (`parallelImpedance_seam_frame`, from
   `tank_eq_parallel_LC`); a reflection pair is one such impedance in the seam's frame
   `w = z − ½` (`pair_eq_impedance`, `tank_eq_pair_centred`, from `pair_eq_tank`); the frame moves
   the comb by `−½` and keeps its flux (`flux_frame`); and the owner's `flux_eq_tankSum` reads as
   the comb's flux at `z` being a sum of half-weighted tank impedances at `w`
   (`flux_eq_series_impedance`).
3. **Frequency and clock normalization.** [proved-standard; formal-checked] With the port open the
   tank rings: `v = cos(γt)`, `i_L = Cγ sin(γt)` solve it when `LCγ² = 1` (`free_oscillation`),
   with constant energy `C/2` (`free_energy`), at `γ = (LC)^{−1/2}` (`resonance_rate`), with
   period `2π/γ` (`free_period`). An undriven Laplace mode exists exactly at a pole,
   `w²LC + 1 = 0` (`free_mode_iff_pole`). [proved-derived; formal-checked] The owner's tank of
   `ρ′ ≠ 0` has its poles exactly at `w = ±ρ′` (`tank_pole_iff`), and at the seam `ρ′ = iγ`,
   `γ > 0`, the real tank `C = ½`, `L = 2/γ²` rings as `cos(γt)` with period `2π/γ`, its poles at
   `±iγ` (`seam_clock`): the height of a zero is the tank's clock rate.
4. **Sign normalization: positivity is the seam (finite Foster theorem).** [proved-standard;
   formal-checked] For `Re u > 0`, `Re(1/u) > 0` (`re_one_div_pos`). A tank whose zero is on the
   seam is positive real: `Re tank(ρ′, w) > 0` on `Re w > 0` when `Re ρ′ = 0`
   (`re_tank_pos_of_seam`, `re_seam_tank_pos` for `ρ′ = iγ`), and real on the real axis
   (`seam_tank_real`). A comb on the seam has `Re ≥ 0` on `Re w > 0`
   (`combFlux_re_nonneg_of_seam`), and `> 0` when it is nonempty with multiplicities `≥ 1`
   (`combFlux_re_pos_of_seam`). Conversely, a positive real comb has no pole in the open right
   half-plane: along `w = a − ε`, `ε → 0⁺`, the real part of the flux goes to `−∞`
   (`no_pole_right_of_positive`). [proved-derived; formal-checked] So a finite reflection-closed
   comb (`ρ′ ∈ Z ⇒ −ρ′ ∈ Z`, multiplicities `≥ 1`) is positive real iff it lies on the seam
   (`comb_positive_real_iff_seam`), and, with `0 ∉ Z`, iff every tank has positive real inductance
   (`foster_finite`, through `inductance_pos_real_iff`); with matched multiplicities the same holds
   for the paired tank sum (`combFlux_eq_halfTankSum`, `pairedTanks_positive_real_iff_seam`).
5. **The comb as an interconnection (the receiver).** [proved-standard; formal-checked] A series
   connection of tanks (one current, voltages adding) has the sum of their storage as its storage
   (`seriesEnergy_nonneg`) and the sum of their balances as its balance,
   `Ḣ = (Σ v_j)·i` (`series_power_balance`), and the sum of their impedances as its impedance
   (`series_impedance`, `mode_sum`); scaling an impedance by `k` scales `L` by `k` and `C` by
   `1/k` (`mul_parallelImpedance`). [proved-derived; formal-checked] The element of `ρ′` with
   multiplicity `k` is the tank `C = 1/k`, `L = −k/ρ′²` (`elementCapacitance`,
   `elementInductance`, `elementInductance_eq`), whose impedance is `k w/(w² − ρ′²)`, half the
   owner's tank weighted by `k` (`element_impedance`, `element_impedance_eq_half_tank`); a
   reflection-closed comb's flux is the impedance of the series interconnection of its elements
   (`combFlux_eq_pairSum`, `combFlux_eq_series`), so a receiver driving the port with the mode
   `Î e^{wt}` reads the voltage amplitude `combFlux · Î` (`comb_receiver`). On the seam the
   elements are real tanks with `C = 1/k > 0`, `L = k/(Im ρ′)² > 0` (`seam_element_real`), so
   the real balance of item 1 applies to each and item 5's sum to the comb.
6. **Witnesses.** [proved-derived; formal-checked] The two seam tanks at `γ = 1, 2` read
   `1 + 2/5 = 7/5` at `w = 1` (`witness_seam_pair`); the off-seam pair `ρ′ = ±(¼ + i)` reads
   `tank = −2096/265 − (128/265)i` at `w = ⅛ + i`, `Re w = ⅛ > 0`, a negative real part
   (`witness_off_seam`).

## What is not claimed

The infinite comb of `ξ` (the owner's Landau remainder, the zero factorization and the Hadamard
series), RH itself, a dissipative (RLC) tank, the Cauer and Foster canonical forms of a general
reactance function, and the Herglotz representation. The converse of item 4 is read on finite
combs only; "positive real" is used for `Re ≥ 0` on `Re w > 0` away from the comb, with the
realness on the real axis proved for a single seam tank only.

## The computational object

The computational object is the helical pair interaction, read on the tank: the free ring
`(v, i_L) = (cos γt, Cγ sin γt)` turns on the energy ellipse at rate `γ`, the helix whose pitch is
the clock `2π/γ`; the port's flow/effort pairing `v·i` is the pair contact's power, and the
reflection pair `ρ′, −ρ′` is one tank; the receiver's face is `Re Z`, the power it absorbs, placed
in the seam's frame `w = z − ½`. Of the winding guide's six general objects this touches the
helix (the free ring and its period), the pair (the port pairing and the reflection pair) and
faces and placement (the receiver's reading at the series port, in the seam's frame); the cell
holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Zeta.FosterReturn

open Complex Finset Filter Topology
open Holonics.Zeta.FosterTanks

/-! ## 1. The tank as a one-port -/

/-- [definition] The stored energy of a parallel LC tank: capacitor voltage `v`, inductor current
`iL`, `H = ½Cv² + ½L iL²`. -/
def tankEnergy (C L v iL : ℝ) : ℝ := C * v ^ 2 / 2 + L * iL ^ 2 / 2

/-- [definition] A trajectory of a parallel LC tank driven at its port by the current `i`:
`C v̇ = i − i_L` (the capacitor takes the port current the inductor does not) and `L i̇_L = v`. -/
structure IsTankSolution (C L : ℝ) (v iL i : ℝ → ℝ) : Prop where
  cap : ∀ t, ∃ dv, HasDerivAt v dv t ∧ C * dv = i t - iL t
  ind : ∀ t, ∃ diL, HasDerivAt iL diL t ∧ L * diL = v t

/-- [proved-standard; formal-checked] The power balance: along a solution, `Ḣ = v·i`. -/
theorem tank_power_balance {C L : ℝ} {v iL i : ℝ → ℝ} (h : IsTankSolution C L v iL i) (t : ℝ) :
    HasDerivAt (fun s => tankEnergy C L (v s) (iL s)) (v t * i t) t := by
  obtain ⟨dv, hv, hcv⟩ := h.cap t
  obtain ⟨diL, hiL, hli⟩ := h.ind t
  have h1 := ((hv.pow 2).const_mul C).div_const 2
  have h2 := ((hiL.pow 2).const_mul L).div_const 2
  have key : HasDerivAt (fun s => tankEnergy C L (v s) (iL s)) _ t := h1.add h2
  refine key.congr_deriv ?_
  norm_num
  linear_combination (v t) * hcv + (iL t) * hli

/-- [proved-standard; formal-checked] With `C, L ≥ 0` the stored energy is nonnegative. -/
theorem tankEnergy_nonneg {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (v iL : ℝ) :
    0 ≤ tankEnergy C L v iL := by
  unfold tankEnergy
  positivity

/-! ## 2. The Laplace mode and the impedance -/

/-- [definition] The Laplace mode of amplitude `A` and rate `w`: `t ↦ A e^{wt}`. -/
def mode (A w : ℂ) (t : ℝ) : ℂ := A * exp (w * t)

/-- [proved-standard; formal-checked] The mode's derivative is `A w e^{wt}`. -/
theorem mode_hasDerivAt (A w : ℂ) (t : ℝ) : HasDerivAt (mode A w) (A * w * exp (w * t)) t := by
  have h1 : HasDerivAt (fun s : ℝ => w * (s : ℂ)) w t := by
    simpa using ((hasDerivAt_id t).ofReal_comp).const_mul w
  have h2 : HasDerivAt (fun s : ℝ => A * exp (w * s)) (A * (exp (w * t) * w)) t :=
    (h1.cexp).const_mul A
  exact h2.congr_deriv (by ring)

/-- [definition] A complex trajectory of a tank with complex constants, for reading modes. -/
structure IsComplexTankSolution (C L : ℂ) (v iL i : ℝ → ℂ) : Prop where
  cap : ∀ t, ∃ dv, HasDerivAt v dv t ∧ C * dv = i t - iL t
  ind : ∀ t, ∃ diL, HasDerivAt iL diL t ∧ L * diL = v t

/-- [proved-standard; formal-checked] Modes solve the tank iff their amplitudes satisfy the
phasor equations `C w V = J − JL`, `L w JL = V`. -/
theorem mode_solution_iff {C L w V J JL : ℂ} :
    IsComplexTankSolution C L (mode V w) (mode JL w) (mode J w) ↔
      C * (w * V) = J - JL ∧ L * (w * JL) = V := by
  constructor
  · intro h
    obtain ⟨dv, hv, hcv⟩ := h.cap 0
    obtain ⟨di, hi, hli⟩ := h.ind 0
    have e1 := hv.unique (mode_hasDerivAt V w 0)
    have e2 := hi.unique (mode_hasDerivAt JL w 0)
    simp only [mode, ofReal_zero, mul_zero, exp_zero, mul_one] at hcv hli e1 e2
    rw [e1] at hcv
    rw [e2] at hli
    constructor
    · linear_combination hcv
    · linear_combination hli
  · rintro ⟨h1, h2⟩
    refine ⟨fun t => ⟨_, mode_hasDerivAt V w t, ?_⟩, fun t => ⟨_, mode_hasDerivAt JL w t, ?_⟩⟩
    · simp only [mode]
      linear_combination exp (w * t) * h1
    · simp only [mode]
      linear_combination exp (w * t) * h2

/-- [definition] The impedance of a parallel LC tank, `Z(w) = wL/(w²LC + 1)`. -/
def parallelImpedance (C L w : ℂ) : ℂ := w * L / (w ^ 2 * L * C + 1)

/-- [proved-standard; formal-checked] The response to a mode: `V = Z(w) J`, `JL = J − C w V`. -/
theorem mode_response {C L w V J JL : ℂ}
    (h : IsComplexTankSolution C L (mode V w) (mode JL w) (mode J w))
    (hden : w ^ 2 * L * C + 1 ≠ 0) :
    V = parallelImpedance C L w * J ∧ JL = J - C * w * V := by
  obtain ⟨h1, h2⟩ := mode_solution_iff.mp h
  refine ⟨?_, by linear_combination h1⟩
  unfold parallelImpedance
  rw [div_mul_eq_mul_div, eq_div_iff hden]
  linear_combination w * L * h1 - h2

/-- [proved-standard; formal-checked] The mode of amplitude `Z(w) J` is a solution. -/
theorem mode_solves {C L w J : ℂ} (hden : w ^ 2 * L * C + 1 ≠ 0) :
    IsComplexTankSolution C L (mode (parallelImpedance C L w * J) w)
      (mode (J - C * w * (parallelImpedance C L w * J)) w) (mode J w) := by
  apply mode_solution_iff.mpr
  have hZ : parallelImpedance C L w * (w ^ 2 * L * C + 1) = w * L := by
    unfold parallelImpedance
    exact div_mul_cancel₀ _ hden
  constructor
  · ring
  · linear_combination -J * hZ

/-- [proved-standard; formal-checked] The power pairing at a mode: `Re(Z J J*) = Re Z · |J|²`. -/
theorem mode_power (Z J : ℂ) : (Z * J * (starRingEnd ℂ) J).re = Z.re * normSq J := by
  rw [mul_assoc, mul_conj, re_mul_ofReal]

/-- [proved-derived; formal-checked] At `C = ½`, `L = −2/ρ′²` the impedance is the owner's tank. -/
theorem parallelImpedance_seam_frame {ρ' w : ℂ} (hρ : ρ' ≠ 0) :
    parallelImpedance capacitance (inductance ρ') w = tank ρ' w := by
  rw [tank_eq_parallel_LC hρ]
  rfl

/-- [proved-derived; formal-checked] A reflection pair is one tank impedance in the frame
`w = z − ½`. -/
theorem pair_eq_impedance {z ρ : ℂ} (h₁ : z ≠ ρ) (h₂ : z ≠ 1 - ρ) (hρ : ρ ≠ 1 / 2) :
    1 / (z - ρ) + 1 / (z - (1 - ρ)) =
      parallelImpedance capacitance (inductance (ρ - 1 / 2)) (z - 1 / 2) := by
  rw [parallelImpedance_seam_frame (sub_ne_zero.mpr hρ)]
  exact pair_eq_tank h₁ h₂

/-- [proved-derived; formal-checked] In the centred frame the tank is the pair `±ρ′`. -/
theorem tank_eq_pair_centred {ρ' w : ℂ} (h₁ : w ≠ ρ') (h₂ : w ≠ -ρ') :
    tank ρ' w = 1 / (w - ρ') + 1 / (w + ρ') := by
  have h := pair_eq_tank (z := w + 1 / 2) (ρ := ρ' + 1 / 2)
    (fun h => h₁ (by linear_combination h)) (fun h => h₂ (by linear_combination h))
  have e1 : w + 1 / 2 - (ρ' + 1 / 2) = w - ρ' := by ring
  have e2 : w + 1 / 2 - (1 - (ρ' + 1 / 2)) = w + ρ' := by ring
  have e3 : ρ' + 1 / 2 - 1 / 2 = ρ' := by ring
  have e4 : w + 1 / 2 - 1 / 2 = w := by ring
  rw [e1, e2, e3, e4] at h
  exact h.symm

/-- [definition] The flux of a centred comb `Z` with multiplicities `m` at the centred point `w`. -/
def combFlux (Z : Finset ℂ) (m : ℂ → ℕ) (w : ℂ) : ℂ := ∑ ρ' ∈ Z, (m ρ' : ℂ) / (w - ρ')

/-- [proved-derived; formal-checked] The seam's frame moves the comb by `−½` and keeps its flux. -/
theorem flux_frame (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ) :
    ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) =
      combFlux (Z.map (Equiv.subRight (1 / 2 : ℂ)).toEmbedding) (fun ρ' => m (ρ' + 1 / 2))
        (z - 1 / 2) := by
  unfold combFlux
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro ρ _
  simp only [Equiv.coe_toEmbedding, Equiv.subRight_apply, sub_add_cancel]
  congr 1
  ring

/-- [proved-derived; formal-checked] The owner's paired flux, read as a sum of tank impedances:
each member of a pair carries half of its pair's tank. -/
theorem flux_eq_series_impedance {Z : Finset ℂ} {m : ℂ → ℕ}
    (hZ : ∀ ρ ∈ Z, 1 - ρ ∈ Z) (hm : ∀ ρ ∈ Z, m (1 - ρ) = m ρ) (hc : (1 / 2 : ℂ) ∉ Z)
    {z : ℂ} (hz : ∀ ρ ∈ Z, z ≠ ρ) :
    ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ Z, (m ρ : ℂ) / 2 *
        parallelImpedance capacitance (inductance (ρ - 1 / 2)) (z - 1 / 2) := by
  rw [flux_eq_tankSum hZ hm hz]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hρ' : ρ - 1 / 2 ≠ 0 := sub_ne_zero.mpr (fun h => hc (h ▸ hρ))
  rw [parallelImpedance_seam_frame hρ']
  unfold tank
  ring

/-! ## 3. Frequency and clock -/

/-- [proved-standard; formal-checked] With the port open the tank rings: `v = cos γt`,
`i_L = Cγ sin γt` when `LCγ² = 1`. -/
theorem free_oscillation {C L γ : ℝ} (h : L * C * γ ^ 2 = 1) :
    IsTankSolution C L (fun t => Real.cos (γ * t)) (fun t => C * γ * Real.sin (γ * t))
      (fun _ => 0) := by
  have hlin : ∀ t : ℝ, HasDerivAt (fun s : ℝ => γ * s) γ t := fun t => by
    simpa using (hasDerivAt_id t).const_mul γ
  refine ⟨fun t => ⟨_, (hlin t).cos, ?_⟩, fun t => ⟨_, ((hlin t).sin).const_mul (C * γ), ?_⟩⟩
  · ring
  · linear_combination Real.cos (γ * t) * h

/-- [proved-standard; formal-checked] The free ring keeps the energy `C/2`. -/
theorem free_energy {C L γ : ℝ} (h : L * C * γ ^ 2 = 1) (t : ℝ) :
    tankEnergy C L (Real.cos (γ * t)) (C * γ * Real.sin (γ * t)) = C / 2 := by
  unfold tankEnergy
  linear_combination (C / 2) * Real.cos_sq_add_sin_sq (γ * t) + (C * Real.sin (γ * t) ^ 2 / 2) * h

/-- [proved-standard; formal-checked] The rate `γ = (LC)^{−1/2}` satisfies `LCγ² = 1`. -/
theorem resonance_rate {C L : ℝ} (hC : 0 < C) (hL : 0 < L) :
    L * C * (1 / Real.sqrt (L * C)) ^ 2 = 1 := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- [proved-standard; formal-checked] The free ring's period is `2π/γ`. -/
theorem free_period {γ : ℝ} (hγ : γ ≠ 0) :
    Function.Periodic (fun t => Real.cos (γ * t)) (2 * Real.pi / γ) ∧
      Function.Periodic (fun t => Real.sin (γ * t)) (2 * Real.pi / γ) := by
  have e : ∀ t : ℝ, γ * (t + 2 * Real.pi / γ) = γ * t + 2 * Real.pi := fun t => by
    field_simp
  exact ⟨fun t => by simp only [e, Real.cos_add_two_pi], fun t => by simp only [e, Real.sin_add_two_pi]⟩

/-- [proved-standard; formal-checked] An undriven mode exists exactly at a pole of `Z`. -/
theorem free_mode_iff_pole {C L w : ℂ} :
    (∃ V JL : ℂ, V ≠ 0 ∧ IsComplexTankSolution C L (mode V w) (mode JL w) (mode 0 w)) ↔
      w ^ 2 * L * C + 1 = 0 := by
  constructor
  · rintro ⟨V, JL, hV, h⟩
    obtain ⟨h1, h2⟩ := mode_solution_iff.mp h
    have hz : (w ^ 2 * L * C + 1) * V = 0 := by linear_combination L * w * h1 - h2
    exact (mul_eq_zero.mp hz).resolve_right hV
  · intro hp
    exact ⟨1, -(C * w), one_ne_zero,
      mode_solution_iff.mpr ⟨by ring, by linear_combination -hp⟩⟩

/-- [proved-derived; formal-checked] The owner's tank of `ρ′ ≠ 0` has its poles at `w = ±ρ′`. -/
theorem tank_pole_iff {ρ' w : ℂ} (hρ : ρ' ≠ 0) :
    w ^ 2 * inductance ρ' * capacitance + 1 = 0 ↔ w = ρ' ∨ w = -ρ' := by
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  unfold inductance capacitance
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  have hs : w ^ 2 * (-2 / ρ' ^ 2) * (1 / 2) + 1 = (ρ' ^ 2 - w ^ 2) / ρ' ^ 2 := by
    field_simp
    ring
  rw [hs, div_eq_zero_iff, or_iff_left h2, sub_eq_zero, eq_comm]

/-- [proved-derived; formal-checked] The seam's clock: at `ρ′ = iγ` the real tank `C = ½`,
`L = 2/γ²` rings as `cos γt` at rate `γ`, with period `2π/γ` and poles at `±iγ`. -/
theorem seam_clock {γ : ℝ} (hγ : 0 < γ) :
    inductance (I * γ) = ((2 / γ ^ 2 : ℝ) : ℂ) ∧ capacitance = ((1 / 2 : ℝ) : ℂ) ∧
      IsTankSolution (1 / 2) (2 / γ ^ 2) (fun t => Real.cos (γ * t))
        (fun t => 1 / 2 * γ * Real.sin (γ * t)) (fun _ => 0) ∧
      1 / Real.sqrt ((2 / γ ^ 2) * (1 / 2)) = γ ∧
      Function.Periodic (fun t => Real.cos (γ * t)) (2 * Real.pi / γ) ∧
      ∀ w : ℂ, (w ^ 2 * inductance (I * γ) * capacitance + 1 = 0 ↔ w = I * γ ∨ w = -(I * γ)) := by
  have hres := seam_tank_resonance hγ
  have hne : I * (γ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hγ.ne')
  refine ⟨hres.1, by unfold capacitance; push_cast; ring, free_oscillation ?_, hres.2,
    (free_period hγ.ne').1, fun w => tank_pole_iff hne⟩
  field_simp

/-! ## 4. Sign: positivity is the seam -/

/-- [proved-standard; formal-checked] On the open right half-plane, `Re(1/u) > 0`. -/
theorem re_one_div_pos {u : ℂ} (hu : 0 < u.re) : 0 < (1 / u).re := by
  have hne : u ≠ 0 := fun h => by rw [h, zero_re] at hu; exact lt_irrefl _ hu
  rw [one_div, inv_re]
  exact div_pos hu (normSq_pos.mpr hne)

/-- [proved-derived; formal-checked] A tank whose zero is on the seam is positive real:
`Re tank(ρ′, w) > 0` when `Re ρ′ = 0` and `Re w > 0`. -/
theorem re_tank_pos_of_seam {ρ' w : ℂ} (hρ : ρ'.re = 0) (hw : 0 < w.re) :
    0 < (tank ρ' w).re := by
  have h₁ : w ≠ ρ' := fun h => by rw [h, hρ] at hw; exact lt_irrefl _ hw
  have h₂ : w ≠ -ρ' := fun h => by rw [h, neg_re, hρ, neg_zero] at hw; exact lt_irrefl _ hw
  rw [tank_eq_pair_centred h₁ h₂, add_re]
  apply add_pos
  · apply re_one_div_pos
    rw [sub_re, hρ, sub_zero]
    exact hw
  · apply re_one_div_pos
    rw [add_re, hρ, add_zero]
    exact hw

/-- [proved-derived; formal-checked] For real `γ`, `Re tank(iγ, w) > 0` on `Re w > 0`. -/
theorem re_seam_tank_pos (γ : ℝ) {w : ℂ} (hw : 0 < w.re) : 0 < (tank (I * γ) w).re :=
  re_tank_pos_of_seam (by simp) hw

/-- [proved-derived; formal-checked] A seam tank is real on the real axis: `2x/(x² + γ²)`. -/
theorem seam_tank_real (γ x : ℝ) : tank (I * γ) x = ((2 * x / (x ^ 2 + γ ^ 2) : ℝ) : ℂ) := by
  unfold tank
  rw [mul_pow, I_sq]
  push_cast
  ring

/-- [proved-standard; formal-checked] A term of the flux: `Re(k/u) = k · Re(1/u)`. -/
theorem re_natCast_div (k : ℕ) (u : ℂ) : ((k : ℂ) / u).re = (k : ℝ) * (1 / u).re := by
  rw [div_eq_mul_one_div, ← ofReal_natCast, re_ofReal_mul]

/-- [proved-derived; formal-checked] A comb on the seam has `Re ≥ 0` on `Re w > 0`. -/
theorem combFlux_re_nonneg_of_seam {Z : Finset ℂ} {m : ℂ → ℕ} (hseam : ∀ ρ' ∈ Z, ρ'.re = 0)
    {w : ℂ} (hw : 0 < w.re) : 0 ≤ (combFlux Z m w).re := by
  unfold combFlux
  rw [re_sum]
  apply Finset.sum_nonneg
  intro ρ' hρ'
  rw [re_natCast_div]
  have hpos := re_one_div_pos (u := w - ρ') (by rw [sub_re, hseam ρ' hρ', sub_zero]; exact hw)
  exact mul_nonneg (Nat.cast_nonneg _) hpos.le

/-- [proved-derived; formal-checked] A nonempty comb on the seam with multiplicities `≥ 1` has
`Re > 0` on `Re w > 0`. -/
theorem combFlux_re_pos_of_seam {Z : Finset ℂ} {m : ℂ → ℕ} (hseam : ∀ ρ' ∈ Z, ρ'.re = 0)
    (hne : Z.Nonempty) (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') {w : ℂ} (hw : 0 < w.re) :
    0 < (combFlux Z m w).re := by
  unfold combFlux
  rw [re_sum]
  apply Finset.sum_pos _ hne
  intro ρ' hρ'
  rw [re_natCast_div]
  have hpos := re_one_div_pos (u := w - ρ') (by rw [sub_re, hseam ρ' hρ', sub_zero]; exact hw)
  have hk : (0 : ℝ) < m ρ' := by exact_mod_cast hm1 ρ' hρ'
  exact mul_pos hk hpos

/-- [proved-standard; formal-checked] A positive real comb has no pole `a` with `Re a > 0` and
multiplicity `≥ 1`: along `w = a − ε` the real part of the flux falls to `−∞`. -/
theorem no_pole_right_of_positive {Z : Finset ℂ} {m : ℂ → ℕ}
    (hpos : ∀ w : ℂ, 0 < w.re → w ∉ Z → 0 ≤ (combFlux Z m w).re)
    {a : ℂ} (ha : a ∈ Z) (hma : 1 ≤ m a) : ¬ 0 < a.re := by
  classical
  intro hare
  have hR : Tendsto (fun ε : ℝ => (∑ ρ' ∈ Z.erase a, (m ρ' : ℂ) / (a - ε - ρ')).re) (𝓝 0)
      (𝓝 (∑ ρ' ∈ Z.erase a, (m ρ' : ℂ) / (a - ((0 : ℝ) : ℂ) - ρ')).re) := by
    have hsum : Tendsto (fun ε : ℝ => ∑ ρ' ∈ Z.erase a, (m ρ' : ℂ) / (a - ε - ρ')) (𝓝 0)
        (𝓝 (∑ ρ' ∈ Z.erase a, (m ρ' : ℂ) / (a - ((0 : ℝ) : ℂ) - ρ'))) := by
      apply tendsto_finsetSum
      intro ρ' hρ'
      have hne : a - ((0 : ℝ) : ℂ) - ρ' ≠ 0 := by
        rw [ofReal_zero, sub_zero, sub_ne_zero]
        exact (ne_of_mem_erase hρ').symm
      have hc : ContinuousAt (fun ε : ℝ => (m ρ' : ℂ) / (a - ε - ρ')) 0 :=
        continuousAt_const.div
          ((continuousAt_const.sub continuous_ofReal.continuousAt).sub continuousAt_const) hne
      exact hc.tendsto
    exact (continuous_re.tendsto _).comp hsum
  have hma' : (1 : ℝ) ≤ m a := by exact_mod_cast hma
  have hpole : Tendsto (fun ε : ℝ => -(m a : ℝ) * ε⁻¹) (𝓝[>] 0) atBot :=
    tendsto_inv_nhdsGT_zero.const_mul_atTop_of_neg (by linarith)
  have hneg := (hpole.atBot_add (hR.mono_left nhdsWithin_le_nhds)).eventually
    (eventually_lt_atBot 0)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < a.re := nhdsWithin_le_nhds (Iio_mem_nhds hare)
  have hgt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  have hout : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ∀ ρ' ∈ Z.erase a, a - (ε : ℂ) ≠ ρ' := by
    rw [eventually_all_finset]
    intro ρ' hρ'
    apply nhdsWithin_le_nhds
    have hc : ContinuousAt (fun ε : ℝ => a - (ε : ℂ)) 0 :=
      continuousAt_const.sub continuous_ofReal.continuousAt
    exact hc.eventually_ne (by rw [ofReal_zero, sub_zero]; exact (ne_of_mem_erase hρ').symm)
  obtain ⟨ε, hε1, hε2, hε3, hε4⟩ := (hneg.and (hsmall.and (hgt.and hout))).exists
  have hwre : 0 < (a - (ε : ℂ)).re := by
    rw [sub_re, ofReal_re]
    linarith
  have hwZ : a - (ε : ℂ) ∉ Z := by
    intro hmem
    by_cases hEq : a - (ε : ℂ) = a
    · have h0 : (ε : ℂ) = 0 := by linear_combination -hEq
      exact hε3.ne' (by exact_mod_cast h0)
    · exact hε4 _ (mem_erase.mpr ⟨hEq, hmem⟩) rfl
  have hval := hpos _ hwre hwZ
  have hsplit : (combFlux Z m (a - ε)).re =
      -(m a : ℝ) * ε⁻¹ + (∑ ρ' ∈ Z.erase a, (m ρ' : ℂ) / (a - ε - ρ')).re := by
    unfold combFlux
    rw [← add_sum_erase Z (fun ρ' => (m ρ' : ℂ) / (a - (ε : ℂ) - ρ')) ha, add_re]
    congr 1
    have hd : a - (ε : ℂ) - a = ((-ε : ℝ) : ℂ) := by push_cast; ring
    rw [hd, ← ofReal_natCast, ← ofReal_div, ofReal_re]
    ring
  linarith

/-- [proved-derived; formal-checked] **The finite Foster theorem on the seam.** A finite
reflection-closed comb with multiplicities `≥ 1` is positive real on `Re w > 0` iff every zero is
on the seam. -/
theorem comb_positive_real_iff_seam {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') :
    (∀ w : ℂ, 0 < w.re → w ∉ Z → 0 ≤ (combFlux Z m w).re) ↔ ∀ ρ' ∈ Z, ρ'.re = 0 := by
  constructor
  · intro hpos ρ' hρ'
    have h1 := no_pole_right_of_positive hpos hρ' (hm1 ρ' hρ')
    have h2 := no_pole_right_of_positive hpos (hZ ρ' hρ') (hm1 _ (hZ ρ' hρ'))
    rw [neg_re, not_lt] at h2
    rw [not_lt] at h1
    linarith
  · intro hseam w hw _
    exact combFlux_re_nonneg_of_seam hseam hw

/-- [proved-derived; formal-checked] **Foster, finite form.** With `0 ∉ Z`, the comb is positive
real iff every tank has positive real inductance. -/
theorem foster_finite {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z) (h0 : (0 : ℂ) ∉ Z)
    (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') :
    (∀ w : ℂ, 0 < w.re → w ∉ Z → 0 ≤ (combFlux Z m w).re) ↔
      ∀ ρ' ∈ Z, ∃ L : ℝ, 0 < L ∧ inductance ρ' = L := by
  rw [comb_positive_real_iff_seam hZ hm1]
  constructor
  · intro hseam ρ' hρ'
    exact (inductance_pos_real_iff ρ').mpr ⟨hseam ρ' hρ', fun h => h0 (h ▸ hρ')⟩
  · intro hL ρ' hρ'
    exact ((inductance_pos_real_iff ρ').mp (hL ρ' hρ')).1

/-! ## 5. The comb as a series interconnection -/

/-- [proved-standard; formal-checked] The series connection's power balance: one port current,
voltages adding, `Ḣ = (Σ v_j)·i`. -/
theorem series_power_balance {ι : Type*} (s : Finset ι) (C L : ι → ℝ) (v iL : ι → ℝ → ℝ)
    (i : ℝ → ℝ) (h : ∀ j ∈ s, IsTankSolution (C j) (L j) (v j) (iL j) i) (t : ℝ) :
    HasDerivAt (fun τ => ∑ j ∈ s, tankEnergy (C j) (L j) (v j τ) (iL j τ))
      ((∑ j ∈ s, v j t) * i t) t := by
  rw [Finset.sum_mul]
  exact HasDerivAt.fun_sum (fun j hj => tank_power_balance (h j hj) t)

/-- [proved-standard; formal-checked] The series connection's storage is nonnegative. -/
theorem seriesEnergy_nonneg {ι : Type*} (s : Finset ι) {C L : ι → ℝ} (hC : ∀ j ∈ s, 0 ≤ C j)
    (hL : ∀ j ∈ s, 0 ≤ L j) (v iL : ι → ℝ) :
    0 ≤ ∑ j ∈ s, tankEnergy (C j) (L j) (v j) (iL j) :=
  Finset.sum_nonneg fun j hj => tankEnergy_nonneg (hC j hj) (hL j hj) _ _

/-- [proved-standard; formal-checked] The series port's voltage is the sum of the voltages. -/
theorem mode_sum {ι : Type*} (s : Finset ι) (V : ι → ℂ) (w : ℂ) (t : ℝ) :
    mode (∑ j ∈ s, V j) w t = ∑ j ∈ s, mode (V j) w t := by
  unfold mode
  rw [Finset.sum_mul]

/-- [proved-standard; formal-checked] The series connection's impedance is the sum. -/
theorem series_impedance {ι : Type*} (s : Finset ι) (C L V JL : ι → ℂ) {w J : ℂ}
    (h : ∀ j ∈ s, IsComplexTankSolution (C j) (L j) (mode (V j) w) (mode (JL j) w) (mode J w))
    (hden : ∀ j ∈ s, w ^ 2 * L j * C j + 1 ≠ 0) :
    ∑ j ∈ s, V j = (∑ j ∈ s, parallelImpedance (C j) (L j) w) * J := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j hj => (mode_response (h j hj) (hden j hj)).1

/-- [proved-standard; formal-checked] `k` tanks' worth of impedance is one tank with `kL`, `C/k`. -/
theorem mul_parallelImpedance {k : ℂ} (hk : k ≠ 0) (C L w : ℂ) :
    k * parallelImpedance C L w = parallelImpedance (C / k) (k * L) w := by
  unfold parallelImpedance
  have hs : w ^ 2 * (k * L) * (C / k) + 1 = w ^ 2 * L * C + 1 := by
    field_simp
  rw [hs]
  ring

/-- [definition] The capacitance of the comb's element of multiplicity `k`. -/
def elementCapacitance (k : ℕ) : ℂ := 1 / k

/-- [definition] The inductance of the comb's element of `ρ′` with multiplicity `k`. -/
def elementInductance (k : ℕ) (ρ' : ℂ) : ℂ := -(k : ℂ) / ρ' ^ 2

/-- [proved-derived; formal-checked] The element's inductance is `k/2` times the owner's. -/
theorem elementInductance_eq (k : ℕ) (ρ' : ℂ) :
    elementInductance k ρ' = (k : ℂ) / 2 * inductance ρ' := by
  unfold elementInductance inductance
  ring

/-- [proved-derived; formal-checked] The element's denominator is `(ρ′² − w²)/ρ′²`. -/
theorem element_split {k : ℕ} (hk : k ≠ 0) {ρ' : ℂ} (hρ : ρ' ≠ 0) (w : ℂ) :
    w ^ 2 * elementInductance k ρ' * elementCapacitance k + 1 = (ρ' ^ 2 - w ^ 2) / ρ' ^ 2 := by
  unfold elementInductance elementCapacitance
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  field_simp
  ring

/-- [proved-derived; formal-checked] The element's impedance is `k w/(w² − ρ′²)`. -/
theorem element_impedance {k : ℕ} (hk : k ≠ 0) {ρ' : ℂ} (hρ : ρ' ≠ 0) (w : ℂ) :
    parallelImpedance (elementCapacitance k) (elementInductance k ρ') w =
      (k : ℂ) * (w / (w ^ 2 - ρ' ^ 2)) := by
  unfold parallelImpedance
  rw [element_split hk hρ w]
  unfold elementInductance
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  by_cases hden : w ^ 2 - ρ' ^ 2 = 0
  · have hB : ρ' ^ 2 - w ^ 2 = 0 := by linear_combination -hden
    rw [hden, hB, zero_div, div_zero, div_zero, mul_zero]
  · have hB : ρ' ^ 2 - w ^ 2 ≠ 0 := fun h => hden (by linear_combination -h)
    field_simp
    ring

/-- [proved-derived; formal-checked] The element is the owner's tank weighted by `k/2`. -/
theorem element_impedance_eq_half_tank {k : ℕ} (hk : k ≠ 0) {ρ' : ℂ} (hρ : ρ' ≠ 0) (w : ℂ) :
    parallelImpedance (elementCapacitance k) (elementInductance k ρ') w =
      (k : ℂ) / 2 * tank ρ' w := by
  rw [element_impedance hk hρ w]
  unfold tank
  ring

/-- [proved-derived; formal-checked] Away from `±ρ′` the element's denominator is nonzero. -/
theorem element_den_ne {k : ℕ} (hk : k ≠ 0) {ρ' w : ℂ} (hρ : ρ' ≠ 0) (h₁ : w ≠ ρ')
    (h₂ : w ≠ -ρ') : w ^ 2 * elementInductance k ρ' * elementCapacitance k + 1 ≠ 0 := by
  rw [element_split hk hρ w]
  have h2 : ρ' ^ 2 ≠ 0 := pow_ne_zero 2 hρ
  refine div_ne_zero ?_ h2
  intro h
  have hsq : w ^ 2 = ρ' ^ 2 := by linear_combination -h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h' | h'
  · exact h₁ h'
  · exact h₂ h'

/-- [proved-derived; formal-checked] The owner's paired flux in the centred frame: on a
reflection-closed comb, `Σ m/(w − ρ′) = Σ m w/(w² − ρ′²)`. -/
theorem combFlux_eq_pairSum {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm : ∀ ρ' ∈ Z, m (-ρ') = m ρ') {w : ℂ} (hw : w ∉ Z) :
    combFlux Z m w = ∑ ρ' ∈ Z, (m ρ' : ℂ) * (w / (w ^ 2 - ρ' ^ 2)) := by
  have key := flux_eq_tankSum (Z := Z.map (Equiv.addRight (1 / 2 : ℂ)).toEmbedding)
    (m := fun ρ => m (ρ - 1 / 2)) (z := w + 1 / 2) ?_ ?_ ?_
  · rw [Finset.sum_map, Finset.sum_map] at key
    simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, add_sub_cancel_right,
      add_sub_add_right_eq_sub] at key
    exact key
  · intro ρ hρ
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_map.mp hρ
    refine Finset.mem_map.mpr ⟨-ρ', hZ ρ' hρ', ?_⟩
    simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight]
    ring
  · intro ρ hρ
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_map.mp hρ
    simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight]
    have e1 : 1 - (ρ' + 1 / 2) - 1 / 2 = -ρ' := by ring
    rw [e1, hm ρ' hρ', add_sub_cancel_right]
  · intro ρ hρ h
    obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_map.mp hρ
    simp only [Equiv.coe_toEmbedding, Equiv.coe_addRight, add_left_inj] at h
    exact hw (h ▸ hρ')

/-- [proved-derived; formal-checked] Equivalently, the comb's flux is its paired tank sum, each
member carrying half its pair's tank. -/
theorem combFlux_eq_halfTankSum {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm : ∀ ρ' ∈ Z, m (-ρ') = m ρ') {w : ℂ} (hw : w ∉ Z) :
    combFlux Z m w = ∑ ρ' ∈ Z, (m ρ' : ℂ) / 2 * tank ρ' w := by
  rw [combFlux_eq_pairSum hZ hm hw]
  apply Finset.sum_congr rfl
  intro ρ' _
  unfold tank
  ring

/-- [proved-derived; formal-checked] The paired tank sum is positive real iff the comb is on the
seam. -/
theorem pairedTanks_positive_real_iff_seam {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm : ∀ ρ' ∈ Z, m (-ρ') = m ρ') (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') :
    (∀ w : ℂ, 0 < w.re → w ∉ Z → 0 ≤ (∑ ρ' ∈ Z, (m ρ' : ℂ) / 2 * tank ρ' w).re) ↔
      ∀ ρ' ∈ Z, ρ'.re = 0 := by
  rw [← comb_positive_real_iff_seam hZ hm1]
  constructor
  · intro h w hw hwZ
    rw [combFlux_eq_halfTankSum hZ hm hwZ]
    exact h w hw hwZ
  · intro h w hw hwZ
    rw [← combFlux_eq_halfTankSum hZ hm hwZ]
    exact h w hw hwZ

/-- [proved-derived; formal-checked] The comb's flux is the impedance of the series
interconnection of its elements. -/
theorem combFlux_eq_series {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm : ∀ ρ' ∈ Z, m (-ρ') = m ρ') (h0 : (0 : ℂ) ∉ Z) (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') {w : ℂ}
    (hw : w ∉ Z) :
    combFlux Z m w =
      ∑ ρ' ∈ Z, parallelImpedance (elementCapacitance (m ρ')) (elementInductance (m ρ') ρ') w := by
  rw [combFlux_eq_pairSum hZ hm hw]
  apply Finset.sum_congr rfl
  intro ρ' hρ'
  have hk : m ρ' ≠ 0 := by have := hm1 ρ' hρ'; omega
  rw [element_impedance hk (fun h => h0 (h ▸ hρ'))]

/-- [proved-derived; formal-checked] **The receiver.** Driving the comb's series port with the
mode `J e^{wt}`, the port's voltage amplitude is `combFlux · J`. -/
theorem comb_receiver {Z : Finset ℂ} {m : ℂ → ℕ} (hZ : ∀ ρ' ∈ Z, -ρ' ∈ Z)
    (hm : ∀ ρ' ∈ Z, m (-ρ') = m ρ') (h0 : (0 : ℂ) ∉ Z) (hm1 : ∀ ρ' ∈ Z, 1 ≤ m ρ') {w J : ℂ}
    (hw : w ∉ Z) (V JL : ℂ → ℂ)
    (h : ∀ ρ' ∈ Z, IsComplexTankSolution (elementCapacitance (m ρ')) (elementInductance (m ρ') ρ')
      (mode (V ρ') w) (mode (JL ρ') w) (mode J w)) :
    ∑ ρ' ∈ Z, V ρ' = combFlux Z m w * J := by
  rw [combFlux_eq_series hZ hm h0 hm1 hw]
  refine series_impedance Z _ _ V JL h fun ρ' hρ' => ?_
  have hk : m ρ' ≠ 0 := by have := hm1 ρ' hρ'; omega
  refine element_den_ne hk (fun h => h0 (h ▸ hρ')) (fun h => hw (h ▸ hρ')) ?_
  intro h
  exact hw (h ▸ hZ ρ' hρ')

/-- [proved-derived; formal-checked] On the seam the comb's elements are real tanks with
`C = 1/k > 0` and `L = k/(Im ρ′)² > 0`. -/
theorem seam_element_real {ρ' : ℂ} (hre : ρ'.re = 0) (hρ : ρ' ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    elementInductance k ρ' = ((k / ρ'.im ^ 2 : ℝ) : ℂ) ∧ 0 < (k : ℝ) / ρ'.im ^ 2 ∧
      elementCapacitance k = ((1 / k : ℝ) : ℂ) ∧ 0 < 1 / (k : ℝ) := by
  have him : ρ'.im ≠ 0 := fun h => hρ (Complex.ext hre h)
  have hρeq : ρ' = I * (ρ'.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have him2 : (0 : ℝ) < ρ'.im ^ 2 := by positivity
  refine ⟨?_, div_pos hk' him2, ?_, by positivity⟩
  · have hsq : ρ' ^ 2 = -((ρ'.im : ℂ) ^ 2) := by
      conv_lhs => rw [hρeq]
      rw [mul_pow, I_sq]
      ring
    unfold elementInductance
    rw [hsq, neg_div_neg_eq]
    push_cast
    rfl
  · unfold elementCapacitance
    push_cast
    ring

/-! ## 6. Witnesses -/

/-- [proved-derived; formal-checked] The seam tanks at `γ = 1, 2` read `1 + 2/5 = 7/5` at `w = 1`. -/
theorem witness_seam_pair : tank (I * 1) 1 + tank (I * 2) 1 = 7 / 5 := by
  simp only [tank, mul_pow, I_sq]
  norm_num

/-- [proved-derived; formal-checked] The off-seam pair `±(¼ + i)` reads a negative real part at
`w = ⅛ + i`, where `Re w = ⅛ > 0`. -/
theorem witness_off_seam :
    tank (1 / 4 + I) (1 / 8 + I) = ((-2096 / 265 : ℝ) : ℂ) - ((128 / 265 : ℝ) : ℂ) * I ∧
      (1 / 8 + I : ℂ).re = 1 / 8 ∧ (tank (1 / 4 + I) (1 / 8 + I)).re < 0 := by
  have hval : tank (1 / 4 + I) (1 / 8 + I) = ((-2096 / 265 : ℝ) : ℂ) - ((128 / 265 : ℝ) : ℂ) * I := by
    unfold tank
    have hd : (1 / 8 + I) ^ 2 - (1 / 4 + I) ^ 2 = -3 / 64 - I / 4 := by ring
    have hne : (-3 / 64 - I / 4 : ℂ) ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    rw [hd, div_eq_iff hne]
    push_cast
    linear_combination (-32 / 265 : ℂ) * I_sq
  refine ⟨hval, by norm_num, ?_⟩
  rw [hval]
  norm_num

end Holonics.Zeta.FosterReturn

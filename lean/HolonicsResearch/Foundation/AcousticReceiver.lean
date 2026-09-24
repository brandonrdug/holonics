import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Holonics.Foundation.CausalChord

/-!
# The acoustic receiver: a resonator bank on the colour receiver's own mode population

[definition] This is the checked mathematical owner of receiver **R2**. A standalone Rust mirror
at `crates/holonic-engine/src/acoustic_receiver.rs` implemented this law and was retired in R1
(issue #65) because no current Rust caller or example consumed it. The correspondence below is
historical evidence, not a live code dependency. R2 is recorded in
`docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`:

```text
r_b' = (−γ_b + i Ω_b) r_b + Σ_m κ_bm A_m(t)
```

driven by **the same co-present mode population the existing colour receiver consumes**. The
historical Rust mirror used `dimensional_wave.rs`'s `ExactReceiverPhasePopulation`, whose
`coherent_modes` map already sums same-mode currents *before* any quadratic response is formed;
here it is the function `A : Fin M → ℂ`. Colour and timbre are then two maps out of one type and
not two authored mappings.

Five things are stated, in this order.

1. **The exact discrete law.** The continuous resonator's response `exp(λ t)` is not rational, so
   nothing here discretizes it by approximation. `cayley h λ = (2 + hλ)/(2 − hλ)` is the
   Cayley/bilinear map at a *declared* step `h > 0`; `gain h λ = h/(2 − hλ)`. Both are Gaussian
   rational when `h`, `γ_b`, `Ω_b` are rational, which allowed the former Rust state to be exact.
   `cayley_den_ne_zero` makes the law **total** on the whole closed left half plane.
   `normSq_cayley_lt_one` proves the stability preservation the plan demands — open left half
   plane ↦ open unit disc — and `normSq_cayley_eq_one` proves the marginal case is marginal
   exactly, not nearly.
2. **Causality and superposition.** `Bank.run` is a fold over the input history.
   `run_causal` is the plan's causality contract: the state after `n` steps depends only on inputs
   strictly before `n`. `run_add` is exact superposition *through the bank* from rest, and
   `pressure_add` carries it through the one-dimensional pressure projection, which is therefore
   **not** where the ordering matters.
3. **Why the ordering is law.** `colour_does_not_distribute` and
   `quantize_then_superpose_ne_superpose_then_quantize` are the two concrete counterexamples. The
   first is the quadratic phase response, the second the integer readout. Either one, applied
   before superposition, returns a different object; this is exactly the cross-term identity
   `|Σ z_j|² = Σ|z_j|² + 2 Re Σ_{j<k} conj(z_j) z_k` of
   `research/records/2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md`.
   Superposition first, quadratic response and quantization last, pressure projection last of all.
4. **Stability and energy.** `energy_advance_le` and `energy_advance_lt` are the declared quadratic
   energy's monotonicity at zero input: nonincreasing for `γ ≥ 0`, strictly decreasing for
   `γ > 0`. `rateForm_realBlock` ties that reading to `Σ_G` of
   `Holonics.Foundation.CausalChord`: the realified one-pole generator has
   `rateForm A 1 = (−2γ) • 1`, so the discrete decay and the continuous rate form are the same
   statement read through two clocks. `charpoly_realBlock` names the band's pole exactly —
   `X² + 2γX + (γ² + Ω²)` — which is what makes each audible component's pole an exact factor
   rather than a measured frequency.
5. **One lineage, two receivers.** `colour` and `Bank.timbre` are two maps out of the one
   population. `population_change_moves_both` shows a change of population moves both.
   `metamer_sounds_different` exhibits two populations with **equal colour and different timbre**
   — swapping which mode carries which quadrature is invisible to a receiver that sums its
   quadratic response across modes — and `unison_looks_different` exhibits two with **equal timbre
   and different colour**, using a mode no resonator couples to. Neither receiver refines the
   other, which is the whole content of "the atlas separates what one face cannot".

[definition] **The standing caution, stated in the owner and built into no gate.** Sound and
colour are guidance receivers and never truth oracles. `energy_advance_lt` says a bank with
positive decay settles; it does not say what it settled onto is true. A construction may reach an
acoustically stable equilibrium under an incomplete receiver while remaining false. Nothing below
is an acceptance condition; the historical mirror built no gate from it.

[definition] The step, decays, rates and couplings are carried here as reals. The retired Rust
mirror carried declared rational instances with sources; ℚ ⊆ ℝ, so every theorem below applies to
those executed instances. The reverse does not hold, and the mirror's exactness came from its own
arithmetic, not from these statements.

Historical Rust correspondence (retired R1, issue #65):
`crates/holonic-engine/src/acoustic_receiver.rs`
(`Bank` ↔ `ResonatorBank`; `cayley`/`gain` ↔ `ResonatorBank::transition`/`ResonatorBank::gain`;
`Bank.advance`/`Bank.run` ↔ `ResonatorBank::advance`/`ResonatorBank::run`; `run_causal` ↔
`the_state_after_n_steps_ignores_every_later_input`; `run_add` ↔
`superposition_holds_through_the_bank`; `colour_does_not_distribute` ↔
`the_colour_law_does_not_distribute_over_superposition`;
`quantize_then_superpose_ne_superpose_then_quantize` ↔
`quantize_then_superpose_differs_from_superpose_then_quantize`; `energy_advance_le`/
`energy_advance_lt` ↔ `the_declared_energy_is_nonincreasing_at_zero_input`/
`positive_decay_strictly_dissipates`; `normSq_cayley_lt_one` ↔
`the_left_half_plane_maps_inside_the_unit_disc`; `charpoly_realBlock` ↔
`each_band_names_its_pole_by_an_exact_factor`; `rateForm_realBlock` ↔
`the_band_rate_form_is_minus_twice_the_decay`; `metamer_sounds_different` ↔
`metamers_sound_different`; `unison_looks_different` ↔ `unisons_look_different`;
`population_change_moves_both` ↔ `a_change_of_population_moves_both_receivers`).
Colour is **not** restated here as a second law: `colour` below is the pre-aperture half of
`dimensional_wave.rs`'s `ExactReceiverPrimaryDoctrine::transduce`, which the historical mirror
called rather than reimplemented.
-/

noncomputable section

namespace Holonics.Foundation.AcousticReceiver

open scoped BigOperators

/-! ## The one-pole causal chord and its exact discrete law -/

section Pole

/-- [definition] The pole of a band: `λ = −γ + iΩ`. It is R1's causal chord at one pole, and the
bank below is the block diagonal of these. -/
def pole (g o : ℝ) : ℂ := ⟨-g, o⟩

@[simp]
theorem pole_re (g o : ℝ) : (pole g o).re = -g := rfl

@[simp]
theorem pole_im (g o : ℝ) : (pole g o).im = o := rfl

/-- [definition] **The declared exact discrete law.** The continuous response `exp(λ t)` is not
rational, so it is not the law: the law is the Cayley/bilinear image of `λ` at the declared step
`h`. For rational `h`, `γ`, `Ω` this is a Gaussian rational; the former Rust mirror used that
representation to keep its executed state exact. -/
def cayley (h : ℝ) (lam : ℂ) : ℂ := (2 + (h : ℂ) * lam) / (2 - (h : ℂ) * lam)

/-- [definition] The matching input gain of the same discretization. -/
def gain (h : ℝ) (lam : ℂ) : ℂ := (h : ℂ) / (2 - (h : ℂ) * lam)

/-- [proved-derived; formal-checked] **The law is total on the closed left half plane.** The real
part of `2 − hλ` is `2 − h·λ.re ≥ 2` there, so the denominator never vanishes and no branch,
guard or refusal is needed inside the step. -/
theorem cayley_den_ne_zero {h : ℝ} (hh : 0 < h) {lam : ℂ} (hre : lam.re ≤ 0) :
    (2 : ℂ) - (h : ℂ) * lam ≠ 0 := by
  intro hz
  have hre' : ((2 : ℂ) - (h : ℂ) * lam).re = 0 := by rw [hz]; simp
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.re_ofNat, zero_mul, sub_zero] at hre'
  nlinarith [mul_nonneg hh.le (neg_nonneg.mpr hre)]

/-- [proved-derived; formal-checked] **Stability is preserved exactly: the open left half plane
maps inside the open unit disc.** `‖2 + hλ‖² − ‖2 − hλ‖² = 8 h λ.re`, so the sign of the decay
alone decides, with no tolerance anywhere. This is the theorem the plan asks to be proved in
Lean. -/
theorem normSq_cayley_lt_one {h : ℝ} (hh : 0 < h) {lam : ℂ} (hre : lam.re < 0) :
    Complex.normSq (cayley h lam) < 1 := by
  have hden : (2 : ℂ) - (h : ℂ) * lam ≠ 0 := cayley_den_ne_zero hh hre.le
  have hd : 0 < Complex.normSq ((2 : ℂ) - (h : ℂ) * lam) := Complex.normSq_pos.mpr hden
  rw [cayley, map_div₀, div_lt_one hd]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero, zero_add, add_zero]
  nlinarith [mul_pos hh (neg_pos.mpr hre)]

/-- [proved-derived; formal-checked] **The marginal case is marginal exactly.** A band with zero
decay has `‖z‖ = 1`, so its declared energy is conserved and not merely almost conserved. -/
theorem normSq_cayley_eq_one {h : ℝ} (hh : 0 < h) {lam : ℂ} (hre : lam.re = 0) :
    Complex.normSq (cayley h lam) = 1 := by
  have hden : (2 : ℂ) - (h : ℂ) * lam ≠ 0 := cayley_den_ne_zero hh hre.le
  have hd : Complex.normSq ((2 : ℂ) - (h : ℂ) * lam) ≠ 0 := (Complex.normSq_pos.mpr hden).ne'
  rw [cayley, map_div₀, div_eq_one_iff_eq hd]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero, zero_add, add_zero, mul_zero, hre]
  ring

end Pole

/-! ## The band's realified generator, its exact pole name and its rate form -/

section Block

open Matrix Polynomial

/-- [definition] The realification over the reals of the one-pole generator `λ = −γ + iΩ`, which is
the `2 × 2` diagonal block the historical Rust mirror assembled into R1's `Linearization`. The bank's state
operator is the block diagonal of these, exactly as `causal_chord::resolvent_probe` realifies a
Gaussian-rational probe point. -/
def realBlock (g o : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![(-g : ℂ), (-o : ℂ); (o : ℂ), (-g : ℂ)]

/-- [proved-derived; formal-checked] **Each band names its pole by an exact factor.** The block's
characteristic polynomial is `X² + 2γX + (γ² + Ω²)`, whose roots are `−γ ± iΩ`. The audible
component's pole is therefore this exact rational factor and never a measured frequency — which is
what let the historical Rust mirror return `Ω` read off an isolating interval as a *declared readout* while
the pole itself stays exact. -/
theorem trace_realBlock (g o : ℝ) : (realBlock g o).trace = -(((2 * g : ℝ)) : ℂ) := by
  simp only [realBlock, Matrix.trace_fin_two_of]
  push_cast
  ring

theorem det_realBlock (g o : ℝ) : (realBlock g o).det = (((g * g + o * o : ℝ)) : ℂ) := by
  simp only [realBlock, Matrix.det_fin_two_of]
  push_cast
  ring

theorem charpoly_realBlock (g o : ℝ) :
    (realBlock g o).charpoly
      = X ^ 2 + C ((2 * g : ℝ) : ℂ) * X + C (((g * g + o * o : ℝ)) : ℂ) := by
  rw [Matrix.charpoly_fin_two, trace_realBlock, det_realBlock, map_neg]
  ring

/-- [proved-derived; formal-checked] **The rate form of a band is minus twice its decay.** With the
unit metric, `Σ_G = AᴴG + GA = (−2γ) · I` for the realified one-pole generator. This is the
`rateForm` of `Holonics.Foundation.CausalChord` evaluated on the bank's block, so the
continuous dissipation reading and the discrete `‖cayley‖ < 1` reading above are one statement at
two clocks: negative definite exactly when `γ > 0`, zero exactly when `γ = 0`. -/
theorem rateForm_realBlock (g o : ℝ) :
    CausalChord.rateForm (realBlock g o) 1 = ((-2 * g : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CausalChord.rateForm, realBlock, Matrix.conjTranspose_apply] <;> ring

end Block

/-! ## The bank, its run, its causality and its superposition -/

section Bank

variable {B M : ℕ}

/-- [definition] **A declared bank of causal resonators.** No validation is carried in the
structure: the former `ResonatorBank::declared` refused a non-positive step, a negative
decay, a mismatched shape and an unsourced rate by name, and every theorem below states the
hypothesis it actually uses. In that historical realization, the executable constructor
validated carrying values while this formal owner stated the law. -/
structure Bank (B M : ℕ) where
  /-- The declared step `h`. -/
  step : ℝ
  /-- `γ_b`. -/
  decay : Fin B → ℝ
  /-- `Ω_b`. -/
  rate : Fin B → ℝ
  /-- `κ_bm`: how much of mode `m` band `b` consumes. -/
  kappa : Fin B → Fin M → ℝ
  /-- The real quadrature weight of the one-dimensional pressure projection. -/
  pressureRe : Fin B → ℝ
  /-- The imaginary quadrature weight of the one-dimensional pressure projection. -/
  pressureIm : Fin B → ℝ

namespace Bank

/-- The band's pole. -/
def bandPole (K : Bank B M) (b : Fin B) : ℂ := pole (K.decay b) (K.rate b)

/-- The band's exact one-step transition coefficient. -/
def transition (K : Bank B M) (b : Fin B) : ℂ := cayley K.step (K.bandPole b)

/-- The band's exact one-step input gain. -/
def bandGain (K : Bank B M) (b : Fin B) : ℂ := gain K.step (K.bandPole b)

/-- [definition] **The excitation: `Σ_m κ_bm A_m`.** The population is consumed *as one current*;
a mode the bank does not couple to contributes exactly zero and was reported by the historical
mirror rather than dropped. -/
def drive [Fintype (Fin M)] (K : Bank B M) (A : Fin M → ℂ) (b : Fin B) : ℂ :=
  ∑ m, (K.kappa b m : ℂ) * A m

/-- [proved-derived; formal-checked] The excitation is linear in the population. This is the first
half of "superposition holds up to the bank". -/
theorem drive_add (K : Bank B M) (A A' : Fin M → ℂ) (b : Fin B) :
    K.drive (A + A') b = K.drive A b + K.drive A' b := by
  simp only [drive, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

/-- One exact step of the bank. -/
def advance (K : Bank B M) (r : Fin B → ℂ) (A : Fin M → ℂ) : Fin B → ℂ :=
  fun b => K.transition b * r b + K.bandGain b * K.drive A b

/-- [definition] **The run.** The state after `n` steps of the declared input history. It is a fold,
which is why causality is structural rather than checked. -/
def run (K : Bank B M) (r₀ : Fin B → ℂ) (u : ℕ → Fin M → ℂ) : ℕ → Fin B → ℂ
  | 0 => r₀
  | n + 1 => K.advance (K.run r₀ u n) (u n)

@[simp]
theorem run_zero (K : Bank B M) (r₀ : Fin B → ℂ) (u : ℕ → Fin M → ℂ) :
    K.run r₀ u 0 = r₀ := rfl

@[simp]
theorem run_succ (K : Bank B M) (r₀ : Fin B → ℂ) (u : ℕ → Fin M → ℂ) (n : ℕ) :
    K.run r₀ u (n + 1) = K.advance (K.run r₀ u n) (u n) := rfl

/-- [proved-derived; formal-checked] **Causality.** The state after `n` steps depends only on the
inputs strictly before `n`. Two histories that agree on that prefix are indistinguishable at that
time however they differ later, which is the plan's "output at `t` depends only on inputs `≤ t`"
in its discrete form. -/
theorem run_causal (K : Bank B M) (r₀ : Fin B → ℂ) (u v : ℕ → Fin M → ℂ) (n : ℕ)
    (h : ∀ i, i < n → u i = v i) : K.run r₀ u n = K.run r₀ v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprefix : ∀ i, i < n → u i = v i := fun i hi => h i (Nat.lt_succ_of_lt hi)
      rw [run_succ, run_succ, ih hprefix, h n (Nat.lt_succ_self n)]

/-- [proved-derived; formal-checked] **Superposition holds up to — and only up to — the bank.**
From rest, the run of a superposed population is the superposition of the runs, exactly. Every
nonlinearity of this receiver therefore lives strictly after this point. -/
theorem run_add (K : Bank B M) (u v : ℕ → Fin M → ℂ) (n : ℕ) :
    K.run 0 (fun i => u i + v i) n = K.run 0 u n + K.run 0 v n := by
  induction n with
  | zero => simp
  | succ n ih =>
      ext b
      simp only [run_succ, advance, ih, Pi.add_apply, drive_add]
      ring

/-- [definition] **The one-dimensional pressure projection, which happens last.** -/
def pressure (K : Bank B M) (r : Fin B → ℂ) : ℝ :=
  ∑ b, (K.pressureRe b * (r b).re + K.pressureIm b * (r b).im)

/-- [proved-derived; formal-checked] The pressure projection is itself linear, so it is **not**
where the ordering matters. The ordering matters at the quadratic response and at the integer
readout, below. -/
theorem pressure_add (K : Bank B M) (r r' : Fin B → ℂ) :
    K.pressure (r + r') = K.pressure r + K.pressure r' := by
  simp only [pressure, Pi.add_apply, Complex.add_re, Complex.add_im, mul_add]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- [definition] **The acoustic reading of a population**: the bank state one step from rest. The
gain is nonzero on the closed left half plane, so this reading and the excitation determine each
other; it is stated at one step because that is the smallest reading in which a population is
already audible. -/
def timbre (K : Bank B M) (A : Fin M → ℂ) : Fin B → ℂ := K.advance 0 A

end Bank

/-! ### The declared quadratic energy -/

/-- [definition] The declared quadratic energy of a bank state under declared nonnegative weights.
It is the discrete reading whose rate form is `rateForm_realBlock`. -/
def energy (e : Fin B → ℝ) (r : Fin B → ℂ) : ℝ := ∑ b, e b * Complex.normSq (r b)

/-- [proved-derived; formal-checked] **At zero input the declared energy is nonincreasing.** Each
band contributes `‖z_b‖² ≤ 1` times its previous contribution, and `‖z_b‖ ≤ 1` is exactly
`γ_b ≥ 0`. -/
theorem energy_advance_le (K : Bank B M) (e : Fin B → ℝ) (he : ∀ b, 0 ≤ e b)
    (hh : 0 < K.step) (hg : ∀ b, 0 ≤ K.decay b) (r : Fin B → ℂ) :
    energy e (K.advance r 0) ≤ energy e r := by
  refine Finset.sum_le_sum fun b _ => ?_
  have hre : (K.bandPole b).re ≤ 0 := by
    simpa [Bank.bandPole] using neg_nonpos.mpr (hg b)
  have hz : Complex.normSq (K.transition b) ≤ 1 := by
    rcases lt_or_eq_of_le hre with hlt | heq
    · exact (normSq_cayley_lt_one hh hlt).le
    · exact (normSq_cayley_eq_one hh heq).le
  have hstep : (K.advance r 0) b = K.transition b * r b := by
    simp [Bank.advance, Bank.drive]
  rw [hstep, Complex.normSq_mul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left (Complex.normSq_nonneg _) hz) (he b)

/-- [proved-derived; formal-checked] **A band with positive decay strictly dissipates.** With
strictly positive weight and a nonzero amplitude in a band whose decay is positive, the declared
energy strictly decreases. `γ > 0 ⇒ ‖z‖ < 1` is `normSq_cayley_lt_one`; nothing is asymptotic and
nothing is approximate. -/
theorem energy_advance_lt (K : Bank B M) (e : Fin B → ℝ) (he : ∀ b, 0 ≤ e b)
    (hh : 0 < K.step) (hg : ∀ b, 0 ≤ K.decay b) (r : Fin B → ℂ)
    (b₀ : Fin B) (hb₀ : 0 < e b₀) (hd : 0 < K.decay b₀) (hr : r b₀ ≠ 0) :
    energy e (K.advance r 0) < energy e r := by
  have hstep : ∀ b, (K.advance r 0) b = K.transition b * r b := by
    intro b; simp [Bank.advance, Bank.drive]
  have hle : ∀ b ∈ Finset.univ, e b * Complex.normSq ((K.advance r 0) b)
      ≤ e b * Complex.normSq (r b) := by
    intro b _
    have hre : (K.bandPole b).re ≤ 0 := by
      simpa [Bank.bandPole] using neg_nonpos.mpr (hg b)
    have hz : Complex.normSq (K.transition b) ≤ 1 := by
      rcases lt_or_eq_of_le hre with hlt | heq
      · exact (normSq_cayley_lt_one hh hlt).le
      · exact (normSq_cayley_eq_one hh heq).le
    rw [hstep b, Complex.normSq_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (Complex.normSq_nonneg _) hz) (he b)
  have hstrict : e b₀ * Complex.normSq ((K.advance r 0) b₀)
      < e b₀ * Complex.normSq (r b₀) := by
    have hre : (K.bandPole b₀).re < 0 := by
      simpa [Bank.bandPole] using neg_neg_of_pos hd
    have hz : Complex.normSq (K.transition b₀) < 1 := normSq_cayley_lt_one hh hre
    have hpos : 0 < Complex.normSq (r b₀) := Complex.normSq_pos.mpr hr
    rw [hstep b₀, Complex.normSq_mul]
    exact mul_lt_mul_of_pos_left (by nlinarith) hb₀
  exact Finset.sum_lt_sum hle ⟨b₀, Finset.mem_univ b₀, hstrict⟩

end Bank

/-! ## Why the ordering is law -/

section Ordering

variable {M : ℕ}

/-- [definition] **The colour receiver's three exact nonnegative phase responses**, formed after
same-mode superposition. This is the pre-aperture half of `dimensional_wave.rs`'s
`ExactReceiverPrimaryDoctrine::transduce` — `(|Re A|², |Im A|², |Re A + Im A|²)` accumulated over
the co-present modes — and it is stated here only so the two receivers can be compared. The Rust
owner calls that doctrine and does not reimplement it. -/
def colour (A : Fin M → ℂ) : Fin 3 → ℝ
  | 0 => ∑ m, (A m).re * (A m).re
  | 1 => ∑ m, (A m).im * (A m).im
  | 2 => ∑ m, ((A m).re + (A m).im) * ((A m).re + (A m).im)

/-- [proved-derived; formal-checked] **The quadratic response does not distribute over
superposition**, so it must be taken after it. Doubling one mode's amplitude quadruples its
response; adding the two separate responses only doubles it. This is the cross-term identity
`|Σ z_j|² = Σ|z_j|² + 2 Re Σ_{j<k} conj(z_j) z_k` made concrete: the discarded term is the
relative phase. -/
theorem colour_does_not_distribute :
    ∃ A A' : Fin 1 → ℂ, colour (A + A') ≠ fun i => colour A i + colour A' i := by
  refine ⟨![1], ![1], ?_⟩
  intro h
  have h0 := congrFun h 0
  simp [colour] at h0

/-- [definition] The declared integer readout: the exterior export face's quantizer at a declared
full-scale denominator. It is produced last and never read back. -/
def quantize (scale : ℚ) (x : ℚ) : ℤ := ⌊x * scale⌋

/-- [proved-derived; formal-checked] **Quantize-then-superpose ≠ superpose-then-quantize.** Two
pressures of one half quantize to zero each, while their superposition quantizes to one. This is
why the ordering is law and not a convention: an export face taken before superposition reports a
silence that the current does not have. -/
theorem quantize_half_eq_zero : quantize 1 (1 / 2) = 0 := by
  unfold quantize
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

theorem quantize_one_eq_one : quantize 1 (1 / 2 + 1 / 2) = 1 := by
  unfold quantize
  rw [Int.floor_eq_iff]
  constructor <;> norm_num

theorem quantize_then_superpose_ne_superpose_then_quantize :
    quantize 1 (1 / 2) + quantize 1 (1 / 2) ≠ quantize 1 (1 / 2 + 1 / 2) := by
  rw [quantize_half_eq_zero, quantize_one_eq_one]
  decide

end Ordering

/-! ## One lineage: two receivers of one population -/

section Lineage

/-- [definition] The worked two-mode, one-band bank. Band `0` couples to mode `0` and **not** to
mode `1`; that uncoupled mode is what makes a unison look different below. -/
def workedBank : Bank 1 2 where
  step := 1
  decay := fun _ => 1
  rate := fun _ => 0
  kappa := fun _ => ![1, 0]
  pressureRe := fun _ => 1
  pressureIm := fun _ => 0

/-- [definition] The same bank with **both** modes coupled, at the unequal coupling constants
`κ = (1, 2)`. This is the bank the metamer below is stated over, and the inequality is what does the
work: a bank that consumed the two modes at *equal* `κ` would sum them and be as blind to the
exchange as the colour receiver is. It is the coupling that separates the modes, not the amount of
current in them. -/
def metamerBank : Bank 1 2 where
  step := 1
  decay := fun _ => 1
  rate := fun _ => 0
  kappa := fun _ => ![1, 2]
  pressureRe := fun _ => 1
  pressureIm := fun _ => 0

theorem bandGain_workedBank_ne_zero : workedBank.bandGain 0 ≠ 0 := by
  have hden : (2 : ℂ) - ((1 : ℝ) : ℂ) * pole 1 0 ≠ 0 :=
    cayley_den_ne_zero (by norm_num) (by simp)
  simp only [Bank.bandGain, gain, Bank.bandPole, workedBank]
  exact div_ne_zero (by norm_num) hden

theorem bandGain_metamerBank_ne_zero : metamerBank.bandGain 0 ≠ 0 := by
  have hden : (2 : ℂ) - ((1 : ℝ) : ℂ) * pole 1 0 ≠ 0 :=
    cayley_den_ne_zero (by norm_num) (by simp)
  simp only [Bank.bandGain, gain, Bank.bandPole, metamerBank]
  exact div_ne_zero (by norm_num) hden

/-- [proved-derived; formal-checked] **Metamers that sound different.** `A = (1, i)` and
`A' = (i, 1)` carry the same current in the same two modes with the quadratures exchanged. The
colour receiver sums its quadratic response *across* modes, so it cannot see the exchange and
returns the identical triple `(1, 1, 2)`. `metamerBank` consumes **both** modes, at `κ = (1, 2)`, so
its excitation is `1 + 2i` against `2 + i`: the same modulus, reflected in the diagonal, and a
different current. Equal colour does not imply equal timbre. -/
theorem metamer_sounds_different :
    colour ![1, Complex.I] = colour ![Complex.I, 1]
      ∧ metamerBank.timbre ![1, Complex.I] ≠ metamerBank.timbre ![Complex.I, 1] := by
  constructor
  · funext i
    fin_cases i <;>
      simp [colour, Fin.sum_univ_two, Complex.I_re, Complex.I_im]
  · intro h
    have h0 := congrFun h 0
    have hg : metamerBank.bandGain 0 ≠ 0 := bandGain_metamerBank_ne_zero
    simp only [Bank.timbre, Bank.advance, Bank.drive, Fin.sum_univ_two, metamerBank,
      Pi.zero_apply, mul_zero, zero_add] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_one,
      Complex.ofReal_ofNat, one_mul] at h0
    have hone := mul_left_cancel₀ hg h0
    have himg := congrArg Complex.im hone
    simp at himg

/-- [proved-derived; formal-checked] **Unisons that look different.** `A = (1, 0)` and
`A' = (1, 1)` differ only on mode `1`, which no resonator in `workedBank` couples to. The bank's
excitation, and therefore its whole future, is identical; the colour receiver's response changes
from `(1, 0, 1)` to `(2, 1, 5)`. Equal timbre does not imply equal colour. -/
theorem unison_looks_different :
    workedBank.timbre ![1, 0] = workedBank.timbre ![1, 1]
      ∧ colour ![(1 : ℂ), 0] ≠ colour ![(1 : ℂ), 1] := by
  constructor
  · funext b
    fin_cases b
    simp [Bank.timbre, Bank.advance, Bank.drive, Fin.sum_univ_two, workedBank]
  · intro h
    have h0 := congrFun h 0
    simp [colour, Fin.sum_univ_two] at h0

/-- [proved-derived; formal-checked] **A change of mode population moves both receivers.** The two
maps are readings of one current, so a change that the bank consumes is generally visible to
both; neither refines the other, and neither is a function of the other. -/
theorem population_change_moves_both :
    colour ![(1 : ℂ), 0] ≠ colour ![(2 : ℂ), 0]
      ∧ workedBank.timbre ![1, 0] ≠ workedBank.timbre ![2, 0] := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp [colour, Fin.sum_univ_two] at h0
    norm_num at h0
  · intro h
    have h0 := congrFun h 0
    have hg : workedBank.bandGain 0 ≠ 0 := bandGain_workedBank_ne_zero
    simp only [Bank.timbre, Bank.advance, Bank.drive, Fin.sum_univ_two, workedBank,
      Pi.zero_apply, mul_zero, zero_add] at h0
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_one,
      Complex.ofReal_zero, one_mul, zero_mul, add_zero] at h0
    have := mul_left_cancel₀ hg h0
    norm_num at this

end Lineage

/-! ## Axiom audit

[definition] Every theorem this owner states is checked to depend on nothing beyond Lean's three
standard axioms. No `sorry`, no `axiom`, no `native_decide`.
-/

section Axioms

#print axioms cayley_den_ne_zero
#print axioms normSq_cayley_lt_one
#print axioms normSq_cayley_eq_one
#print axioms trace_realBlock
#print axioms det_realBlock
#print axioms charpoly_realBlock
#print axioms rateForm_realBlock
#print axioms Bank.drive_add
#print axioms Bank.run_causal
#print axioms Bank.run_add
#print axioms Bank.pressure_add
#print axioms energy_advance_le
#print axioms energy_advance_lt
#print axioms colour_does_not_distribute
#print axioms quantize_then_superpose_ne_superpose_then_quantize
#print axioms bandGain_workedBank_ne_zero
#print axioms bandGain_metamerBank_ne_zero
#print axioms metamer_sounds_different
#print axioms unison_looks_different
#print axioms population_change_moves_both

end Axioms

end Holonics.Foundation.AcousticReceiver

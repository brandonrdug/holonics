import Holonics.Physics.InformationDifference
import Holonics.Computation.HolonicAdjointNormalization
import Holonics.Geometry.CrossRatio
import Holonics.Objects.Ratio.ExponentialKernel
import Holonics.Objects.Ratio.GaugeCalculus
import Holonics.Transport.JetStaircase
import Mathlib.Analysis.Quaternion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The ratio object: loss is the logarithm of a Holon ratio, and the ratio is a calculus

[definition] Object 9 of `docs/ELEMENTARY_OBJECTS.md`. A ratio compares two Holon readings and is
carried as the undivided pair (`Geometry/CrossRatio.RatioPresentation`). Its logarithm is a lift
carried as data, with the winding as its branch (`Objects/Ratio/ExponentialKernel`); its first
order is the Maurer–Cartan form `R⁻¹dR`, which is the pure-gauge term of the gauge owner
(`Objects/Ratio/GaugeCalculus`); its higher orders are the jet of the log ratio, read
continuously by `iteratedDeriv` and on the tick lattice by `Transport/JetStaircase`.

This module joins those owners; it founds no second softmax, cross-entropy or gauge.

Convention throughout, following `ℓ = log Ĝ_(T←H)`: `T` is the target (observed) Holon and
`H` the produced one. In the owner's `crossEntropy`/`liftedCrossEntropy` the first argument is the
target and the second the produced section.

1. **Logit covector.** [proved-derived; formal-checked] For the produced receiver
   `p = face s` (`Computation/HolonicAdjointNormalization.NormalizedExponential`), the surprisal
   `−log p_t` has section-line derivative `E_p[d] − d_t`, hence coordinate derivative
   `p_j − [t = j]` (`hasDerivAt_targetSurprisal_coordinate`); a positive target section `T` gives
   `p_j − T_j` (`hasDerivAt_crossEntropy_coordinate`). Both compose
   `hasDerivAt_face_mass_sectionLine`. The one-hot target is not a `PositiveProbabilitySection`;
   it is kept as the one-index receiver.
2. **Lifted cross-entropy is the target expectation of a lifted log.** With amplitude
   `z_i = √q_i e^{iθ_i}` and lift `log̃ z_i = (log q_i)/2 + iθ_i` (`exp_liftedLog`),
   `liftedCrossEntropy T H θ = −(2/ln 2) Σ T_i log̃ z^H_i`, and the excess over the target is
   `(2/ln 2) Σ T_i ℓ_i` with `ℓ_i = log̃(z^T_i / z^H_i)` (`liftedCrossEntropy_excess_eq_logRatio`).
3. **Winding.** A lift shift `θ_i ↦ θ_i + 2πk_i` moves only the phase face, by
   `−(4π/ln 2) Σ p_i k_i`; amplitudes agree exactly when the lifts differ by whole turns
   (`amplitude_eq_iff_winding`, via `Turn`); the principal logarithm returns the lift iff it lies
   in `(−π, π]` (`principalLog_amplitude_iff`). A concrete pair of lifts with equal amplitudes and
   distinct lifted cross-entropy is exhibited (`winding_separates_liftedCrossEntropy`).
4. **Undivided pair.** The log fibre of a ratio pair is empty for `(num ≠ 0, 0)`, everything for
   `(0, 0)`, and a `2πiℤ`-torsor when the denominator is a unit, where every lift exponentiates to
   the owner's `fractionalChart`; the fibre is projective and additive under composition.
4b. **The join: loss is the log of the Holon ratio.** Each `ℓ_i` lies in the log fibre of the
   undivided pair `(z^T_i : z^H_i)` (`logRatio_mem_logFibre`). Along a logit coordinate `j` of
   `H = face s`, the ratio `R_i = z^T_i / z^H_i` has `R_i⁻¹R_i' = (H_j − [i = j])/2`
   (`ratio_logDerivative_logit`, through `lift_deriv_eq_logDeriv`), and the logit derivative of the
   real part of the loss is `(H_j − T_j)/ln 2 = (2/ln 2) Σ T_i Re(R_i⁻¹∂_j R_i)`
   (`lossCovector_eq_expected_logDerivative`): the produced-minus-target covector is the target
   expectation of the ratio's logarithmic derivative. The phase face of `R⁻¹dR` is zero along a
   logit because the logits do not move the lifts.
5. **First order and jet.** A lift's derivative is `R⁻¹R'` whichever lift is used
   (`lift_deriv_eq_logDeriv`). For gauges, the log derivative of a product is the gauge transform
   of the first factor's log derivative by the second's inverse
   (`logDerivative_mul_eq_gaugeTransform`), with a quaternion witness in which the conjugation is
   visible (`logDerivative_mul_ne_sum`). The second jet is `R''/R − (R'/R)²`
   (`logJet_two`); orders `≥ 1` are winding-blind. For `R = e^{at + bt²/2}` the jet is
   `(a + bt, b, 0)`, and the unit tick lattice reads the same `b` and `0` through `JetStaircase`.

[definition] Reading of the jet: when the log ratio is a position-like coordinate, its first,
second and third derivatives are called velocity, acceleration and jerk. Nothing here asserts a
kinematic law; those words name orders of the jet only.

[open] A phase-moving covector (the imaginary part of `R⁻¹dR` when the produced lifts depend on
the parameters) is not derived here. The Schwarzian (second-order projective invariant of the
cross-ratio), a branch-choosing theorem for continuous lifts of nonvanishing `R` (existence of
`L`), and a matrix-valued `log` beyond the gauge/log-derivative level are not proved here.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.Objects.Ratio

open scoped BigOperators
open Holonics
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Physics.InformationDifference

/-! ## 1. The logit covector of the normalized receiver -/

section LogitCovector

variable {Index : Type*} [Fintype Index] [Nonempty Index]

open NormalizedExponential

/-- [definition] The surprisal of the target index `t` under the normalized receiver of `s`. -/
def targetSurprisal (s : Index → ℝ) (t : Index) : ℝ :=
  -Real.log ((face s).mass t)

/-- [proved-derived; formal-checked] Surprisal is the partition logarithm minus the target
potential (`log_face_mass`). -/
theorem targetSurprisal_eq (s : Index → ℝ) (t : Index) :
    targetSurprisal s t = Real.log (partition s) - s t := by
  rw [targetSurprisal, log_face_mass]
  ring

/-- [proved-derived; formal-checked] Along the section line `s + x d`, the surprisal has
derivative `E_p[d] − d_t`. Composes `hasDerivAt_face_mass_sectionLine` with the logarithm. -/
theorem hasDerivAt_targetSurprisal_sectionLine (s d : Index → ℝ) (t : Index) :
    HasDerivAt (fun x => targetSurprisal (fun j => s j + x * d j) t)
      (expectation (face s) d - d t) 0 := by
  have h := hasDerivAt_face_mass_sectionLine s d t
  have hne : (face (fun j => s j + (0 : ℝ) * d j)).mass t ≠ 0 := (face _).ne_zero t
  have hl := (h.log hne).neg
  have hs : (fun j => s j + (0 : ℝ) * d j) = s := by funext j; ring
  rw [hs] at hl
  refine hl.congr_deriv ?_
  have hp := (face s).ne_zero t
  simp only [laplacianReturn]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The cross-entropy logit gradient.** Along coordinate `j`,
`∂/∂s_j (−log p_t) = p_j − [t = j]`. -/
theorem hasDerivAt_targetSurprisal_coordinate [DecidableEq Index]
    (s : Index → ℝ) (t j : Index) :
    HasDerivAt (fun x => targetSurprisal (fun i => s i + x * (Pi.single j (1 : ℝ) : Index → ℝ) i) t)
      ((face s).mass j - if t = j then 1 else 0) 0 := by
  refine (hasDerivAt_targetSurprisal_sectionLine s (Pi.single j (1 : ℝ)) t).congr_deriv ?_
  congr 1
  · simp [expectation, Pi.single_apply]
  · simp [Pi.single_apply]

/-- [proved-derived; formal-checked] For a positive target section `target` (the observed
Holon) and the produced receiver `face s`, the cross-entropy `H(target, face s)` has section-line
derivative `E_produced[d] − E_target[d]`. -/
theorem hasDerivAt_crossEntropy_sectionLine (target : PositiveProbabilitySection Index)
    (s d : Index → ℝ) :
    HasDerivAt (fun x => crossEntropy target (face (fun j => s j + x * d j)))
      (expectation (face s) d - expectation target d) 0 := by
  have hterm : ∀ t ∈ (Finset.univ : Finset Index),
      HasDerivAt (fun x => target.mass t * targetSurprisal (fun j => s j + x * d j) t)
        (target.mass t * (expectation (face s) d - d t)) 0 :=
    fun t _ => (hasDerivAt_targetSurprisal_sectionLine s d t).const_mul (target.mass t)
  have hsum := HasDerivAt.fun_sum hterm
  have hfun : (fun x => crossEntropy target (face (fun j => s j + x * d j))) =
      (fun x => ∑ t, target.mass t * targetSurprisal (fun j => s j + x * d j) t) := by
    funext x
    simp only [crossEntropy, targetSurprisal, mul_neg, Finset.sum_neg_distrib]
  rw [hfun]
  refine hsum.congr_deriv ?_
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, target.normalized, one_mul,
    expectation]

/-- [proved-derived; formal-checked] Coordinate form:
`∂/∂s_j H(target, face s) = (face s)_j − target_j`, produced minus target. -/
theorem hasDerivAt_crossEntropy_coordinate [DecidableEq Index]
    (target : PositiveProbabilitySection Index) (s : Index → ℝ) (j : Index) :
    HasDerivAt
      (fun x => crossEntropy target
        (face (fun i => s i + x * (Pi.single j (1 : ℝ) : Index → ℝ) i)))
      ((face s).mass j - target.mass j) 0 := by
  refine (hasDerivAt_crossEntropy_sectionLine target s (Pi.single j (1 : ℝ))).congr_deriv ?_
  congr 1 <;> simp [expectation, Pi.single_apply]

/-- [proved-derived; formal-checked] The logit covector `produced − target` carries no total
current: the common additive (gauge) direction pairs to zero. -/
theorem sum_logitCovector (target : PositiveProbabilitySection Index) (s : Index → ℝ) :
    ∑ j, ((face s).mass j - target.mass j) = 0 := by
  rw [Finset.sum_sub_distrib, (face s).normalized, target.normalized, sub_self]

/-- Witness: the uniform binary receiver `s = 0` has mass `1/2` on each sheet. -/
theorem face_zero_bool (b : Bool) : (face (fun _ : Bool => (0 : ℝ))).mass b = 1 / 2 := by
  simp only [face, partition, Fintype.sum_bool, Real.exp_zero]
  norm_num

/-- [proved-derived; formal-checked] Witness: at `s = 0` over `Bool` with target `true`, the
logit covector is `(1/2, −1/2)`; it is nonzero, so the derivative carries a real return. -/
theorem logitCovector_witness :
    HasDerivAt (fun x => targetSurprisal
        (fun i => (fun _ : Bool => (0 : ℝ)) i + x * (Pi.single true (1 : ℝ) : Bool → ℝ) i) true)
      (-(1 / 2)) 0 ∧
    HasDerivAt (fun x => targetSurprisal
        (fun i => (fun _ : Bool => (0 : ℝ)) i + x * (Pi.single false (1 : ℝ) : Bool → ℝ) i) true)
      (1 / 2) 0 := by
  constructor
  · refine (hasDerivAt_targetSurprisal_coordinate _ true true).congr_deriv ?_
    rw [face_zero_bool]; norm_num
  · refine (hasDerivAt_targetSurprisal_coordinate _ true false).congr_deriv ?_
    rw [face_zero_bool]; norm_num

end LogitCovector

/-! ## 2. The lifted cross-entropy is the expectation of a lifted log amplitude -/

section LiftedLog

variable {Index : Type*} [Fintype Index]

/-- [definition] The amplitude `√q_i e^{iθ_i}` of a positive section with a phase lift. -/
def amplitude (q : PositiveProbabilitySection Index) (phase : Index → ℝ) (i : Index) : ℂ :=
  (Real.sqrt (q.mass i) : ℂ) * Complex.exp (phase i * Complex.I)

/-- [definition] The lifted logarithm of that amplitude, `(log q_i)/2 + iθ_i`. The lift is
carried as data; it is not `Complex.log`. -/
def liftedLog (q : PositiveProbabilitySection Index) (phase : Index → ℝ) (i : Index) : ℂ :=
  ⟨Real.log (q.mass i) / 2, phase i⟩

theorem liftedLog_eq (q : PositiveProbabilitySection Index) (phase : Index → ℝ) (i : Index) :
    liftedLog q phase i = ((Real.log (q.mass i) / 2 : ℝ) : ℂ) + (phase i : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [liftedLog]

/-- [proved-derived; formal-checked] The lift is a genuine logarithm of the amplitude. -/
theorem exp_liftedLog (q : PositiveProbabilitySection Index) (phase : Index → ℝ) (i : Index) :
    Complex.exp (liftedLog q phase i) = amplitude q phase i := by
  rw [liftedLog_eq, Complex.exp_add, ← Complex.ofReal_exp, amplitude]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (q.positive i)]
  ring_nf

theorem amplitude_ne_zero (q : PositiveProbabilitySection Index) (phase : Index → ℝ)
    (i : Index) : amplitude q phase i ≠ 0 := by
  rw [← exp_liftedLog]; exact Complex.exp_ne_zero _

/-- [proved-derived; formal-checked] **Lifted cross-entropy is the log of an amplitude, read by
the target.** In the owner's convention the first argument is the target (observed) section and
the second the produced one: `liftedCrossEntropy target produced θ = −(2/ln 2) Σ target_i log̃ z_i`
with `z_i = √produced_i e^{iθ_i}`. -/
theorem liftedCrossEntropy_eq_liftedLog (target produced : PositiveProbabilitySection Index)
    (phase : Index → ℝ) :
    liftedCrossEntropy target produced phase =
      -((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (target.mass i : ℂ) * liftedLog produced phase i := by
  apply Complex.ext
  · simp only [liftedCrossEntropy_real, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
      Complex.neg_im, Complex.ofReal_im, Complex.re_sum, Complex.im_sum, liftedLog, zero_mul,
      sub_zero, neg_zero, crossEntropy]
    rw [show (∑ i, target.mass i * (Real.log (produced.mass i) / 2)) =
        (∑ i, target.mass i * Real.log (produced.mass i)) / 2 by
      rw [Finset.sum_div]; congr 1; funext i; ring]
    ring
  · simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, Complex.re_sum, Complex.im_sum, liftedLog, zero_mul, neg_zero,
      add_zero]
    change -(2 / Real.log 2) * phaseMean target phase = _
    simp [phaseMean]

/-- [definition] The lifted log ratio `ℓ_i = log̃ z^T_i − log̃ z^H_i` of the target amplitude
over the produced amplitude, i.e. a lift of `log Ĝ_(T←H)` channel by channel. -/
def logRatio (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (i : Index) : ℂ :=
  liftedLog target targetPhase i - liftedLog produced producedPhase i

/-- [proved-derived; formal-checked] The lifted log ratio exponentiates to `z^T_i / z^H_i`. -/
theorem exp_logRatio (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (i : Index) :
    Complex.exp (logRatio target produced targetPhase producedPhase i) =
      amplitude target targetPhase i / amplitude produced producedPhase i := by
  rw [logRatio, Complex.exp_sub, exp_liftedLog, exp_liftedLog]

/-- [proved-derived; formal-checked] **The excess is the target expectation of the log ratio.**
`liftedCrossEntropy T H θ_H − liftedCrossEntropy T T θ_T = (2/ln 2) Σ T_i ℓ_i` with
`ℓ_i = log̃(z^T_i / z^H_i)`; its real part is `KL(T‖H)/ln 2` by the owner's
`liftedCrossEntropy_excess`. -/
theorem liftedCrossEntropy_excess_eq_logRatio (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) :
    liftedCrossEntropy target produced producedPhase -
        liftedCrossEntropy target target targetPhase =
      ((2 / Real.log 2 : ℝ) : ℂ) *
        ∑ i, (target.mass i : ℂ) * logRatio target produced targetPhase producedPhase i ∧
    (liftedCrossEntropy target produced producedPhase -
        liftedCrossEntropy target target targetPhase).re =
      klDivergence target produced / Real.log 2 := by
  constructor
  · rw [liftedCrossEntropy_eq_liftedLog, liftedCrossEntropy_eq_liftedLog]
    simp only [logRatio, mul_sub, Finset.sum_sub_distrib]
    ring
  · rw [liftedCrossEntropy_excess]

end LiftedLog

/-! ## 3. Winding: the phase face carries it, the amplitude deletes it -/

section Winding

variable {Index : Type*} [Fintype Index]

/-- [definition] Shift every lift by whole turns `k_i`. -/
def windShift (phase : Index → ℝ) (turns : Index → ℤ) (i : Index) : ℝ :=
  phase i + 2 * Real.pi * turns i

/-- [proved-derived; formal-checked] The code-length face does not see a winding shift. This
holds definitionally because the real part of `liftedCrossEntropy` does not read the phase. -/
theorem liftedCrossEntropy_windShift_re (p q : PositiveProbabilitySection Index)
    (phase : Index → ℝ) (turns : Index → ℤ) :
    (liftedCrossEntropy p q (windShift phase turns)).re = (liftedCrossEntropy p q phase).re :=
  rfl

/-- [proved-derived; formal-checked] The phase face moves by exactly `−(4π/ln 2) Σ p_i k_i`. -/
theorem liftedCrossEntropy_windShift_im (p q : PositiveProbabilitySection Index)
    (phase : Index → ℝ) (turns : Index → ℤ) :
    (liftedCrossEntropy p q (windShift phase turns)).im =
      (liftedCrossEntropy p q phase).im -
        (4 * Real.pi / Real.log 2) * ∑ i, p.mass i * (turns i : ℝ) := by
  change -(2 / Real.log 2) * phaseMean p (windShift phase turns) =
    -(2 / Real.log 2) * phaseMean p phase - _
  have : phaseMean p (windShift phase turns) =
      phaseMean p phase + 2 * Real.pi * ∑ i, p.mass i * (turns i : ℝ) := by
    simp only [phaseMean, windShift, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this]
  ring

/-- [proved-derived; formal-checked] A whole-turn shift is invisible to the amplitude
(`ExponentialKernel.exp_eq_one_iff_integer_period`). -/
theorem amplitude_windShift (q : PositiveProbabilitySection Index) (phase : Index → ℝ)
    (turns : Index → ℤ) (i : Index) :
    amplitude q (windShift phase turns) i = amplitude q phase i := by
  have hshift : liftedLog q (windShift phase turns) i =
      liftedLog q phase i + (turns i : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [liftedLog_eq, liftedLog_eq, windShift]
    push_cast
    ring
  have hturn : Complex.exp ((turns i : ℂ) * (2 * Real.pi * Complex.I)) = 1 :=
    (ExponentialKernel.exp_eq_one_iff_integer_period _).mpr ⟨turns i, rfl⟩
  rw [← exp_liftedLog, ← exp_liftedLog, hshift, Complex.exp_add, hturn, mul_one]

/-- [proved-derived; formal-checked] **The amplitude loses exactly the winding.** Two lifts give
the same amplitude iff they differ by a whole number of turns. -/
theorem amplitude_eq_iff_winding (q : PositiveProbabilitySection Index)
    (phase phase' : Index → ℝ) (i : Index) :
    amplitude q phase i = amplitude q phase' i ↔
      ∃ k : ℤ, phase' i = phase i + 2 * Real.pi * k := by
  constructor
  · intro h
    rw [← exp_liftedLog, ← exp_liftedLog] at h
    have h1 : Complex.exp (liftedLog q phase' i - liftedLog q phase i) = 1 := by
      rw [Complex.exp_sub, ← h, div_self (Complex.exp_ne_zero _)]
    obtain ⟨k, hk⟩ := (ExponentialKernel.exp_eq_one_iff_integer_period _).mp h1
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simp [liftedLog] at him
    linarith
  · rintro ⟨k, hk⟩
    have hsame : amplitude q phase' i = amplitude q (windShift phase (fun _ => k)) i := by
      simp only [amplitude, windShift, hk]
    rw [hsame, amplitude_windShift]

/-- [proved-derived; formal-checked] The principal logarithm returns the lift **iff** the lift
lies in the principal window `(−π, π]`; outside it the winding is not recoverable from the
amplitude. -/
theorem principalLog_amplitude_iff (q : PositiveProbabilitySection Index) (phase : Index → ℝ)
    (i : Index) :
    Complex.log (amplitude q phase i) = liftedLog q phase i ↔
      -Real.pi < phase i ∧ phase i ≤ Real.pi := by
  constructor
  · intro h
    have him := congrArg Complex.im h
    rw [Complex.log_im] at him
    have him' : Complex.arg (amplitude q phase i) = phase i := by simpa [liftedLog] using him
    rw [← him']
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  · rintro ⟨hlo, hhi⟩
    rw [← exp_liftedLog]
    exact Complex.log_exp (by simpa [liftedLog] using hlo) (by simpa [liftedLog] using hhi)

/-- [proved-derived; formal-checked] Witness: two lifts on the uniform binary section with
identical amplitudes (hence identical principal logs) and different lifted cross-entropy. The
difference is the winding, `−(4π/ln 2)`. -/
theorem winding_separates_liftedCrossEntropy :
    (∀ i, amplitude halfSection (fun _ => 0) i =
      amplitude halfSection (windShift (fun _ => 0) (fun _ => 1)) i) ∧
    liftedCrossEntropy halfSection halfSection (fun _ => 0) ≠
      liftedCrossEntropy halfSection halfSection (windShift (fun _ => 0) (fun _ => 1)) := by
  refine ⟨fun i => (amplitude_windShift _ _ _ i).symm, ?_⟩
  intro h
  have him := congrArg Complex.im h
  rw [liftedCrossEntropy_windShift_im] at him
  have hsum : (∑ i : Bool, halfSection.mass i * ((1 : ℤ) : ℝ)) = 1 := by
    simp [halfSection]
  rw [hsum] at him
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : 4 * Real.pi / Real.log 2 * 1 = 0 := by linarith
  have hpos : 0 < 4 * Real.pi / Real.log 2 * 1 := by
    have := Real.pi_pos; positivity
  linarith

end Winding

/-! ## 4. The ratio as an undivided pair; its log only on the unit chart -/

section UndividedPair

/-- [definition] A ratio of two complex Holon readings, produced over target, kept undivided. -/
def holonRatio (produced target : ℂ) : RatioPresentation ℂ := ⟨produced, target⟩

/-- [definition] The log fibre of a ratio pair: every `ℓ` with `e^ℓ · den = num`. No division
is performed. -/
def logFibre (r : RatioPresentation ℂ) : Set ℂ :=
  {ℓ | Complex.exp ℓ * r.den = r.num}

/-- [proved-derived; formal-checked] Refusal: a nonzero numerator over a zero denominator has
no logarithm. -/
theorem logFibre_eq_empty_of_den_eq_zero {r : RatioPresentation ℂ} (hden : r.den = 0)
    (hnum : r.num ≠ 0) : logFibre r = ∅ := by
  ext ℓ
  simp only [logFibre, hden, mul_zero, Set.mem_empty_iff_false, iff_false]
  exact fun h => hnum h.symm

/-- [proved-derived; formal-checked] Refusal: the pair `(0, 0)` has every `ℓ` in its fibre; no
log is determined. -/
theorem logFibre_zero_zero : logFibre (holonRatio 0 0) = Set.univ := by
  ext ℓ; simp [logFibre, holonRatio]

/-- [proved-derived; formal-checked] On the unit chart every lift exponentiates to the owner's
fractional chart `num · den⁻¹`. -/
theorem exp_eq_fractionalChart {r : RatioPresentation ℂ}
    (hunit : IsUnit (0 * r.num + 1 * r.den)) {ℓ : ℂ} (hℓ : ℓ ∈ logFibre r) :
    Complex.exp ℓ = RatioPresentation.fractionalChart 1 0 0 1 r hunit := by
  have hchart := RatioPresentation.fractionalChart_mul_denominator 1 0 0 1 r hunit
  have hden : r.den ≠ 0 := by
    have := hunit.ne_zero; simpa using this
  simp only [zero_mul, one_mul, zero_add, add_zero] at hchart
  have hℓ' : Complex.exp ℓ * r.den = r.num := hℓ
  exact mul_right_cancel₀ hden (hℓ'.trans hchart.symm)

/-- [proved-derived; formal-checked] On the unit chart with nonzero numerator the fibre is
inhabited (by the principal log of the quotient). -/
theorem logFibre_nonempty {r : RatioPresentation ℂ} (hden : r.den ≠ 0) (hnum : r.num ≠ 0) :
    (logFibre r).Nonempty := by
  refine ⟨Complex.log (r.num / r.den), ?_⟩
  change Complex.exp (Complex.log (r.num / r.den)) * r.den = r.num
  rw [Complex.exp_log (div_ne_zero hnum hden), div_mul_cancel₀ _ hden]

/-- [proved-derived; formal-checked] On the unit chart the fibre is a `2πiℤ`-torsor: two lifts
differ exactly by whole turns (`Turn`). -/
theorem logFibre_torsor {r : RatioPresentation ℂ} (hden : r.den ≠ 0) {ℓ ℓ' : ℂ}
    (hℓ : ℓ ∈ logFibre r) :
    ℓ' ∈ logFibre r ↔ ∃ n : ℤ, ℓ' = ℓ + n * (2 * Real.pi * Complex.I) := by
  have hℓ' : Complex.exp ℓ * r.den = r.num := hℓ
  constructor
  · intro h
    have h' : Complex.exp ℓ' * r.den = r.num := h
    have heq : Complex.exp ℓ' = Complex.exp ℓ :=
      mul_right_cancel₀ hden (h'.trans hℓ'.symm)
    have h1 : Complex.exp (ℓ' - ℓ) = 1 := by
      rw [Complex.exp_sub, heq, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := (ExponentialKernel.exp_eq_one_iff_integer_period _).mp h1
    exact ⟨n, by rw [← hn]; ring⟩
  · rintro ⟨n, rfl⟩
    change Complex.exp (ℓ + n * (2 * Real.pi * Complex.I)) * r.den = r.num
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact hℓ'

/-- [proved-derived; formal-checked] The fibre is projective: common nonzero scaling of the
pair (`RatioPresentation.scale`) does not change it. -/
theorem logFibre_scale (r : RatioPresentation ℂ) {u : ℂ} (hu : u ≠ 0) :
    logFibre (r.scale u) = logFibre r := by
  ext ℓ
  change Complex.exp ℓ * (u * r.den) = u * r.num ↔ Complex.exp ℓ * r.den = r.num
  constructor
  · intro h
    apply mul_left_cancel₀ hu
    rw [← h]; ring
  · intro h
    rw [← h]; ring

/-- [proved-derived; formal-checked] **Log ratios add along a composed comparison.** If `ℓ₁`
lifts `a : b` and `ℓ₂` lifts `b : c`, then `ℓ₁ + ℓ₂` lifts `a : c`. -/
theorem logFibre_comp {a b c ℓ₁ ℓ₂ : ℂ} (h₁ : ℓ₁ ∈ logFibre (holonRatio a b))
    (h₂ : ℓ₂ ∈ logFibre (holonRatio b c)) : ℓ₁ + ℓ₂ ∈ logFibre (holonRatio a c) := by
  have h₁' : Complex.exp ℓ₁ * b = a := h₁
  have h₂' : Complex.exp ℓ₂ * c = b := h₂
  change Complex.exp (ℓ₁ + ℓ₂) * c = a
  rw [Complex.exp_add, mul_assoc, h₂', h₁']

/-- [proved-derived; formal-checked] Witness: `(1 : 0)` and `(2 : 0)` are distinct undivided
pairs whose log charts are both refused; the pair retains what the chart cannot. -/
theorem undividedPair_retains_refused :
    holonRatio 1 0 ≠ holonRatio 2 0 ∧
      logFibre (holonRatio 1 0) = ∅ ∧ logFibre (holonRatio 2 0) = ∅ := by
  refine ⟨?_, logFibre_eq_empty_of_den_eq_zero rfl one_ne_zero,
    logFibre_eq_empty_of_den_eq_zero rfl two_ne_zero⟩
  intro h
  have := congrArg RatioPresentation.num h
  norm_num [holonRatio] at this

end UndividedPair

/-! ## 4b. The join: loss is the logarithm of the Holon ratio, and its logit covector is the real
part of the ratio's logarithmic derivative -/

section LossIsLogRatio

/-- [proved-derived; formal-checked] **The derivative of a lift is the log derivative.** If `L`
is any lift of `R` (`exp ∘ L = R`) then `L' = R⁻¹ R'`. The first order does not depend on which
lift (winding branch) is carried. -/
theorem lift_deriv_eq_logDeriv {L R : ℝ → ℂ} (hlift : ∀ s, Complex.exp (L s) = R s)
    {t : ℝ} {ℓ' R' : ℂ} (hL : HasDerivAt L ℓ' t) (hR : HasDerivAt R R' t) :
    ℓ' = (R t)⁻¹ * R' := by
  have hR' : HasDerivAt R (Complex.exp (L t) * ℓ') t := by
    have hfun : R = fun s => Complex.exp (L s) := by funext s; exact (hlift s).symm
    rw [hfun]; exact hL.cexp
  have heq := hR.unique hR'
  rw [heq, ← hlift t, ← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]


variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] Each channel's lifted log ratio lies in the log fibre of the
undivided pair `(z^T_i : z^H_i)`: the lifted cross-entropy excess is read from the same ratio
object as §4. -/
theorem logRatio_mem_logFibre (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (i : Index) :
    logRatio target produced targetPhase producedPhase i ∈
      logFibre (holonRatio (amplitude target targetPhase i)
        (amplitude produced producedPhase i)) := by
  change Complex.exp _ * amplitude produced producedPhase i = amplitude target targetPhase i
  rw [exp_logRatio, div_mul_cancel₀ _ (amplitude_ne_zero _ _ _)]

variable [Nonempty Index] [DecidableEq Index]

open NormalizedExponential

/-- The produced receiver moved along logit coordinate `j`. -/
abbrev producedAlong (s : Index → ℝ) (j : Index) (x : ℝ) : PositiveProbabilitySection Index :=
  face (fun i => s i + x * (Pi.single j (1 : ℝ) : Index → ℝ) i)

/-- [proved-derived; formal-checked] Along logit coordinate `j`, the channel-`i` log ratio moves
by the real number `(p_j − [i = j])/2`, where `p = face s` is the produced receiver. -/
theorem hasDerivAt_logRatio_logit (target : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (s : Index → ℝ) (i j : Index) :
    HasDerivAt
      (fun x => logRatio target (producedAlong s j x) targetPhase producedPhase i)
      ((((face s).mass j - if i = j then 1 else 0) / 2 : ℝ) : ℂ) 0 := by
  have hreal : HasDerivAt
      (fun x => Real.log (target.mass i) / 2 +
        targetSurprisal (fun k => s k + x * (Pi.single j (1 : ℝ) : Index → ℝ) k) i / 2)
      (((face s).mass j - if i = j then 1 else 0) / 2) 0 := by
    simpa using ((hasDerivAt_targetSurprisal_coordinate s i j).div_const 2).const_add
      (Real.log (target.mass i) / 2)
  have hfun : (fun x => logRatio target (producedAlong s j x) targetPhase producedPhase i) =
      fun x => (((Real.log (target.mass i) / 2 +
        targetSurprisal (fun k => s k + x * (Pi.single j (1 : ℝ) : Index → ℝ) k) i / 2 : ℝ)
          : ℂ)) + ((targetPhase i - producedPhase i : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext
    · simp [logRatio, liftedLog, targetSurprisal]; ring
    · simp [logRatio, liftedLog]
  rw [hfun]
  exact hreal.ofReal_comp.add_const _

/-- [proved-derived; formal-checked] **`R⁻¹dR` of the Holon ratio along a logit.** For the channel
ratio `R_i(x) = z^T_i / z^H_i(x)`, the ratio is differentiable and its logarithmic derivative is
`R_i⁻¹ R_i' = (p_j − [i = j])/2`, via `lift_deriv_eq_logDeriv` (no branch of `log` is chosen). -/
theorem ratio_logDerivative_logit (target : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (s : Index → ℝ) (i j : Index) :
    ∃ R' : ℂ,
      HasDerivAt (fun x => amplitude target targetPhase i /
          amplitude (producedAlong s j x) producedPhase i) R' 0 ∧
        (amplitude target targetPhase i / amplitude (producedAlong s j 0) producedPhase i)⁻¹ *
            R' = ((((face s).mass j - if i = j then 1 else 0) / 2 : ℝ) : ℂ) := by
  have hL := hasDerivAt_logRatio_logit target targetPhase producedPhase s i j
  have hlift : ∀ x, Complex.exp (logRatio target (producedAlong s j x) targetPhase
      producedPhase i) = amplitude target targetPhase i /
        amplitude (producedAlong s j x) producedPhase i := fun x => exp_logRatio _ _ _ _ _
  have hR := hL.cexp
  simp only [hlift] at hR
  exact ⟨_, hR, (lift_deriv_eq_logDeriv hlift hL hR).symm⟩

/-- [proved-derived; formal-checked] **Loss is the logarithm of the Holon ratio, and its covector
is the ratio's logarithmic derivative.** With target `T` and produced `H = face s`:
the real part of the excess `(2/ln 2) Σ T_i ℓ_i` has logit derivative `(H_j − T_j)/ln 2`, and this
equals the target expectation of `Re(R_i⁻¹ ∂_j R_i)` scaled by `2/ln 2`. -/
theorem lossCovector_eq_expected_logDerivative (target : PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (s : Index → ℝ) (j : Index) :
    HasDerivAt
      (fun x => (liftedCrossEntropy target (producedAlong s j x) producedPhase -
        liftedCrossEntropy target target targetPhase).re)
      (((face s).mass j - target.mass j) / Real.log 2) 0 ∧
    (2 / Real.log 2) * ∑ i, target.mass i *
        (((face s).mass j - if i = j then 1 else 0) / 2) =
      ((face s).mass j - target.mass j) / Real.log 2 := by
  constructor
  · have hfun : (fun x => (liftedCrossEntropy target (producedAlong s j x) producedPhase -
        liftedCrossEntropy target target targetPhase).re) =
        fun x => crossEntropy target (producedAlong s j x) / Real.log 2 -
          crossEntropy target target / Real.log 2 := by
      funext x; rfl
    rw [hfun]
    have h := ((hasDerivAt_crossEntropy_coordinate target s j).div_const (Real.log 2)).sub_const
      (crossEntropy target target / Real.log 2)
    exact h
  · have hsum : ∑ i, target.mass i * (((face s).mass j - if i = j then 1 else 0) / 2) =
        ((face s).mass j - target.mass j) / 2 := by
      simp only [mul_div_assoc', ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, target.normalized, one_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    ring

end LossIsLogRatio

/-! ## 5. First order: the log derivative, the gauge, and the jet -/

section LogDerivative

open Holonics.Objects.HolonicGaugeCovariance
open Holonics.Geometry.HolonicConnectionCurvature
  (differential differential_mul Base Connection direction)

variable {n : ℕ} {𝔤 : Type*} [NormedRing 𝔤] [NormedAlgebra ℝ 𝔤]

/-- [definition] The log derivative (Maurer–Cartan form) `g⁻¹ ∂_i g` of a gauge. -/
def logDerivative (G : Gauge n 𝔤) : Connection n 𝔤 :=
  fun i x => G.ginv x * differential i G.g x

/-- [definition] The inverse gauge. -/
def inverseGauge (G : Gauge n 𝔤) : Gauge n 𝔤 where
  g := G.ginv
  ginv := G.g
  mul_inv := G.inv_mul
  inv_mul := G.mul_inv
  smooth := G.smooth_inv
  smooth_inv := G.smooth

/-- [definition] The pointwise product of two gauges. -/
def productGauge (G H : Gauge n 𝔤) : Gauge n 𝔤 where
  g x := G.g x * H.g x
  ginv x := H.ginv x * G.ginv x
  mul_inv x := by
    rw [mul_assoc, ← mul_assoc (H.g x), H.mul_inv, one_mul, G.mul_inv]
  inv_mul x := by
    rw [mul_assoc, ← mul_assoc (G.ginv x), G.inv_mul, one_mul, H.inv_mul]
  smooth := G.smooth.mul H.smooth
  smooth_inv := H.smooth_inv.mul G.smooth_inv

/-- [proved-derived; formal-checked] `R⁻¹dR` is the pure-gauge term `g∂g⁻¹` of the gauge
`g = R⁻¹` acting on the zero connection. -/
theorem logDerivative_eq_pureGauge (G : Gauge n 𝔤) (i : Fin n) (x : Base n) :
    logDerivative G i x = gaugeTransform (inverseGauge G) (fun _ _ => 0) i x := by
  simp [logDerivative, gaugeTransform, inverseGauge]

/-- [proved-derived; formal-checked] The second face of the same first order, through the
owner's differentiated unit law: `g⁻¹∂g = −(∂g⁻¹) g`. -/
theorem logDerivative_eq_neg_differential_inverse (G : Gauge n 𝔤) (i : Fin n) (x : Base n) :
    logDerivative G i x = -(differential i G.ginv x * G.g x) := by
  rw [G.differential_ginv i x, logDerivative]
  have h : G.ginv x * differential i G.g x * G.ginv x * G.g x =
      G.ginv x * differential i G.g x := by
    rw [mul_assoc, G.inv_mul, mul_one]
  rw [neg_mul, neg_neg, h]

/-- [proved-derived; formal-checked] **The product split.** For `R = g₁ g₂`,
`R⁻¹∂R = g₂⁻¹ (g₁⁻¹∂g₁) g₂ + g₂⁻¹∂g₂`: the log derivative of the product is the gauge transform
of the first factor's log derivative by `g₂⁻¹`. -/
theorem logDerivative_mul_eq_gaugeTransform (G H : Gauge n 𝔤) (i : Fin n) (x : Base n) :
    logDerivative (productGauge G H) i x =
      H.ginv x * logDerivative G i x * H.g x + logDerivative H i x ∧
    logDerivative (productGauge G H) i x =
      gaugeTransform (inverseGauge H) (logDerivative G) i x := by
  have hmul : differential i (fun y => G.g y * H.g y) x =
      G.g x * differential i H.g x + differential i G.g x * H.g x :=
    differential_mul (G.differentiableAt_g x) (H.differentiableAt_g x) i
  have hsplit : logDerivative (productGauge G H) i x =
      H.ginv x * logDerivative G i x * H.g x + logDerivative H i x := by
    change (H.ginv x * G.ginv x) * differential i (fun y => G.g y * H.g y) x = _
    rw [hmul, logDerivative, logDerivative]
    have hG : H.ginv x * G.ginv x * (G.g x * differential i H.g x) =
        H.ginv x * differential i H.g x := by
      rw [mul_assoc, ← mul_assoc (G.ginv x), G.inv_mul, one_mul]
    rw [mul_add, hG]
    noncomm_ring
  refine ⟨hsplit, ?_⟩
  rw [hsplit]
  simp [gaugeTransform, inverseGauge, logDerivative]

end LogDerivative

/-! ### A noncommutative witness: the conjugation in the split is visible -/

section QuaternionWitness

open Quaternion Holonics.Objects.HolonicGaugeCovariance
open Holonics.Geometry.HolonicConnectionCurvature
  (differential differential_mul Base Connection direction)

/-- The quaternion unit `i`. -/
def qI : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion unit `j`. -/
def qJ : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

@[simp] theorem qI_re : qI.re = 0 := rfl
@[simp] theorem qI_imI : qI.imI = 1 := rfl
@[simp] theorem qI_imJ : qI.imJ = 0 := rfl
@[simp] theorem qI_imK : qI.imK = 0 := rfl
@[simp] theorem qJ_re : qJ.re = 0 := rfl
@[simp] theorem qJ_imI : qJ.imI = 0 := rfl
@[simp] theorem qJ_imJ : qJ.imJ = 1 := rfl
@[simp] theorem qJ_imK : qJ.imK = 0 := rfl

/-- A rotating gauge `cos x₀ + sin x₀ · i` on the one-dimensional base. -/
def rotor : Gauge 1 ℍ[ℝ] where
  g x := Real.cos (x 0) • (1 : ℍ[ℝ]) + Real.sin (x 0) • qI
  ginv x := Real.cos (x 0) • (1 : ℍ[ℝ]) - Real.sin (x 0) • qI
  mul_inv x := by
    have h := Real.cos_sq_add_sin_sq (x 0)
    ext <;> simp <;> nlinarith [h]
  inv_mul x := by
    have h := Real.cos_sq_add_sin_sq (x 0)
    ext <;> simp <;> nlinarith [h]
  smooth := by
    have h0 : ContDiff ℝ 2 (fun x : Base 1 => x 0) := contDiff_apply ℝ ℝ 0
    exact ((Real.contDiff_cos.comp h0).smul contDiff_const).add
      ((Real.contDiff_sin.comp h0).smul contDiff_const)
  smooth_inv := by
    have h0 : ContDiff ℝ 2 (fun x : Base 1 => x 0) := contDiff_apply ℝ ℝ 0
    exact ((Real.contDiff_cos.comp h0).smul contDiff_const).sub
      ((Real.contDiff_sin.comp h0).smul contDiff_const)

/-- The constant gauge `j` (with inverse `−j`). -/
def constJ : Gauge 1 ℍ[ℝ] where
  g _ := qJ
  ginv _ := -qJ
  mul_inv _ := by ext <;> simp
  inv_mul _ := by ext <;> simp
  smooth := contDiff_const
  smooth_inv := contDiff_const

theorem differential_rotor (x : Base 1) :
    differential 0 rotor.g x = -Real.sin (x 0) • (1 : ℍ[ℝ]) + Real.cos (x 0) • qI := by
  have h0 : HasFDerivAt (fun y : Base 1 => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).hasFDerivAt
  have hc := ((Real.hasDerivAt_cos (x 0)).comp_hasFDerivAt x h0).smul_const (1 : ℍ[ℝ])
  have hs := ((Real.hasDerivAt_sin (x 0)).comp_hasFDerivAt x h0).smul_const qI
  have hsum : HasFDerivAt (fun y : Base 1 => Real.cos (y 0) • (1 : ℍ[ℝ]) + Real.sin (y 0) • qI)
      (((-Real.sin (x 0)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
          (1 : ℍ[ℝ]) +
        (Real.cos (x 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).smulRight
          qI) x := hc.add hs
  change fderiv ℝ (fun y : Base 1 => Real.cos (y 0) • (1 : ℍ[ℝ]) + Real.sin (y 0) • qI) x
    (direction 0) = _
  rw [hsum.fderiv]
  simp [direction]

theorem logDerivative_rotor (x : Base 1) : logDerivative rotor 0 x = qI := by
  rw [logDerivative, differential_rotor]
  have h := Real.cos_sq_add_sin_sq (x 0)
  change (Real.cos (x 0) • (1 : ℍ[ℝ]) - Real.sin (x 0) • qI) *
    (-Real.sin (x 0) • (1 : ℍ[ℝ]) + Real.cos (x 0) • qI) = qI
  ext <;> simp <;> nlinarith [h]

theorem logDerivative_constJ (x : Base 1) : logDerivative constJ 0 x = 0 := by
  simp [logDerivative, differential, constJ]

/-- [proved-derived; formal-checked] **Witness of the conjugation.** For `R = rotor · j`, the
log derivative is `−i`, whereas the sum of the factors' log derivatives is `i`: in a
noncommutative carrier the split is a gauge transform, not a sum. -/
theorem logDerivative_mul_ne_sum (x : Base 1) :
    logDerivative (productGauge rotor constJ) 0 x = -qI ∧
      logDerivative (productGauge rotor constJ) 0 x ≠
        logDerivative rotor 0 x + logDerivative constJ 0 x := by
  have hsplit := (logDerivative_mul_eq_gaugeTransform rotor constJ 0 x).1
  rw [logDerivative_rotor, logDerivative_constJ, add_zero] at hsplit
  have hval : logDerivative (productGauge rotor constJ) 0 x = -qI := by
    rw [hsplit]
    change -qJ * qI * qJ = -qI
    ext <;> simp
  refine ⟨hval, ?_⟩
  rw [hval, logDerivative_rotor, logDerivative_constJ, add_zero]
  intro h
  have := congrArg (fun q : ℍ[ℝ] => q.imI) h
  simp at this
  norm_num at this

end QuaternionWitness

/-! ### The jet of the log ratio -/

section Jet

/-- [definition] The order-`k` jet coordinate of a log lift `L`. Order 0 carries the branch;
orders 1, 2, 3 are read as velocity, acceleration and jerk of the log ratio. -/
def logJet (L : ℝ → ℂ) (k : ℕ) (t : ℝ) : ℂ := iteratedDeriv k L t

/-- [proved-derived; formal-checked] Orders `≥ 1` of the jet do not see a constant branch shift,
in particular a winding `2πi k`. -/
theorem logJet_const_add (L : ℝ → ℂ) (c : ℂ) {k : ℕ} (hk : 0 < k) (t : ℝ) :
    logJet (fun s => c + L s) k t = logJet L k t :=
  iteratedDeriv_const_add hk c

/-- [proved-derived; formal-checked] **The second jet is the derivative of the log derivative.**
For a `C²` lift `L` of `R = exp ∘ L`: `L'' = R''/R − (R'/R)²`, and `L' = R'/R`. -/
theorem logJet_two {L : ℝ → ℂ} (hL : ContDiff ℝ 2 L) (t : ℝ) :
    logJet L 1 t = deriv (fun s => Complex.exp (L s)) t / Complex.exp (L t) ∧
    logJet L 2 t =
      iteratedDeriv 2 (fun s => Complex.exp (L s)) t / Complex.exp (L t) -
        (deriv (fun s => Complex.exp (L s)) t / Complex.exp (L t)) ^ 2 := by
  have hd0 : Differentiable ℝ L := by
    simpa using hL.differentiable_iteratedDeriv 0 (by norm_num)
  have hd1 : Differentiable ℝ (deriv L) := by
    simpa [iteratedDeriv_one] using hL.differentiable_iteratedDeriv 1 (by norm_num)
  have hR : ∀ s, HasDerivAt (fun s => Complex.exp (L s))
      (Complex.exp (L s) * deriv L s) s := fun s => (hd0 s).hasDerivAt.cexp
  have hderivR : deriv (fun s => Complex.exp (L s)) =
      fun s => Complex.exp (L s) * deriv L s := by
    funext s; exact (hR s).deriv
  have hR2 : HasDerivAt (fun s => Complex.exp (L s) * deriv L s)
      (Complex.exp (L t) * deriv L t * deriv L t + Complex.exp (L t) * deriv (deriv L) t) t :=
    (hR t).mul (hd1 t).hasDerivAt
  have he := Complex.exp_ne_zero (L t)
  constructor
  · rw [logJet, iteratedDeriv_one, hderivR]
    field_simp
  · rw [logJet, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one,
      hderivR, hR2.deriv]
    field_simp
    ring

/-- The quadratic log ratio `ℓ(t) = a t + b t²/2`. -/
def quadraticLog (a b : ℂ) (t : ℝ) : ℂ := a * t + b * (t : ℂ) ^ 2 / 2

theorem hasDerivAt_quadraticLog (a b : ℂ) (t : ℝ) :
    HasDerivAt (quadraticLog a b) (a + b * t) t := by
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h := (hid.const_mul a).add (((hid.pow 2).const_mul b).div_const 2)
  refine h.congr_deriv ?_
  simp
  ring

theorem hasDerivAt_quadraticLog_velocity (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => a + b * (s : ℂ)) b t := by
  have hid : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  simpa using (hid.const_mul b).const_add a

/-- [proved-derived; formal-checked] **Witness jet.** For `R(t) = e^{at + bt²/2}` the log jet is
velocity `a + bt`, acceleration `b`, jerk `0`. -/
theorem quadraticLog_jet (a b : ℂ) (t : ℝ) :
    logJet (quadraticLog a b) 1 t = a + b * t ∧
      logJet (quadraticLog a b) 2 t = b ∧ logJet (quadraticLog a b) 3 t = 0 := by
  have h1 : deriv (quadraticLog a b) = fun s : ℝ => a + b * (s : ℂ) := by
    funext s; exact (hasDerivAt_quadraticLog a b s).deriv
  have h2 : deriv (fun s : ℝ => a + b * (s : ℂ)) = fun _ => b := by
    funext s; exact (hasDerivAt_quadraticLog_velocity a b s).deriv
  refine ⟨?_, ?_, ?_⟩
  · simp [logJet, iteratedDeriv_one, h1]
  · simp [logJet, iteratedDeriv_succ, h1, h2]
  · simp [logJet, iteratedDeriv_succ, h1, h2]

/-- [proved-derived; formal-checked] The witness satisfies the second-jet chain: the lift is
`C²` and its `R = e^{ℓ}` returns the acceleration `b` as `R''/R − (R'/R)²`. -/
theorem quadraticLog_chain (a b : ℂ) (t : ℝ) :
    iteratedDeriv 2 (fun s => Complex.exp (quadraticLog a b s)) t /
        Complex.exp (quadraticLog a b t) -
      (deriv (fun s => Complex.exp (quadraticLog a b s)) t /
        Complex.exp (quadraticLog a b t)) ^ 2 = b := by
  have hC : ContDiff ℝ 2 (quadraticLog a b) := by
    have hid : ContDiff ℝ 2 (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
    unfold quadraticLog
    exact (contDiff_const.mul hid).add ((contDiff_const.mul (hid.pow 2)).div_const 2)
  rw [← (logJet_two hC t).2]
  exact (quadraticLog_jet a b t).2.1

open Transport.JetStaircase

/-- The Newton coefficients `(0, a + b/2, b)` of the sampled quadratic log ratio. -/
def quadraticCoefficients (a b : ℚ) : ℕ → ℚ
  | 1 => a + b / 2
  | 2 => b
  | _ => 0

/-- The quadratic log ratio sampled on the unit tick lattice, over `ℚ`. -/
def sampledQuadraticLog (a b : ℚ) (m : ℕ) : ℚ := a * m + b * (m : ℚ) ^ 2 / 2

/-- [proved-derived; formal-checked] The sample is a Newton jet of order 2 with coefficients
`(0, a + b/2, b)` in the `JetStaircase` chart. -/
theorem sampledQuadraticLog_eq_ofCoefficients (a b : ℚ) :
    sampledQuadraticLog a b = ofCoefficients 2 (quadraticCoefficients a b) := by
  funext m
  simp only [sampledQuadraticLog, ofCoefficients, binom, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp [Nat.cast_choose_two, quadraticCoefficients]
  ring

/-- [proved-derived; formal-checked] **The tick lattice reads the same acceleration and jerk.**
The second difference of the sampled log ratio is the constant `b` (the continuous acceleration)
and its third difference vanishes (the continuous jerk), via `JetStaircase`. -/
theorem sampledQuadraticLog_differences (a b : ℚ) :
    (∀ m, (Delta^[2] (sampledQuadraticLog a b)) m = b) ∧
      Delta^[3] (sampledQuadraticLog a b) = fun _ => 0 := by
  rw [sampledQuadraticLog_eq_ofCoefficients]
  refine ⟨fun m => ?_, iteratedDelta_ofCoefficients_eq_zero 2 _⟩
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_zero_apply,
    delta_ofCoefficients, delta_ofCoefficients]
  simp [ofCoefficients, binom, quadraticCoefficients]

/-- [proved-derived; formal-checked] The continuous and lattice jets agree for rational
coefficients: acceleration `b` and zero jerk on both. -/
theorem jet_continuous_matches_lattice (a b : ℚ) (t : ℝ) (m : ℕ) :
    logJet (quadraticLog a b) 2 t = ((Delta^[2] (sampledQuadraticLog a b)) m : ℂ) ∧
      logJet (quadraticLog a b) 3 t = ((Delta^[3] (sampledQuadraticLog a b)) m : ℂ) := by
  obtain ⟨_, h2, h3⟩ := quadraticLog_jet (a : ℂ) (b : ℂ) t
  obtain ⟨d2, d3⟩ := sampledQuadraticLog_differences a b
  refine ⟨?_, ?_⟩
  · rw [h2, d2 m]
  · rw [h3, d3]; simp

end Jet

section Audit

#print axioms hasDerivAt_targetSurprisal_coordinate
#print axioms hasDerivAt_crossEntropy_coordinate
#print axioms logitCovector_witness
#print axioms exp_liftedLog
#print axioms liftedCrossEntropy_eq_liftedLog
#print axioms liftedCrossEntropy_excess_eq_logRatio
#print axioms liftedCrossEntropy_windShift_im
#print axioms amplitude_eq_iff_winding
#print axioms principalLog_amplitude_iff
#print axioms winding_separates_liftedCrossEntropy
#print axioms exp_eq_fractionalChart
#print axioms logFibre_torsor
#print axioms logFibre_scale
#print axioms logFibre_comp
#print axioms undividedPair_retains_refused
#print axioms logRatio_mem_logFibre
#print axioms hasDerivAt_logRatio_logit
#print axioms ratio_logDerivative_logit
#print axioms lossCovector_eq_expected_logDerivative
#print axioms lift_deriv_eq_logDeriv
#print axioms logDerivative_eq_neg_differential_inverse
#print axioms logDerivative_mul_eq_gaugeTransform
#print axioms logDerivative_mul_ne_sum
#print axioms logJet_two
#print axioms quadraticLog_jet
#print axioms quadraticLog_chain
#print axioms sampledQuadraticLog_differences
#print axioms jet_continuous_matches_lattice

end Audit

end Holonics.Objects.Ratio

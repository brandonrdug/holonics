import ElementaryHolonics.Objects.Ratio
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# The phase covector of the Holon ratio, and the continuous lift that carries it

[definition] Object 9 of `docs/ELEMENTARY_OBJECTS.md`, continuing `Objects/Ratio`. There the
logit derivative of the lifted cross-entropy excess was derived with the produced lifts held
fixed, so the phase face of `R⁻¹dR` was zero. Here the produced Holon moves along one parameter
`x ↦ (s(x), φ(x))`: logits `s` of the normalized receiver `H = face s`
(`Computation/HolonicAdjointNormalization.NormalizedExponential`) and its phase lifts `φ`. The
target `T` with its lifts `θ` is the observed Holon. Convention as in `Objects/Ratio`:
`ℓ_i = log̃ z^T_i − log̃ z^H_i`, `R_i = z^T_i / z^H_i`.

[proved-derived; formal-checked] What is proved.

1. **The full covector is the expected `R⁻¹dR`.** Along the curve, each channel's lifted log
   ratio moves by `ratioCovector_i = (E_H[ds] − ds_i)/2 − i dφ_i`
   (`hasDerivAt_logRatio_curve`, composing `log_face_mass` with the derivative of the log
   partition, `hasDerivAt_log_partition`). The channel ratio `R_i` is differentiable and
   `R_i⁻¹R_i' = ratioCovector_i` (`ratio_logDerivative_curve`, through
   `Ratio.lift_deriv_eq_logDeriv`). The lifted cross-entropy excess
   `(2/ln 2) Σ T_i ℓ_i` (`Ratio.liftedCrossEntropy_excess_eq_logRatio`) has derivative
   `(2/ln 2) Σ T_i R_i⁻¹R_i'` (`hasDerivAt_excess_curve`), whose real part is
   `(E_H[ds] − E_T[ds])/ln 2` — the logit covector `H − T` paired with `ds`
   (`excessCovector_re`) — and whose imaginary part is the **phase covector**
   `−(2/ln 2) Σ T_i dφ_i` (`excessCovector_im`). Witness: on the uniform binary pair, turning
   one produced lift at unit rate moves the phase face by `−1/ln 2` while the code-length face
   does not move (`phase_covector_witness`).
2b. **The implemented phase law (September 22 ruling).** The phase is aligned by descent on
   `½ Σ_c q_c Δ_c²`, `Δ_c = φ^T_c − φ^H_c`, `φ^H = Im s^H/2`: its gradient along `Im s^H_c` is
   `−½ q_c Δ_c` (`hasDerivAt_alignCost`), zero exactly at alignment and reversing with the gap
   (`alignCost_gradient_sign`); a common ring winding cancels from `Δ` (`phaseGap_winding`). The
   signed covector of item 1 remains a reading of the excess, not the descent law
   (`signed_reading_is_not_alignment`).
2. **The moving-weight term.** A phase mean whose weights also move (e.g. the produced Holon read
   by its own weights) has derivative `Σ dq_i φ_i + Σ q_i dφ_i`
   (`hasDerivAt_phaseMean_moving`); for `q = face s`, `dq_i = H_i (ds_i − E_H[ds])`
   (`hasDerivAt_face_mass_curve`). Unlike the fixed-weight covector, the `∂q` term reads the lift
   itself: a whole-turn shift moves it by `2π Σ dq_i k_i` (`movingWeight_term_windShift`), with a
   nonzero binary witness (`movingWeight_term_sees_the_winding`). The owner's
   `liftedCrossEntropy` weights its phase mean by the (fixed) target, so its covector is
   branch-free; a reading weighted by a moving section is not.
3. **Continuous lifts exist and are unique up to whole turns.** A continuous nonvanishing
   `R : [a,b] → ℂ` has a continuous `L` with `exp ∘ L = R` (`exists_continuous_lift`), from
   Mathlib's covering `Complex.isCoveringMapOn_exp` and unique lifting on the simply connected,
   locally path-connected interval (`IsCoveringMapOn.existsUnique_continuousMap_lifts`). Two
   continuous lifts differ by one constant `2πin` (`continuous_lift_unique`). At an interior point
   where `R` is differentiable, a continuous lift is differentiable with derivative `R⁻¹R'`
   (`continuous_lift_hasDerivAt`, by the local principal branch of `R/R(t)` and discreteness of
   `2πiℤ`); this supplies the differentiability hypothesis of `Ratio.lift_deriv_eq_logDeriv`,
   whose value it agrees with (`continuous_lift_deriv_agrees`).

[open] Lifts over higher-dimensional parameter domains (needing simple connectivity of the domain
and returning the monodromy otherwise), and a piecewise-`C¹` integral formula
`L(t) = L(a) + ∫ R'/R`, are not proved here.

No `sorry`, no `axiom`, no `native_decide`; the audit block prints the axioms.
-/

noncomputable section

namespace Soma.Holonics.Objects.RatioPhase

open Set Filter Topology
open Soma.Holonics
open Soma.Holonics.Computation.HolonicInformationTheory
open Soma.Holonics.Computation.HolonicAdjointNormalization
open Soma.Holonics.Physics.InformationDifference
open Soma.Holonics.Objects.Ratio
open NormalizedExponential

/-! ## 1. The full covector of the Holon ratio along a moving produced Holon -/

section Covector

variable {Index : Type*} [Fintype Index] [Nonempty Index]

/-- [proved-derived; formal-checked] The log partition moves by the produced expectation of the
logit velocity: `d log Z = E_H[ds]`. -/
theorem hasDerivAt_log_partition {s : ℝ → Index → ℝ} {ds : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x) :
    HasDerivAt (fun y => Real.log (partition (s y))) (expectation (face (s x)) ds) x := by
  have hZ : HasDerivAt (fun y => partition (s y)) (∑ i, Real.exp (s x i) * ds i) x := by
    unfold partition
    exact HasDerivAt.fun_sum fun i _ => (hs i).exp
  refine (hZ.log (partition_ne_zero _)).congr_deriv ?_
  simp only [expectation, face, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- [proved-derived; formal-checked] `d log H_i = ds_i − E_H[ds]` (`log_face_mass`). -/
theorem hasDerivAt_log_mass {s : ℝ → Index → ℝ} {ds : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x) (i : Index) :
    HasDerivAt (fun y => Real.log ((face (s y)).mass i))
      (ds i - expectation (face (s x)) ds) x := by
  have hfun : (fun y => Real.log ((face (s y)).mass i)) =
      fun y => s y i - Real.log (partition (s y)) := by
    funext y; exact log_face_mass _ _
  rw [hfun]
  exact (hs i).sub (hasDerivAt_log_partition hs)

/-- [definition] The channel covector `R_i⁻¹dR_i = (E_H[ds] − ds_i)/2 − i dφ_i` of the Holon
ratio `R_i = z^T_i / z^H_i` along a produced velocity `(ds, dφ)`. -/
def ratioCovector (p : PositiveProbabilitySection Index) (ds dφ : Index → ℝ) (i : Index) : ℂ :=
  (((expectation p ds - ds i) / 2 : ℝ) : ℂ) - (dφ i : ℂ) * Complex.I

/-- [proved-derived; formal-checked] Each channel's lifted log ratio moves by `ratioCovector`. -/
theorem hasDerivAt_logRatio_curve (target : PositiveProbabilitySection Index)
    (targetPhase : Index → ℝ) {s φ : ℝ → Index → ℝ} {ds dφ : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x)
    (hφ : ∀ i, HasDerivAt (fun y => φ y i) (dφ i) x) (i : Index) :
    HasDerivAt (fun y => logRatio target (face (s y)) targetPhase (φ y) i)
      (ratioCovector (face (s x)) ds dφ i) x := by
  have hre : HasDerivAt
      (fun y => Real.log (target.mass i) / 2 - Real.log ((face (s y)).mass i) / 2)
      ((expectation (face (s x)) ds - ds i) / 2) x := by
    refine ((hasDerivAt_log_mass hs i).div_const 2).const_sub _ |>.congr_deriv ?_
    ring
  have him : HasDerivAt (fun y => targetPhase i - φ y i) (-dφ i) x :=
    (hφ i).const_sub _
  have hfun : (fun y => logRatio target (face (s y)) targetPhase (φ y) i) =
      fun y => ((Real.log (target.mass i) / 2 - Real.log ((face (s y)).mass i) / 2 : ℝ) : ℂ) +
        ((targetPhase i - φ y i : ℝ) : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp [logRatio, liftedLog]
  rw [hfun]
  refine (hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I)).congr_deriv ?_
  simp [ratioCovector]
  ring

/-- [proved-derived; formal-checked] **`R⁻¹dR` of the Holon ratio in full.** The channel ratio is
differentiable along the curve and its logarithmic derivative is `ratioCovector`, through
`Ratio.lift_deriv_eq_logDeriv` (no branch of `log` is chosen). -/
theorem ratio_logDerivative_curve (target : PositiveProbabilitySection Index)
    (targetPhase : Index → ℝ) {s φ : ℝ → Index → ℝ} {ds dφ : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x)
    (hφ : ∀ i, HasDerivAt (fun y => φ y i) (dφ i) x) (i : Index) :
    ∃ R' : ℂ,
      HasDerivAt (fun y => amplitude target targetPhase i / amplitude (face (s y)) (φ y) i) R' x ∧
        (amplitude target targetPhase i / amplitude (face (s x)) (φ x) i)⁻¹ * R' =
          ratioCovector (face (s x)) ds dφ i := by
  have hL := hasDerivAt_logRatio_curve target targetPhase hs hφ i
  have hlift : ∀ y, Complex.exp (logRatio target (face (s y)) targetPhase (φ y) i) =
      amplitude target targetPhase i / amplitude (face (s y)) (φ y) i :=
    fun y => exp_logRatio _ _ _ _ _
  have hR := hL.cexp
  simp only [hlift] at hR
  exact ⟨_, hR, (lift_deriv_eq_logDeriv hlift hL hR).symm⟩

/-- [proved-derived; formal-checked] **`d(excess)` is the target expectation of `R⁻¹dR`.** The
lifted cross-entropy excess moves by `(2/ln 2) Σ T_i R_i⁻¹R_i'`, real and imaginary parts
together. -/
theorem hasDerivAt_excess_curve (target : PositiveProbabilitySection Index)
    (targetPhase : Index → ℝ) {s φ : ℝ → Index → ℝ} {ds dφ : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x)
    (hφ : ∀ i, HasDerivAt (fun y => φ y i) (dφ i) x) :
    HasDerivAt (fun y => liftedCrossEntropy target (face (s y)) (φ y) -
        liftedCrossEntropy target target targetPhase)
      (((2 / Real.log 2 : ℝ) : ℂ) *
        ∑ i, (target.mass i : ℂ) * ratioCovector (face (s x)) ds dφ i) x := by
  have hfun : (fun y => liftedCrossEntropy target (face (s y)) (φ y) -
        liftedCrossEntropy target target targetPhase) =
      fun y => ((2 / Real.log 2 : ℝ) : ℂ) *
        ∑ i, (target.mass i : ℂ) * logRatio target (face (s y)) targetPhase (φ y) i := by
    funext y
    exact (liftedCrossEntropy_excess_eq_logRatio target (face (s y)) targetPhase (φ y)).1
  rw [hfun]
  exact (HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_logRatio_curve target targetPhase hs hφ i).const_mul _).const_mul _

omit [Nonempty Index] in
/-- [proved-derived; formal-checked] The code-length face of that covector is the logit covector
`(E_H[ds] − E_T[ds])/ln 2`, i.e. `H − T` paired with `ds`. -/
theorem excessCovector_re (target p : PositiveProbabilitySection Index) (ds dφ : Index → ℝ) :
    (((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (target.mass i : ℂ) * ratioCovector p ds dφ i).re =
      (expectation p ds - expectation target ds) / Real.log 2 := by
  simp only [Complex.re_sum, ratioCovector, Complex.sub_re,
    Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, mul_one]
  have : ∑ i, target.mass i * ((expectation p ds - ds i) / 2) =
      (expectation p ds - expectation target ds) / 2 := by
    simp only [mul_div_assoc', ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, target.normalized, one_mul, expectation]
  rw [this]
  ring

omit [Nonempty Index] in
/-- [proved-derived; formal-checked] **The signed phase reading.** The phase face of the excess
moves by `−(2/ln 2) Σ T_i dφ_i`. This is a *reading* of the lifted excess, not the implemented
descent law: the September 22 ruling replaced it by the alignment descent of §2b
(`hasDerivAt_alignCost`). -/
theorem excessCovector_im (target p : PositiveProbabilitySection Index) (ds dφ : Index → ℝ) :
    (((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (target.mass i : ℂ) * ratioCovector p ds dφ i).im =
      -(2 / Real.log 2) * ∑ i, target.mass i * dφ i := by
  simp only [Complex.im_sum, ratioCovector, Complex.sub_im,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, mul_one, zero_sub, mul_neg]
  simp only [add_zero, Finset.sum_neg_distrib]
  ring

/-- [proved-derived; formal-checked] **Witness: the phase covector moves where the logit covector
does not.** Uniform binary target with zero lifts; produced logits fixed at `0`; the produced lift
of `true` turns at unit rate. The excess moves by `−i/ln 2`: real part `0`, imaginary part
`−1/ln 2 ≠ 0`. -/
theorem phase_covector_witness :
    HasDerivAt (fun y => liftedCrossEntropy halfSection (face (fun _ : Bool => (0 : ℝ)))
        (fun b => if b then y else 0) - liftedCrossEntropy halfSection halfSection (fun _ => 0))
      (((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (halfSection.mass i : ℂ) *
        ratioCovector (face (fun _ : Bool => (0 : ℝ))) (fun _ => 0)
          (fun b => if b then 1 else 0) i) 0 ∧
    (((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (halfSection.mass i : ℂ) *
        ratioCovector (face (fun _ : Bool => (0 : ℝ))) (fun _ => 0)
          (fun b => if b then 1 else 0) i).re = 0 ∧
    (((2 / Real.log 2 : ℝ) : ℂ) * ∑ i, (halfSection.mass i : ℂ) *
        ratioCovector (face (fun _ : Bool => (0 : ℝ))) (fun _ => 0)
          (fun b => if b then 1 else 0) i).im = -(1 / Real.log 2) ∧
    -(1 / Real.log 2) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : ∀ i : Bool, HasDerivAt (fun _ : ℝ => (fun _ : Bool => (0 : ℝ)) i) 0 0 :=
      fun _ => hasDerivAt_const _ _
    have hφ : ∀ i : Bool, HasDerivAt (fun y : ℝ => (fun b : Bool => if b then y else 0) i)
        ((fun b : Bool => if b then (1 : ℝ) else 0) i) 0 := by
      intro i; cases i
      · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
      · simpa using hasDerivAt_id' (0 : ℝ)
    exact hasDerivAt_excess_curve (s := fun _ _ => 0) halfSection (fun _ => 0) hs hφ
  · rw [excessCovector_re]; simp [expectation]
  · rw [excessCovector_im]; simp [halfSection]; ring
  · have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have : 0 < 1 / Real.log 2 := by positivity
    linarith

end Covector

/-! ## 2b. The implemented phase law: alignment descent -/

section Alignment

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [definition] The phase gap `Δ_c = φ^T_c − φ^H_c` with the produced phase `φ^H = Im s^H / 2`,
written in the produced imaginary logits `y = Im s^H`. -/
def phaseGap (φT y : Index → ℝ) (c : Index) : ℝ := φT c - y c / 2

/-- [definition] The alignment cost `½ Σ_c q_c Δ_c²`. -/
def alignCost (q φT y : Index → ℝ) : ℝ := (1 / 2) * ∑ c, q c * phaseGap φT y c ^ 2

/-- [proved-derived; formal-checked] **The alignment gradient.** Along `Im s^H_c` the cost moves
by `−½ q_c Δ_c`; the descent direction is `+½ q_c Δ_c`. -/
theorem hasDerivAt_alignCost (q φT y : Index → ℝ) (c : Index) :
    HasDerivAt (fun t => alignCost q φT (fun i => y i + t * (Pi.single c (1 : ℝ) : Index → ℝ) i))
      (-(1 / 2) * q c * phaseGap φT y c) 0 := by
  have hterm : ∀ i ∈ (Finset.univ : Finset Index),
      HasDerivAt (fun t => q i * phaseGap φT
          (fun j => y j + t * (Pi.single c (1 : ℝ) : Index → ℝ) j) i ^ 2)
        (q i * (2 * phaseGap φT y i * (-(Pi.single c (1 : ℝ) : Index → ℝ) i / 2))) 0 := by
    intro i _
    have hlin : HasDerivAt (fun t => phaseGap φT
        (fun j => y j + t * (Pi.single c (1 : ℝ) : Index → ℝ) j) i)
        (-(Pi.single c (1 : ℝ) : Index → ℝ) i / 2) 0 := by
      unfold phaseGap
      have := ((((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single c (1 : ℝ) : Index → ℝ) i)).const_add
        (y i)).div_const 2).const_sub (φT i)
      refine this.congr_deriv ?_
      simp; ring
    have hsq := hlin.pow 2
    refine (hsq.const_mul (q i)).congr_deriv ?_
    simp [phaseGap]
  have hsum := (HasDerivAt.fun_sum hterm).const_mul (1 / 2 : ℝ)
  refine hsum.congr_deriv ?_
  rw [Finset.sum_eq_single c]
  · simp; ring
  · intro b _ hb; simp [hb]
  · simp

omit [Fintype Index] [DecidableEq Index] in
/-- [proved-derived; formal-checked] **The descent vanishes at alignment and reverses with the
gap.** For `q_c > 0`: the gradient is zero exactly when `Δ_c = 0`, negative when the target leads
(`Δ_c > 0`) and positive when it lags. -/
theorem alignCost_gradient_sign (q φT y : Index → ℝ) (c : Index) (hq : 0 < q c) :
    (-(1 / 2) * q c * phaseGap φT y c = 0 ↔ phaseGap φT y c = 0) ∧
      (0 < phaseGap φT y c → -(1 / 2) * q c * phaseGap φT y c < 0) ∧
      (phaseGap φT y c < 0 → 0 < -(1 / 2) * q c * phaseGap φT y c) := by
  refine ⟨⟨fun h => ?_, fun h => by rw [h]; ring⟩, fun h => by nlinarith, fun h => by nlinarith⟩
  have : q c * phaseGap φT y c = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left hq.ne'

omit [Fintype Index] [DecidableEq Index] in
/-- [proved-derived; formal-checked] **The ring winding cancels.** When target and produced phases
are lifts read through the same ring at the same phase, both carry the same winding `2πn`
(`Im s^H` carries `2·2πn`), and the gap is unchanged. -/
theorem phaseGap_winding (φT y : Index → ℝ) (n : Index → ℤ) (c : Index) :
    phaseGap (fun i => φT i + 2 * Real.pi * n i) (fun i => y i + 2 * (2 * Real.pi * n i)) c =
      phaseGap φT y c := by
  unfold phaseGap; ring

omit [Fintype Index] [DecidableEq Index] in
/-- [counterexample; formal-checked] The signed reading is not the alignment law: at an aligned
channel (`Δ = 0`) the alignment gradient is `0`, while the signed reading moves the phase face by
`−(2/ln 2) T_c ≠ 0` per unit phase velocity. -/
theorem signed_reading_is_not_alignment (q φT y : Index → ℝ) (c : Index)
    (haligned : phaseGap φT y c = 0) (T : ℝ) (hT : 0 < T) :
    -(1 / 2) * q c * phaseGap φT y c = 0 ∧ -(2 / Real.log 2) * T ≠ 0 := by
  refine ⟨by rw [haligned]; ring, ?_⟩
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have : 0 < 2 / Real.log 2 * T := by positivity
  linarith

end Alignment

/-! ## 2. The moving-weight term reads the branch -/

section MovingWeight

variable {Index : Type*} [Fintype Index] [Nonempty Index]


/-- [proved-derived; formal-checked] The produced weights move by `H_i (ds_i − E_H[ds])`. -/
theorem hasDerivAt_face_mass_curve {s : ℝ → Index → ℝ} {ds : Index → ℝ} {x : ℝ}
    (hs : ∀ i, HasDerivAt (fun y => s y i) (ds i) x) (i : Index) :
    HasDerivAt (fun y => (face (s y)).mass i)
      ((face (s x)).mass i * (ds i - expectation (face (s x)) ds)) x := by
  have h := (hasDerivAt_log_mass hs i).exp
  have hfun : (fun y => Real.exp (Real.log ((face (s y)).mass i))) =
      fun y => (face (s y)).mass i := by
    funext y; exact Real.exp_log ((face _).positive i)
  rw [hfun, Real.exp_log ((face _).positive i)] at h
  exact h

omit [Nonempty Index] in
/-- [proved-derived; formal-checked] A phase mean with moving weights moves by
`Σ dq_i φ_i + Σ q_i dφ_i`. -/
theorem hasDerivAt_phaseMean_moving {q : ℝ → PositiveProbabilitySection Index}
    {φ : ℝ → Index → ℝ} {dq dφ : Index → ℝ} {x : ℝ}
    (hq : ∀ i, HasDerivAt (fun y => (q y).mass i) (dq i) x)
    (hφ : ∀ i, HasDerivAt (fun y => φ y i) (dφ i) x) :
    HasDerivAt (fun y => phaseMean (q y) (φ y))
      (∑ i, dq i * φ x i + ∑ i, (q x).mass i * dφ i) x := by
  unfold phaseMean
  refine (HasDerivAt.fun_sum fun i _ => (hq i).mul (hφ i)).congr_deriv ?_
  rw [← Finset.sum_add_distrib]

omit [Nonempty Index] in
/-- [proved-derived; formal-checked] The `∂q` term reads the lift: a whole-turn shift moves it by
`2π Σ dq_i k_i`. -/
theorem movingWeight_term_windShift (dq : Index → ℝ) (φ : Index → ℝ) (turns : Index → ℤ) :
    ∑ i, dq i * windShift φ turns i =
      ∑ i, dq i * φ i + 2 * Real.pi * ∑ i, dq i * (turns i : ℝ) := by
  simp only [windShift, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- [proved-derived; formal-checked] **Witness: the moving-weight term sees the winding.** The
uniform binary receiver moved along the `true` logit has weight velocity `(1/4, −1/4)`; one whole
turn on `true` moves the `∂q` term by `π/2 ≠ 0`, while the fixed-weight covector of §1 is
unchanged by any whole-turn shift. -/
theorem movingWeight_term_sees_the_winding :
    HasDerivAt (fun y => (face (fun b : Bool => if b then y else 0)).mass true) (1 / 4) 0 ∧
    HasDerivAt (fun y => (face (fun b : Bool => if b then y else 0)).mass false) (-(1 / 4)) 0 ∧
    2 * Real.pi * ∑ i : Bool, (if i then (1 / 4 : ℝ) else -(1 / 4)) *
        ((fun b : Bool => if b then (1 : ℤ) else 0) i : ℝ) = Real.pi / 2 ∧
    Real.pi / 2 ≠ 0 := by
  have hs : ∀ i : Bool, HasDerivAt (fun y : ℝ => (fun b : Bool => if b then y else 0) i)
      ((fun b : Bool => if b then (1 : ℝ) else 0) i) 0 := by
    intro i; cases i
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    · simpa using hasDerivAt_id' (0 : ℝ)
  have hface : face (fun b : Bool => if b then (0 : ℝ) else 0) = face (fun _ : Bool => 0) := by
    congr 1; funext b; cases b <;> rfl
  have hE : expectation (face (fun _ : Bool => (0 : ℝ))) (fun b => if b then 1 else 0) = 1 / 2 := by
    simp [expectation, face_zero_bool]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (hasDerivAt_face_mass_curve (s := fun y b => if b then y else 0) hs true).congr_deriv ?_
    simp only [hface, hE, face_zero_bool]; norm_num
  · refine (hasDerivAt_face_mass_curve (s := fun y b => if b then y else 0) hs false).congr_deriv ?_
    simp only [hface, hE, face_zero_bool]; norm_num
  · simp; ring
  · exact div_ne_zero Real.pi_ne_zero two_ne_zero

end MovingWeight

/-! ## 3. Continuous lifts of a nonvanishing ratio -/

section ContinuousLift

/-- [proved-derived; formal-checked] **Continuous lifts exist.** -/
theorem exists_continuous_lift {R : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hR : ContinuousOn R (Icc a b)) (hne : ∀ t ∈ Icc a b, R t ≠ 0) :
    ∃ L : ℝ → ℂ, ContinuousOn L (Icc a b) ∧ ∀ t ∈ Icc a b, Complex.exp (L t) = R t := by
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.mpr hab⟩⟩
  have := (convex_Icc a b).contractibleSpace (nonempty_Icc.mpr hab)
  have := (convex_Icc a b).locallyPathConnectedSpace
  let f : C(Icc a b, ℂ) := ⟨fun t => R t, hR.domRestrict⟩
  let a₀ : Icc a b := ⟨a, left_mem_Icc.mpr hab⟩
  have he : Complex.exp (Complex.log (R a)) = f a₀ := Complex.exp_log (hne a a₀.2)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he
    (fun t => hne t t.2)
  refine ⟨fun t => F (projIcc a b hab t), ?_, ?_⟩
  · exact (F.continuous.comp continuous_projIcc).continuousOn
  · intro t ht
    have := congrFun hF (projIcc a b hab t)
    simp only [Function.comp_apply] at this
    rw [this]
    change R (projIcc a b hab t : ℝ) = R t
    rw [projIcc_of_mem hab ht]


/-- [proved-derived; formal-checked] **Two continuous lifts differ by one whole-turn constant.** -/
theorem continuous_lift_unique {R L L' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hL : ContinuousOn L (Icc a b)) (hL' : ContinuousOn L' (Icc a b))
    (hlift : ∀ t ∈ Icc a b, Complex.exp (L t) = R t)
    (hlift' : ∀ t ∈ Icc a b, Complex.exp (L' t) = R t) (hne : ∀ t ∈ Icc a b, R t ≠ 0) :
    ∃ n : ℤ, ∀ t ∈ Icc a b, L' t = L t + n * (2 * Real.pi * Complex.I) := by
  have : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.mpr hab⟩⟩
  have := (convex_Icc a b).contractibleSpace (nonempty_Icc.mpr hab)
  have := (convex_Icc a b).locallyPathConnectedSpace
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  obtain ⟨n, hn⟩ : ∃ n : ℤ, L' a = L a + n * (2 * Real.pi * Complex.I) :=
    Complex.exp_eq_exp_iff_exists_int.mp ((hlift' a ha).trans (hlift a ha).symm)
  refine ⟨n, ?_⟩
  let f : C(Icc a b, ℂ) := ⟨fun t => R t, by
    have hR : ContinuousOn R (Icc a b) := by
      refine (Complex.continuous_exp.comp_continuousOn hL).congr ?_
      intro t ht; exact (hlift t ht).symm
    exact hR.domRestrict⟩
  let a₀ : Icc a b := ⟨a, ha⟩
  let G : C(Icc a b, ℂ) := ⟨fun t => L' t, hL'.domRestrict⟩
  let H : C(Icc a b, ℂ) := ⟨fun t => L t + n * (2 * Real.pi * Complex.I), by
    exact (hL.domRestrict).add continuous_const⟩
  have hG : Complex.exp ∘ G = f := by funext t; exact hlift' t t.2
  have hH : Complex.exp ∘ H = f := by
    funext t
    change Complex.exp (L t + n * (2 * Real.pi * Complex.I)) = R t
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact hlift t t.2
  have he : Complex.exp (G a₀) = f a₀ := congrFun hG a₀
  obtain ⟨F, -, huniq⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he
    (fun t => hne t t.2)
  have hGF : G = F := huniq G ⟨rfl, hG⟩
  have hHF : H = F := huniq H ⟨by change L a + _ = L' a; rw [hn], hH⟩
  intro t ht
  have := congrArg (fun F : C(Icc a b, ℂ) => F ⟨t, ht⟩) (hGF.trans hHF.symm)
  exact this

/-- [proved-derived; formal-checked] **A continuous lift is differentiable where `R` is, with
derivative `R⁻¹R'`** (interior points). -/
theorem continuous_lift_hasDerivAt {R L : ℝ → ℂ} {a b t : ℝ} {R' : ℂ}
    (hL : ContinuousOn L (Icc a b)) (hlift : ∀ s ∈ Icc a b, Complex.exp (L s) = R s)
    (ht : t ∈ Ioo a b) (hR : HasDerivAt R R' t) :
    HasDerivAt L ((R t)⁻¹ * R') t := by
  have hIcc : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hLt : ContinuousAt L t := hL.continuousAt hIcc
  have hRt : R t ≠ 0 := by
    rw [← hlift t (Ioo_subset_Icc_self ht)]; exact Complex.exp_ne_zero _
  set w : ℝ → ℂ := fun s => R s / R t
  have hw : HasDerivAt w (R' / R t) t := hR.div_const _
  have hw1 : w t = 1 := div_self hRt
  have hslit : w t ∈ Complex.slitPlane := by rw [hw1]; exact Complex.one_mem_slitPlane
  have hlog : HasDerivAt (fun s => Complex.log (w s)) (R' / R t / w t) t := hw.clog_real hslit
  -- the difference g = L - L t - log w takes values in 2πiℤ and is continuous at t
  set g : ℝ → ℂ := fun s => L s - L t - Complex.log (w s)
  have hg : ContinuousAt g t :=
    (hLt.sub continuousAt_const).sub (hlog.continuousAt)
  have hgt : g t = 0 := by simp [g, hw1]
  have hgint : ∀ s ∈ Icc a b, ∃ n : ℤ, g s = n * (2 * Real.pi * Complex.I) := by
    intro s hs
    have hws : w s ≠ 0 := by
      simp only [w]
      rw [← hlift s hs]
      exact div_ne_zero (Complex.exp_ne_zero _) hRt
    have hRs : R s ≠ 0 := by rw [← hlift s hs]; exact Complex.exp_ne_zero _
    have : Complex.exp (g s) = 1 := by
      simp only [g, Complex.exp_sub, Complex.exp_log hws, w, hlift s hs,
        hlift t (Ioo_subset_Icc_self ht)]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp this
    exact ⟨n, by rw [hn]⟩
  have hsmall : ∀ᶠ s in 𝓝 t, ‖g s‖ < 2 * Real.pi := by
    have h2 : Tendsto (fun s => ‖g s‖) (𝓝 t) (𝓝 0) := by
      have := hg.norm
      rw [ContinuousAt, hgt, norm_zero] at this
      exact this
    exact h2.eventually (gt_mem_nhds (by positivity))
  have hzero : ∀ᶠ s in 𝓝 t, g s = 0 := by
    filter_upwards [hsmall, hIcc] with s hs hsI
    obtain ⟨n, hn⟩ := hgint s hsI
    rw [hn] at hs ⊢
    have hn0 : n = 0 := by
      by_contra hne
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hne
        exact_mod_cast this
      have hnorm : ‖(n : ℂ) * (2 * Real.pi * Complex.I)‖ = |(n : ℝ)| * (2 * Real.pi) := by
        rw [norm_mul, Complex.norm_intCast, norm_mul, norm_mul, Complex.norm_I, Complex.norm_two,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        ring
      rw [hnorm] at hs
      nlinarith [Real.pi_pos]
    simp [hn0]
  have heq : (fun s => L t + Complex.log (w s)) =ᶠ[𝓝 t] L := by
    filter_upwards [hzero] with s hs
    simp only [g] at hs
    linear_combination -hs
  have hd : HasDerivAt (fun s => L t + Complex.log (w s)) ((R t)⁻¹ * R') t := by
    refine (hlog.const_add (L t)).congr_deriv ?_
    rw [hw1, div_one, div_eq_inv_mul]
  exact hd.congr_of_eventuallyEq heq.symm

/-- [proved-derived; formal-checked] **The continuous lift meets the owner's first order.** For
a global lift `exp ∘ L = R` that is continuous at an interior point where `R` is differentiable,
`L` is differentiable there, and the derivative that `Ratio.lift_deriv_eq_logDeriv` names
(`R⁻¹R'`) is the one it has. -/
theorem continuous_lift_deriv_agrees {R L : ℝ → ℂ} {t : ℝ} {R' : ℂ}
    (hlift : ∀ s, Complex.exp (L s) = R s) (hL : Continuous L) (hR : HasDerivAt R R' t) :
    ∃ ℓ', HasDerivAt L ℓ' t ∧ ℓ' = (R t)⁻¹ * R' := by
  have hd := continuous_lift_hasDerivAt (a := t - 1) (b := t + 1) hL.continuousOn
    (fun s _ => hlift s) ⟨by linarith, by linarith⟩ hR
  exact ⟨_, hd, lift_deriv_eq_logDeriv hlift hd hR⟩

/-- [proved-derived; formal-checked] Witness: the unit circle `t ↦ e^{it}` on `[0, 2π]` has the
continuous lift `t ↦ it`, and every continuous lift is `it + 2πin`; its end-to-end change is the
winding `2πi`, which the principal logarithm (equal at both ends) cannot return. -/
theorem circle_lift_winding :
    (∀ L : ℝ → ℂ, ContinuousOn L (Icc 0 (2 * Real.pi)) →
        (∀ t ∈ Icc 0 (2 * Real.pi), Complex.exp (L t) = Complex.exp (t * Complex.I)) →
        L (2 * Real.pi) - L 0 = 2 * Real.pi * Complex.I) ∧
      Complex.log (Complex.exp ((2 * Real.pi : ℝ) * Complex.I)) =
        Complex.log (Complex.exp ((0 : ℝ) * Complex.I)) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  refine ⟨fun L hL hlift => ?_, ?_⟩
  · have hid : ContinuousOn (fun t : ℝ => (t : ℂ) * Complex.I) (Icc 0 (2 * Real.pi)) :=
      (Complex.continuous_ofReal.mul continuous_const).continuousOn
    obtain ⟨n, hn⟩ := continuous_lift_unique hpi hid hL (fun _ _ => rfl) hlift
      (fun _ _ => Complex.exp_ne_zero _)
    rw [hn _ (right_mem_Icc.mpr hpi), hn _ (left_mem_Icc.mpr hpi)]
    push_cast
    ring
  · have h2 : Complex.exp ((2 * Real.pi : ℝ) * Complex.I) = 1 := by
      push_cast; exact Complex.exp_two_pi_mul_I
    rw [h2]; simp

end ContinuousLift

section Audit

#print axioms hasDerivAt_log_partition
#print axioms hasDerivAt_logRatio_curve
#print axioms ratio_logDerivative_curve
#print axioms hasDerivAt_excess_curve
#print axioms excessCovector_re
#print axioms excessCovector_im
#print axioms phase_covector_witness
#print axioms hasDerivAt_alignCost
#print axioms alignCost_gradient_sign
#print axioms phaseGap_winding
#print axioms signed_reading_is_not_alignment
#print axioms hasDerivAt_face_mass_curve
#print axioms hasDerivAt_phaseMean_moving
#print axioms movingWeight_term_windShift
#print axioms movingWeight_term_sees_the_winding
#print axioms exists_continuous_lift
#print axioms continuous_lift_unique
#print axioms continuous_lift_hasDerivAt
#print axioms continuous_lift_deriv_agrees
#print axioms circle_lift_winding

end Audit

end Soma.Holonics.Objects.RatioPhase

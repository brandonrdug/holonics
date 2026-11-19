import Holonics.Objects.Ratio
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The phase part of the loss covector, with both participants moving

Source: #410's box "The phase part of the loss covector, beside the proved real covector", and CLAUDE.md's loss law:
the loss is `ℓ = log R` of the Holon ratio `R = ψ_T/ψ_H`, `log(ψ_T/ψ_H) = ½ log(q/p) + i(φ_T − φ_H + 2πn)`, and its
calculus is the logarithmic derivative `R⁻¹ dR`, the learning covector. `Objects/Ratio` and `Objects/RatioPhase`
already prove this covector in the logit chart of the produced receiver, with the target held fixed
(`RatioPhase.ratio_logDerivative_curve`, `excessCovector_re`, `excessCovector_im`; atlas `ratio.full-covector`,
`ratio.excess-covector-faces`). This file reads one channel's covector in the amplitude chart with **both**
participants moving along one clock, as the cross-entropy law asks (`d/dλ H(p, q) = −Σ ṗ log q − Σ p q̇/q`: both
move).

[proved-derived; formal-checked] What is proved. For one channel, the produced amplitude `ψ_H = √p e^{iφ}` and the
target amplitude `ψ_T = √q e^{iθ}` (`amp`, which is `Objects/Ratio.amplitude` at one index, `amplitude_eq_amp`):

1. **The log of the ratio splits** (§1). Every lift `ℓ_n = ½(log q − log p) + i(θ − φ + 2πn)` (`lift`) exponentiates
   to `R = ψ_T/ψ_H` (`exp_lift`); its real part is `½ log(q/p)` (`lift_re`) and its imaginary part `θ − φ + 2πn`
   (`lift_im`); the principal logarithm of `R` is one of them (`log_ratio_mem_lifts`), and the lifts differ by whole
   turns only (`lift_sub`). `Objects/Ratio.logRatio` is the lift with `n = 0` (`logRatio_eq_lift`).
2. **The covector along a clock** (§2). Along differentiable paths `p, q > 0`, `φ, θ`, every lift moves by the one
   covector `½(q̇/q − ṗ/p) + i(θ̇ − φ̇)` (`hasDerivAt_lift`, `lossCovector`): its real part is the code-length face,
   the rate of `½ log(q/p)` (`lossCovector_re`), and its imaginary part the **phase face**, the rate of the phase gap
   (`lossCovector_im`). The ratio moves by `R · covector` (`hasDerivAt_ratio`), so any derivative `R'` of the ratio
   has `R⁻¹ R' = covector` (`logDeriv_ratio`, through `Objects/Ratio.lift_deriv_eq_logDeriv`). The winding branch
   `2πn` is absent from the covector: every lift has the same derivative.
3. **A common turn is invisible** (§3). Turning both phases by one `α` leaves the ratio (`ratio_common_turn`), every
   lift (`lift_common_turn`) and the covector unchanged (`lossCovector_common_turn`): only the relative phase is read.
   A turn of the produced phase alone moves the phase face by `−α̇` and leaves the code-length face
   (`lossCovector_produced_turn`).

Limits. One channel; the sum over a receiver's channels weighted by the target is `Objects/RatioPhase`'s
`hasDerivAt_excess_curve` in the logit chart, and its moving-weight term (`hasDerivAt_phaseMean_moving`) is not
restated here. The paths are differentiable at the reading point and positive everywhere (the positivity makes the
ratio one exponential of the lift at every time); lifts that are only continuous are `Objects/RatioPhase`'s
`exists_continuous_lift`. Nothing here is a descent law for the phase: the implemented law is
`RatioPhase.alignCost`, and this covector is a reading of the loss.

The computational object is the helical pair interaction: the produced and the target Holon are a pair compared by
their ratio, and the covector is the rate of that comparison on its receiving face. Of the winding guide's six
general objects this touches the pair (the ratio of the two amplitudes and its relative phase) and faces and
placement (the code-length face and the phase face of the covector); the helix (the winding `2πn`, which the
covector does not see), cell holonomy, the tube and the tower thread stay attached.

Consumers: #410's box on the phase part of the loss covector; CLAUDE.md's loss law; `Objects/Ratio.logRatio`,
`Objects/Ratio.lift_deriv_eq_logDeriv`; atlas `ratio.full-covector`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LossPhase

open Complex

/-! ## 1. The log of the ratio splits -/

/-- [definition] **One channel's amplitude** `√p e^{iφ}`. -/
def amp (p φ : ℝ) : ℂ := (Real.sqrt p : ℂ) * Complex.exp (φ * Complex.I)

/-- [definition] **The Holon ratio** `R = ψ_T/ψ_H` of the target `(q, θ)` over the produced `(p, φ)`. -/
def ratio (p q φ θ : ℝ) : ℂ := amp q θ / amp p φ

/-- [definition] **The lift on winding branch `n`**: `½(log q − log p) + i(θ − φ + 2πn)`. -/
def lift (p q φ θ : ℝ) (n : ℤ) : ℂ :=
  (((Real.log q - Real.log p) / 2 : ℝ) : ℂ) + ((θ - φ + 2 * Real.pi * n : ℝ) : ℂ) * Complex.I

/-- [proved-derived; formal-checked] `Objects/Ratio.amplitude` is this amplitude at one index. -/
theorem amplitude_eq_amp {Index : Type*} [Fintype Index]
    (q : Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection Index)
    (phase : Index → ℝ) (i : Index) :
    Holonics.Objects.Ratio.amplitude q phase i = amp (q.mass i) (phase i) := rfl

/-- [proved-derived; formal-checked] `Objects/Ratio.logRatio` is the lift on the branch `n = 0`. -/
theorem logRatio_eq_lift {Index : Type*} [Fintype Index]
    (target produced : Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection Index)
    (targetPhase producedPhase : Index → ℝ) (i : Index) :
    Holonics.Objects.Ratio.logRatio target produced targetPhase producedPhase i =
      lift (produced.mass i) (target.mass i) (producedPhase i) (targetPhase i) 0 := by
  apply Complex.ext
  · simp [Holonics.Objects.Ratio.logRatio, Holonics.Objects.Ratio.liftedLog, lift]; ring
  · simp [Holonics.Objects.Ratio.logRatio, Holonics.Objects.Ratio.liftedLog, lift]

theorem exp_halfLog (p φ : ℝ) (hp : 0 < p) :
    Complex.exp ((((Real.log p / 2) : ℝ) : ℂ) + (φ : ℂ) * Complex.I) = amp p φ := by
  rw [Complex.exp_add, ← Complex.ofReal_exp, amp]
  congr 2
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  ring_nf

/-- [proved-derived; formal-checked] **Every lift is a logarithm of the ratio**: `exp ℓ_n = ψ_T/ψ_H`. -/
theorem exp_lift {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (φ θ : ℝ) (n : ℤ) :
    Complex.exp (lift p q φ θ n) = ratio p q φ θ := by
  have hsplit : lift p q φ θ n =
      ((((Real.log q / 2) : ℝ) : ℂ) + (θ : ℂ) * Complex.I) -
        ((((Real.log p / 2) : ℝ) : ℂ) + (φ : ℂ) * Complex.I) + n * (2 * Real.pi * Complex.I) := by
    rw [lift]; push_cast; ring
  rw [hsplit, Complex.exp_add, Complex.exp_sub, exp_halfLog q θ hq, exp_halfLog p φ hp,
    Complex.exp_int_mul_two_pi_mul_I, mul_one, ratio]

/-- [proved-derived; formal-checked] The real part of every lift is `½ log(q/p)`. -/
theorem lift_re {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (φ θ : ℝ) (n : ℤ) :
    (lift p q φ θ n).re = Real.log (q / p) / 2 := by
  rw [Real.log_div hq.ne' hp.ne']
  simp [lift]

/-- [proved-derived; formal-checked] The imaginary part of the lift on branch `n` is `θ − φ + 2πn`. -/
theorem lift_im (p q φ θ : ℝ) (n : ℤ) : (lift p q φ θ n).im = θ - φ + 2 * Real.pi * n := by
  simp [lift]

/-- [proved-derived; formal-checked] Two lifts differ by whole turns: `ℓ_n − ℓ_m = 2πi(n − m)`. -/
theorem lift_sub (p q φ θ : ℝ) (n m : ℤ) :
    lift p q φ θ n - lift p q φ θ m = ((n - m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
  rw [lift, lift]; push_cast; ring

/-- [proved-derived; formal-checked] **The principal logarithm of the ratio is one of the lifts.** -/
theorem log_ratio_mem_lifts {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (φ θ : ℝ) :
    ∃ n : ℤ, Complex.log (ratio p q φ θ) = lift p q φ θ n := by
  have hR : ratio p q φ θ ≠ 0 := by
    rw [← exp_lift hp hq φ θ 0]; exact Complex.exp_ne_zero _
  have h : Complex.exp (Complex.log (ratio p q φ θ)) = Complex.exp (lift p q φ θ 0) := by
    rw [Complex.exp_log hR, exp_lift hp hq φ θ 0]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  rw [hn, lift, lift]
  push_cast
  ring

/-! ## 2. The covector along a clock -/

/-- [definition] **The loss covector** of one channel, `½(q̇/q − ṗ/p) + i(θ̇ − φ̇)`. -/
def lossCovector (p q p' q' φ' θ' : ℝ) : ℂ :=
  ((((q' / q - p' / p) / 2) : ℝ) : ℂ) + ((θ' - φ' : ℝ) : ℂ) * Complex.I

/-- [proved-derived; formal-checked] Its real part, the code-length face, is the rate of `½ log(q/p)`. -/
theorem lossCovector_re (p q p' q' φ' θ' : ℝ) :
    (lossCovector p q p' q' φ' θ').re = (q' / q - p' / p) / 2 := by
  simp [lossCovector]

/-- [proved-derived; formal-checked] Its imaginary part, **the phase face**, is the rate of the phase gap. -/
theorem lossCovector_im (p q p' q' φ' θ' : ℝ) : (lossCovector p q p' q' φ' θ').im = θ' - φ' := by
  simp [lossCovector]

variable {p q φ θ : ℝ → ℝ} {p' q' φ' θ' t : ℝ}

/-- [proved-derived; formal-checked] **Every lift moves by the one covector**; the branch `n` does not enter. -/
theorem hasDerivAt_lift (hp : 0 < p t) (hq : 0 < q t) (dp : HasDerivAt p p' t)
    (dq : HasDerivAt q q' t) (dφ : HasDerivAt φ φ' t) (dθ : HasDerivAt θ θ' t) (n : ℤ) :
    HasDerivAt (fun s => lift (p s) (q s) (φ s) (θ s) n) (lossCovector (p t) (q t) p' q' φ' θ') t := by
  have hre : HasDerivAt (fun s => (Real.log (q s) - Real.log (p s)) / 2)
      ((q' / q t - p' / p t) / 2) t :=
    ((dq.log hq.ne').sub (dp.log hp.ne')).div_const 2
  have him : HasDerivAt (fun s => θ s - φ s + 2 * Real.pi * n) (θ' - φ') t :=
    (dθ.sub dφ).add_const _
  exact hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I)

/-- [proved-derived; formal-checked] **The ratio moves by `R · covector`** along positive paths. -/
theorem hasDerivAt_ratio (hp : ∀ s, 0 < p s) (hq : ∀ s, 0 < q s) (dp : HasDerivAt p p' t)
    (dq : HasDerivAt q q' t) (dφ : HasDerivAt φ φ' t) (dθ : HasDerivAt θ θ' t) :
    HasDerivAt (fun s => ratio (p s) (q s) (φ s) (θ s))
      (ratio (p t) (q t) (φ t) (θ t) * lossCovector (p t) (q t) p' q' φ' θ') t := by
  have hfun : (fun s => ratio (p s) (q s) (φ s) (θ s)) =
      fun s => Complex.exp (lift (p s) (q s) (φ s) (θ s) 0) := by
    funext s; exact (exp_lift (hp s) (hq s) _ _ 0).symm
  rw [hfun, ← exp_lift (hp t) (hq t) _ _ 0]
  exact (hasDerivAt_lift (hp t) (hq t) dp dq dφ dθ 0).cexp

/-- [proved-derived; formal-checked] **`R⁻¹ dR` is the loss covector**: any derivative of the ratio, divided by the
ratio, is `½(q̇/q − ṗ/p) + i(θ̇ − φ̇)`. -/
theorem logDeriv_ratio (hp : ∀ s, 0 < p s) (hq : ∀ s, 0 < q s) (dp : HasDerivAt p p' t)
    (dq : HasDerivAt q q' t) (dφ : HasDerivAt φ φ' t) (dθ : HasDerivAt θ θ' t) {R' : ℂ}
    (dR : HasDerivAt (fun s => ratio (p s) (q s) (φ s) (θ s)) R' t) :
    (ratio (p t) (q t) (φ t) (θ t))⁻¹ * R' = lossCovector (p t) (q t) p' q' φ' θ' :=
  (Holonics.Objects.Ratio.lift_deriv_eq_logDeriv (L := fun s => lift (p s) (q s) (φ s) (θ s) 0)
    (fun s => exp_lift (hp s) (hq s) _ _ 0) (hasDerivAt_lift (hp t) (hq t) dp dq dφ dθ 0) dR).symm

/-! ## 3. A common turn is invisible -/

theorem amp_turn (p φ α : ℝ) : amp p (φ + α) = amp p φ * Complex.exp (α * Complex.I) := by
  rw [amp, amp]; push_cast; rw [add_mul, Complex.exp_add]; ring

/-- [proved-derived; formal-checked] **Turning both phases by one `α` leaves the ratio.** -/
theorem ratio_common_turn (p q φ θ α : ℝ) : ratio p q (φ + α) (θ + α) = ratio p q φ θ := by
  rw [ratio, ratio, amp_turn, amp_turn]
  exact mul_div_mul_right _ _ (Complex.exp_ne_zero _)

/-- [proved-derived; formal-checked] Turning both phases by one `α` leaves every lift. -/
theorem lift_common_turn (p q φ θ α : ℝ) (n : ℤ) : lift p q (φ + α) (θ + α) n = lift p q φ θ n := by
  rw [lift, lift]; push_cast; ring

/-- [proved-derived; formal-checked] Turning both phases at one rate `α̇` leaves the covector. -/
theorem lossCovector_common_turn (p q p' q' φ' θ' α' : ℝ) :
    lossCovector p q p' q' (φ' + α') (θ' + α') = lossCovector p q p' q' φ' θ' := by
  rw [lossCovector, lossCovector]; push_cast; ring

/-- [proved-derived; formal-checked] Turning the produced phase alone at rate `α̇` moves the phase face by `−α̇` and
leaves the code-length face. -/
theorem lossCovector_produced_turn (p q p' q' φ' θ' α' : ℝ) :
    lossCovector p q p' q' (φ' + α') θ' = lossCovector p q p' q' φ' θ' - (α' : ℂ) * Complex.I := by
  rw [lossCovector, lossCovector]; push_cast; ring

end Holonics.HNN.LossPhase

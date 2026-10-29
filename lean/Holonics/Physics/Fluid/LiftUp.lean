import Holonics.Geometry.Motion

/-!
# Lift-up: every mode of a shear decays while its energy grows

[proved-standard] Linearize the incompressible Navier–Stokes equations about the uniform shear
`U = (S y, 0, 0)` and keep a disturbance that is constant along the stream (`∂ₓ = 0`), one Fourier
mode `e^(i(k_y y + k_z z))` with `k² = k_y² + k_z² ≠ 0`. Then `U·∇` vanishes, the pressure
equation reads `∇²p = −2S ∂ₓv = 0`, so `p = 0`, and the streamwise and wall-normal velocities obey
```text
u̇ = −d u − S v,        v̇ = −d v,        d = ν k²
```
exactly: the wall-normal velocity lifts slow fluid up into the fast stream (lift-up; Ellingsen and
Palm 1975, Landahl 1980). This is the mode-level face of the Navier–Stokes target's transient
amplification (plane Couette flow is linearly stable at every Reynolds number, Romanov 1973, and
turbulent in experiment; Trefethen, Trefethen, Reddy and Driscoll 1993).

[proved-derived; formal-checked] The consumer of `Geometry/Motion.numerical_abscissa` (record
`2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS`, J6):

* **Every mode decays.** The rate `liftUp S d = [[−d, −S], [0, −d]]` has the single eigenvalue
  `−d` (`liftUp_eigenvalue`).
* **The boost does not.** Against the unit metric (kinetic energy), the boost is
  `[[−d, −S/2], [−S/2, −d]]` (`liftUp_boost`), whose largest reading is `|S|/2 − d`
  (`liftUp_reading_le`, `liftUp_readings_iff`). So `e^(t(|S|/2 − d))` bounds the response, and no
  smaller exponent does (`liftUp_energy_bound_iff`): the response is read on the boost, not on the
  spectrum. For `|S| > 2d` the bound allows growth although every mode decays.
* **The response.** For `t ≥ 0`, `e^(tA)(u₀, v₀) = e^(−dt)(u₀ − S t v₀, v₀)` (`liftUp_exp`): a
  free-fall shear `[[1, −St], [0, 1]]` riding a uniform decay. Forward uniqueness comes from the
  energy bound itself: the difference of two motions starts at zero energy and its energy is
  bounded by `e^(2λt)·0`. The energy is `e^(−2dt)((u₀ − S t v₀)² + v₀²)` (`liftUp_energy`), with
  the algebraic growth `S²t²` against the exponential decay.
* **Transient amplification** (`liftUp_transient`). At `S = 1`, `d = 1/10`, every eigenvalue is
  negative, yet from `(0, 1)` the energy at `t = 2` is `5e^(−2/5) > 1`.

The reals here are the mathematics of the continuum mode; the machine's own carriers stay exact.
-/

namespace Holonics.Physics.Fluid.LiftUp

open Matrix Holonics.Geometry.Motion

/-- [definition] **The lift-up rate** of a streamwise-constant Fourier mode of the uniform shear
`U = S y`, with viscous decay `d = ν k²`, on the state `(u, v)` (streamwise, wall-normal). -/
def liftUp (S d : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![-d, -S; 0, -d]

/-- [proved-standard; formal-checked] **Every mode decays at the viscous rate:** the only
eigenvalue of the lift-up rate is `−d`. -/
theorem liftUp_eigenvalue {S d μ : ℝ} {w : Fin 2 → ℝ} (hw : w ≠ 0)
    (h : liftUp S d *ᵥ w = μ • w) : μ = -d := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [liftUp, mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  by_cases hw1 : w 1 = 0
  · have hw0 : w 0 ≠ 0 := by
      intro hw0
      exact hw (funext fun i => by fin_cases i <;> simp [hw0, hw1])
    rw [hw1] at h0
    have : (μ + d) * w 0 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hw0
  · have : (μ + d) * w 1 = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · exact absurd h hw1

/-- [proved-derived; formal-checked] **The lift-up's boost** against the unit metric. -/
theorem liftUp_boost (S d : ℝ) : boost 1 (liftUp S d) = !![-d, -(S / 2); -(S / 2), -d] := by
  rw [boost, adjointIn_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [liftUp] <;> ring

/-- [proved-derived; formal-checked] The energy-rate reading of the lift-up,
`⟨y, (A + Aᵀ) y⟩ = −2d(y₀² + y₁²) − 2S y₀ y₁`. -/
theorem liftUp_reading (S d : ℝ) (y : Fin 2 → ℝ) :
    y ⬝ᵥ ((1 * liftUp S d + (liftUp S d)ᵀ * 1) *ᵥ y) =
      -2 * d * (y 0 ^ 2 + y 1 ^ 2) - 2 * S * (y 0 * y 1) := by
  simp [liftUp, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] **The boost's largest reading is at most `|S|/2 − d`.** -/
theorem liftUp_reading_le (S d : ℝ) (y : Fin 2 → ℝ) :
    y ⬝ᵥ ((1 * liftUp S d + (liftUp S d)ᵀ * 1) *ᵥ y) ≤
      2 * (|S| / 2 - d) * (y ⬝ᵥ (1 *ᵥ y)) := by
  rw [liftUp_reading]
  simp only [one_mulVec, dotProduct, Fin.sum_univ_two]
  rcases abs_cases S with ⟨hS, _⟩ | ⟨hS, _⟩ <;> rw [hS] <;>
    nlinarith [sq_nonneg (y 0 + y 1), sq_nonneg (y 0 - y 1)]

/-- [proved-derived; formal-checked] **The numerical abscissa of lift-up is exactly
`|S|/2 − d`:** every reading of the energy rate is at most `2λ` times the energy exactly when
`|S|/2 − d ≤ λ`. -/
theorem liftUp_readings_iff (S d lam : ℝ) :
    (∀ y : Fin 2 → ℝ, y ⬝ᵥ ((1 * liftUp S d + (liftUp S d)ᵀ * 1) *ᵥ y) ≤
      2 * lam * (y ⬝ᵥ (1 *ᵥ y))) ↔ |S| / 2 - d ≤ lam := by
  constructor
  · intro h
    rcases le_or_gt 0 S with hS | hS
    · have := h ![1, -1]
      rw [liftUp_reading] at this
      simp [dotProduct, Fin.sum_univ_two] at this
      rw [abs_of_nonneg hS]
      linarith
    · have := h ![1, 1]
      rw [liftUp_reading] at this
      simp [dotProduct, Fin.sum_univ_two] at this
      rw [abs_of_neg hS]
      linarith
  · intro hlam y
    have hq : 0 ≤ y ⬝ᵥ (1 *ᵥ y) := by
      simp only [one_mulVec, dotProduct, Fin.sum_univ_two]
      nlinarith [mul_self_nonneg (y 0), mul_self_nonneg (y 1)]
    have := liftUp_reading_le S d y
    nlinarith

/-- [proved-derived; formal-checked] **The response of the lift-up is bounded by its boost, and
by nothing smaller** (`numerical_abscissa` at the unit metric): the kinetic energy of every motion
`e^(tA) y` stays below `e^(2λt)` times its start for all `t ≥ 0` exactly when
`|S|/2 − d ≤ λ`. -/
theorem liftUp_energy_bound_iff (S d lam : ℝ) :
    (∀ y : Fin 2 → ℝ, ∀ t, 0 ≤ t →
      (NormedSpace.exp (t • liftUp S d) *ᵥ y) ⬝ᵥ (NormedSpace.exp (t • liftUp S d) *ᵥ y) ≤
        Real.exp (2 * lam * t) * (y ⬝ᵥ y)) ↔ |S| / 2 - d ≤ lam := by
  rw [← liftUp_readings_iff, abscissa_iff]
  simp only [one_mulVec]

/-- The explicit lift-up motion: a shear riding a uniform decay. -/
private theorem liftUp_motion (S d u₀ v₀ t : ℝ) :
    HasDerivAt (fun s => Real.exp (-d * s) • ![u₀ - S * s * v₀, v₀])
      (liftUp S d *ᵥ (Real.exp (-d * t) • ![u₀ - S * t * v₀, v₀])) t := by
  have he : HasDerivAt (fun s => Real.exp (-d * s)) (Real.exp (-d * t) * (-d)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-d)).exp
  refine hasDerivAt_pi.2 fun i => ?_
  fin_cases i
  · have hl : HasDerivAt (fun s => u₀ - S * s * v₀) (-(S * v₀)) t := by
      simpa using ((hasDerivAt_id t).const_mul S).mul_const v₀ |>.const_sub u₀
    have h : HasDerivAt (fun s => (Real.exp (-d * s) • ![u₀ - S * s * v₀, v₀]) 0)
        (Real.exp (-d * t) * -d * (u₀ - S * t * v₀) + Real.exp (-d * t) * -(S * v₀)) t :=
      he.mul hl
    refine h.congr_deriv ?_
    simp [liftUp, mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · have h : HasDerivAt (fun s => (Real.exp (-d * s) • ![u₀ - S * s * v₀, v₀]) 1)
        (Real.exp (-d * t) * -d * v₀) t :=
      he.mul_const v₀
    refine h.congr_deriv ?_
    simp [liftUp, mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- [proved-derived; formal-checked] **The lift-up response is a shear riding a uniform decay:**
for `t ≥ 0`, `e^(tA)(u₀, v₀) = e^(−dt)(u₀ − S t v₀, v₀)`. Forward uniqueness is the energy bound
itself: the difference of the two motions starts at zero energy. -/
theorem liftUp_exp (S d u₀ v₀ t : ℝ) (ht : 0 ≤ t) :
    NormedSpace.exp (t • liftUp S d) *ᵥ ![u₀, v₀] =
      Real.exp (-d * t) • ![u₀ - S * t * v₀, v₀] := by
  set z : ℝ → Fin 2 → ℝ := fun s => NormedSpace.exp (s • liftUp S d) *ᵥ ![u₀, v₀] -
    Real.exp (-d * s) • ![u₀ - S * s * v₀, v₀] with hz
  have hzd : ∀ s, HasDerivAt z (liftUp S d *ᵥ z s) s := fun s => by
    have := (hasDerivAt_exp_mulVec (liftUp S d) ![u₀, v₀] s).sub (liftUp_motion S d u₀ v₀ s)
    rwa [← Matrix.mulVec_sub] at this
  have hz0 : z 0 = 0 := by
    simp only [hz, exp_zero_mulVec, mul_zero, Real.exp_zero, one_smul, zero_mul, sub_zero]
    exact sub_self _
  have hle := energy_le_exp_abscissa hzd ((liftUp_readings_iff S d _).2 le_rfl) ht
  rw [hz0, zero_dotProduct, mul_zero] at hle
  have hzz : z t ⬝ᵥ z t = 0 := by
    rw [one_mulVec] at hle
    have : 0 ≤ z t ⬝ᵥ z t := by
      simp only [dotProduct, Fin.sum_univ_two]
      nlinarith [mul_self_nonneg (z t 0), mul_self_nonneg (z t 1)]
    linarith
  exact sub_eq_zero.1 (dotProduct_self_eq_zero.1 hzz)

/-- [proved-derived; formal-checked] **The lift-up energy:** for `t ≥ 0` the kinetic energy of
`e^(tA)(u₀, v₀)` is `e^(−2dt)((u₀ − S t v₀)² + v₀²)`, the algebraic growth of the lifted
streamwise velocity against the viscous decay. -/
theorem liftUp_energy (S d u₀ v₀ t : ℝ) (ht : 0 ≤ t) :
    (NormedSpace.exp (t • liftUp S d) *ᵥ ![u₀, v₀]) ⬝ᵥ
        (NormedSpace.exp (t • liftUp S d) *ᵥ ![u₀, v₀]) =
      Real.exp (-2 * d * t) * ((u₀ - S * t * v₀) ^ 2 + v₀ ^ 2) := by
  rw [liftUp_exp S d u₀ v₀ t ht]
  simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have : Real.exp (-2 * d * t) = Real.exp (-d * t) * Real.exp (-d * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  ring

/-- [proved-derived; formal-checked] **Transient amplification while every mode decays.** At
`S = 1`, `d = 1/10` the only eigenvalue is `−1/10 < 0`, yet the energy of the response from
`(0, 1)` at `t = 2` is `5e^(−2/5) > 1`. -/
theorem liftUp_transient :
    (∀ (μ : ℝ) (w : Fin 2 → ℝ), w ≠ 0 → liftUp 1 (1 / 10) *ᵥ w = μ • w → μ < 0) ∧
      1 < (NormedSpace.exp ((2 : ℝ) • liftUp 1 (1 / 10)) *ᵥ ![0, 1]) ⬝ᵥ
        (NormedSpace.exp ((2 : ℝ) • liftUp 1 (1 / 10)) *ᵥ ![0, 1]) := by
  refine ⟨fun μ w hw h => by have := liftUp_eigenvalue hw h; linarith, ?_⟩
  rw [liftUp_energy 1 (1 / 10) 0 1 2 (by norm_num)]
  have h := Real.add_one_le_exp (-2 * (1 / 10) * 2)
  nlinarith

end Holonics.Physics.Fluid.LiftUp

section Audit
open Holonics.Physics.Fluid.LiftUp
#print axioms liftUp_eigenvalue
#print axioms liftUp_boost
#print axioms liftUp_reading
#print axioms liftUp_reading_le
#print axioms liftUp_readings_iff
#print axioms liftUp_energy_bound_iff
#print axioms liftUp_exp
#print axioms liftUp_energy
#print axioms liftUp_transient
end Audit

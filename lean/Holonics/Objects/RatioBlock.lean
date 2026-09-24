import Holonics.Objects.Ratio
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.MatrixPolynomialAlgebra
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Matrix.Normed

/-!
# Block ratios and the projective second order of a ratio

[definition] Object 9 of `docs/ELEMENTARY_OBJECTS.md`, continuing `Objects/Ratio` to matrix
(block) ratios `R = A_H⁻¹ A_T` of two transports and to the second-order projective invariant.
Nothing here founds a second ratio: the scalar faces are read in `Ratio.logFibre`, the pairs in
`Geometry/CrossRatio.RatioPresentation`, and a Möbius map is its `blockTransport`.

[proved-derived; formal-checked] What is proved.

1. **Jacobi's formula.** Along any entrywise-differentiable matrix curve `M(s)` with `M(t)`
   invertible, `d det M = det M · tr(M⁻¹M')` (`hasDerivAt_det_curve`); the scalar log derivative
   of the determinant is the trace of the matrix Maurer–Cartan form `R⁻¹dR`
   (`logDerivative_det_line`). Route: the permutation expansion of `det` gives a derivative that
   depends only on `(M(t), M')` (`hasDerivAt_det_entries`), and on the line `R + sR'` it is
   `det R · tr(R⁻¹R')` by Mathlib's `Matrix.derivative_det_one_add_X_smul`.
2. **`det(exp A) = exp(tr A)`** over `ℂ` (`det_exp`; listed as a TODO in Mathlib's
   `MatrixExponential`). Route: `f(t) = det exp(tA)` satisfies `f' = f · tr A` by Jacobi, so
   `f(t) e^{−t tr A}` has zero derivative and equals its value `1` at `0`.
3. **The trace of a declared matrix log lies in the log fibre of the determinant ratio.** For a
   declared log `L` of `R = A_H⁻¹A_T` (`exp L = R`, `A_H` invertible),
   `tr L ∈ logFibre (det A_T : det A_H)` (`trace_log_mem_logFibre`), so `tr log R = log det R`
   modulo `2πiℤ` (`trace_log_eq_log_det_mod`). Witness: `0` and `diag(2πi, 0)` are two declared
   logs of `R = 1` whose traces differ by one turn (`trace_log_carries_the_winding`): the
   determinant face cannot choose the branch, the declared log carries it.
4. **The Schwarzian.** `S(f) = (f''/f')' − ½(f''/f')²`, computed from a declared 3-jet on an open
   set as `f'''/f' − (3/2)(f''/f')²` (`schwarzian_eq_of_jet`). A Möbius map
   `M(w) = (aw+b)/(cw+d)`, `ad − bc ≠ 0`, transports the jet explicitly (`mobius_jet`) and
   **`S(M ∘ f) = S(f)`** wherever `cf + d ≠ 0` (`schwarzian_mobius_comp`); hence **`S(M) = 0`**
   (`schwarzian_mobius`). Witnesses: `S(exp) = −1/2`, `S(w²) = −3/(2w²)`.
5. **The cross ratio sees exactly the Möbius transports.** On undivided pairs the bracket
   `[p, q] = p.num q.den − q.num p.den` scales by `ad − bc` under `blockTransport a b c d`
   (`bracket_blockTransport`); the projective swing pair of four points scales by `(ad − bc)²`
   (`projectiveSwing_mobius`) and restricts to `CrossRatio.swingPair` on affine points
   (`projectiveSwing_points`); so the scalar `crossRatio` is Möbius invariant
   (`crossRatio_mobius`), extending the owner's `crossRatio_affine`. The Schwarzian is the
   second-order invariant under the same group: it is invariant under post-composition by the
   transports the cross ratio cannot see and vanishes on them.

[open] The converse `S(f) = 0 ⇒ f` Möbius (an ODE uniqueness statement), the cocycle
`S(f ∘ g) = (S f ∘ g) g'² + S g`, the infinitesimal cross-ratio expansion of `S`, a principal
matrix logarithm and its domain, and Jacobi for real-parameter curves of real matrices are not
proved here.

No `sorry`, no `axiom`, no `native_decide`; the audit block prints the axioms.
-/

noncomputable section

namespace Holonics.Objects.RatioBlock

open Equiv Finset Matrix Polynomial Filter Topology
open Holonics
open Holonics.Objects.Ratio

/-! ## 1. Jacobi's formula -/

section Jacobi

open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] The derivative of `det` read from the permutation expansion at the value `M` in
the direction `M'`. -/
def detDeriv (M M' : Matrix n n ℂ) : ℂ :=
  ∑ σ : Perm n, (Perm.sign σ : ℂ) * ∑ i, (∏ j ∈ univ.erase i, M (σ j) j) * M' (σ i) i

/-- [proved-derived; formal-checked] Along an entrywise-differentiable curve, `det` has the
derivative `detDeriv (M t) M'`: it depends only on the value and the velocity. -/
theorem hasDerivAt_det_entries {M : ℂ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℂ}
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) :
    HasDerivAt (fun s => (M s).det) (detDeriv (M t) M') t := by
  have hfun : (fun s => (M s).det) =
      fun s => ∑ σ : Perm n, (Perm.sign σ : ℂ) * ∏ i, M s (σ i) i := by
    funext s
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  have := HasDerivAt.fun_finsetProd (u := univ) (fun i _ => h (σ i) i)
  simpa [smul_eq_mul] using this

/-- [proved-derived; formal-checked] `d/ds det(1 + sA)|₀ = tr A`, from
`Matrix.derivative_det_one_add_X_smul`. -/
theorem hasDerivAt_det_line_one (A : Matrix n n ℂ) :
    HasDerivAt (fun s : ℂ => (1 + s • A).det) (trace A) 0 := by
  set P : ℂ[X] := (1 + (X : ℂ[X]) • A.map C).det
  have hP : ∀ s : ℂ, (1 + s • A).det = P.eval s := by
    intro s
    rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij] <;> ring
  have hfun : (fun s : ℂ => (1 + s • A).det) = fun s => P.eval s := funext hP
  rw [hfun]
  have := P.hasDerivAt 0
  rwa [Matrix.derivative_det_one_add_X_smul] at this

/-- [proved-derived; formal-checked] At the identity the expansion derivative is the trace. -/
theorem detDeriv_one (A : Matrix n n ℂ) : detDeriv 1 A = trace A := by
  have h1 := hasDerivAt_det_entries (M := fun s : ℂ => 1 + s • A) (M' := A) (t := 0)
    (fun i j => by
      simpa using ((hasDerivAt_id (0:ℂ)).mul_const (A i j)).const_add ((1 : Matrix n n ℂ) i j))
  simp only [zero_smul, add_zero] at h1
  exact h1.unique (hasDerivAt_det_line_one A)

/-- [proved-derived; formal-checked] Jacobi along a line through an invertible matrix:
`det(R + sR') = det R · det(1 + s R⁻¹R')`. -/
theorem hasDerivAt_det_line {R : Matrix n n ℂ} (hR : IsUnit R.det) (R' : Matrix n n ℂ) :
    HasDerivAt (fun s : ℂ => (R + s • R').det) (R.det * trace (R⁻¹ * R')) 0 := by
  have hfac : ∀ s : ℂ, (R + s • R').det = R.det * (1 + s • (R⁻¹ * R')).det := by
    intro s
    rw [← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hR, Matrix.one_mul]
  have hfun : (fun s : ℂ => (R + s • R').det) = fun s => R.det * (1 + s • (R⁻¹ * R')).det :=
    funext hfac
  rw [hfun]
  exact (hasDerivAt_det_line_one _).const_mul _

/-- [proved-derived; formal-checked] The expansion derivative at an invertible value is
`det R · tr(R⁻¹R')`. -/
theorem detDeriv_eq {R : Matrix n n ℂ} (hR : IsUnit R.det) (R' : Matrix n n ℂ) :
    detDeriv R R' = R.det * trace (R⁻¹ * R') := by
  have h1 := hasDerivAt_det_entries (M := fun s : ℂ => R + s • R') (M' := R') (t := 0)
    (fun i j => by
      simpa using ((hasDerivAt_id (0:ℂ)).mul_const (R' i j)).const_add (R i j))
  simp only [zero_smul, add_zero] at h1
  exact h1.unique (hasDerivAt_det_line hR R')

/-- [proved-derived; formal-checked] **Jacobi's formula** along any entrywise-differentiable curve
through an invertible matrix. -/
theorem hasDerivAt_det_curve {M : ℂ → Matrix n n ℂ} {M' : Matrix n n ℂ} {t : ℂ}
    (h : ∀ i j, HasDerivAt (fun s => M s i j) (M' i j) t) (hM : IsUnit (M t).det) :
    HasDerivAt (fun s => (M s).det) ((M t).det * trace ((M t)⁻¹ * M')) t := by
  rw [← detDeriv_eq hM]
  exact hasDerivAt_det_entries h

/-- [proved-derived; formal-checked] The entries of `exp(uA)` move by the entries of
`exp(tA) A`. -/
theorem hasDerivAt_exp_entries (A : Matrix n n ℂ) (t : ℂ) (i j : n) :
    HasDerivAt (fun u : ℂ => NormedSpace.exp (u • A) i j) ((NormedSpace.exp (t • A) * A) i j) t :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => n → ℂ) i)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (𝕂 := ℂ) A t)

/-- [proved-derived; formal-checked] **`det(exp A) = exp(tr A)`.** -/
theorem det_exp (A : Matrix n n ℂ) : (NormedSpace.exp A).det = Complex.exp (trace A) := by
  set f : ℂ → ℂ := fun t => (NormedSpace.exp (t • A)).det
  have hunit : ∀ t : ℂ, IsUnit (NormedSpace.exp (t • A)).det := fun t =>
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.isUnit_exp _)
  have hf : ∀ t, HasDerivAt f (f t * trace A) t := by
    intro t
    have h := hasDerivAt_det_curve (hasDerivAt_exp_entries A t) (hunit t)
    rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hunit t), Matrix.one_mul] at h
  set g : ℂ → ℂ := fun t => f t * Complex.exp (-(t * trace A))
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have he : HasDerivAt (fun t : ℂ => Complex.exp (-(t * trace A)))
        (Complex.exp (-(t * trace A)) * (-(1 * trace A))) t :=
      (((hasDerivAt_id t).mul_const (trace A)).neg).cexp
    have := (hf t).mul he
    refine this.congr_deriv ?_
    ring
  have hconst : g 1 = g 0 := by
    have hd : Differentiable ℂ g := fun t => (hg t).differentiableAt
    exact is_const_of_deriv_eq_zero hd (fun t => (hg t).deriv) 1 0
  have hg0 : g 0 = 1 := by simp [g, f]
  have hg1 : g 1 = (NormedSpace.exp A).det * Complex.exp (-trace A) := by simp [g, f]
  rw [hg0, hg1] at hconst
  have := congrArg (· * Complex.exp (trace A)) hconst
  simp only [one_mul, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
    mul_one] at this
  exact this

/-- [proved-derived; formal-checked] **The log derivative of the determinant is the trace of
`R⁻¹dR`.** Along `R + sR'` with `R` invertible, `(det R)⁻¹ · d det = tr(R⁻¹R')`: the scalar ratio
face of a block ratio reads the trace of its Maurer–Cartan form. -/
theorem logDerivative_det_line {R : Matrix n n ℂ} (hR : IsUnit R.det) (R' : Matrix n n ℂ) :
    ∃ D : ℂ, HasDerivAt (fun s : ℂ => (R + s • R').det) D 0 ∧
      (R.det)⁻¹ * D = trace (R⁻¹ * R') := by
  refine ⟨_, hasDerivAt_det_line hR R', ?_⟩
  rw [← mul_assoc, inv_mul_cancel₀ hR.ne_zero, one_mul]

end Jacobi

/-! ## 2. The trace of a declared matrix log is a log of the determinant ratio -/

section BlockLog

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **`tr log R` lies in the log fibre of the determinant
ratio.** For a declared log `L` of the block ratio `R = A_H⁻¹ A_T` (`exp L = R`, `A_H`
invertible), `exp(tr L) · det A_H = det A_T`: the trace is a log of the undivided determinant
pair `(det A_T : det A_H)` of `Ratio.logFibre`. -/
theorem trace_log_mem_logFibre {A_H A_T L : Matrix n n ℂ} (hH : IsUnit A_H.det)
    (hL : NormedSpace.exp L = A_H⁻¹ * A_T) :
    trace L ∈ logFibre (holonRatio A_T.det A_H.det) := by
  change Complex.exp (trace L) * A_H.det = A_T.det
  rw [← det_exp, hL, Matrix.det_mul, Matrix.det_nonsing_inv, mul_comm, ← mul_assoc,
    Ring.mul_inverse_cancel _ hH, one_mul]

/-- [proved-derived; formal-checked] **`tr log R = log det R` modulo `2πiℤ`.** Every log `ℓ` of the
determinant ratio differs from the trace of a declared matrix log by whole turns
(`Ratio.logFibre_torsor`). -/
theorem trace_log_eq_log_det_mod {A_H A_T L : Matrix n n ℂ} (hH : IsUnit A_H.det)
    (hL : NormedSpace.exp L = A_H⁻¹ * A_T) {ℓ : ℂ}
    (hℓ : ℓ ∈ logFibre (holonRatio A_T.det A_H.det)) :
    ∃ k : ℤ, trace L = ℓ + k * (2 * Real.pi * Complex.I) :=
  (logFibre_torsor (r := holonRatio A_T.det A_H.det) hH.ne_zero hℓ).mp
    (trace_log_mem_logFibre hH hL)

/-- [proved-derived; formal-checked] **Witness: the declared log carries the winding the
determinant face cannot.** `0` and `diag(2πi, 0)` both exponentiate to the identity (so both are
declared logs of `R = 1⁻¹ · 1`), and their traces differ by exactly one turn `2πi`. -/
theorem trace_log_carries_the_winding :
    NormedSpace.exp (0 : Matrix (Fin 2) (Fin 2) ℂ) = 1 ∧
      NormedSpace.exp (diagonal ![2 * Real.pi * Complex.I, 0]) = (1 : Matrix (Fin 2) (Fin 2) ℂ) ∧
      trace (diagonal ![(2 * Real.pi * Complex.I : ℂ), 0]) - trace (0 : Matrix (Fin 2) (Fin 2) ℂ) =
        2 * Real.pi * Complex.I := by
  refine ⟨NormedSpace.exp_zero, ?_, ?_⟩
  · rw [Matrix.exp_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonal, ← Complex.exp_eq_exp_ℂ, Complex.exp_two_pi_mul_I]
  · simp [trace, Fin.sum_univ_two]

end BlockLog

/-! ## 3. The Schwarzian: the second-order invariant of the projective chart -/

section Schwarzian

/-- [definition] The pre-Schwarzian `f''/f'`: the first order of `log f'`. -/
def preSchwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ := deriv (deriv f) z / deriv f z
/-- [definition] The Schwarzian `S(f) = (f''/f')' − ½ (f''/f')²`. -/
def schwarzian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv (preSchwarzian f) z - (1 / 2) * preSchwarzian f z ^ 2

/-- [definition] A declared 3-jet of `f` on `U`: `f' = f₁`, `f₁' = f₂`, `f₂' = f₃` there. -/
structure Jet3On (f f₁ f₂ f₃ : ℂ → ℂ) (U : Set ℂ) : Prop where
  d₀ : ∀ w ∈ U, HasDerivAt f (f₁ w) w
  d₁ : ∀ w ∈ U, HasDerivAt f₁ (f₂ w) w
  d₂ : ∀ w ∈ U, HasDerivAt f₂ (f₃ w) w

/-- [proved-derived; formal-checked] On an open set the pre-Schwarzian reads `f₂/f₁`. -/
theorem Jet3On.preSchwarzian_eq {f f₁ f₂ f₃ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hj : Jet3On f f₁ f₂ f₃ U) {w : ℂ} (hw : w ∈ U) :
    preSchwarzian f w = f₂ w / f₁ w := by
  have h1 : deriv f =ᶠ[𝓝 w] f₁ :=
    Filter.eventually_of_mem (hU.mem_nhds hw) fun v hv => (hj.d₀ v hv).deriv
  rw [preSchwarzian, h1.deriv_eq, (hj.d₁ w hw).deriv, (hj.d₀ w hw).deriv]

/-- [proved-derived; formal-checked] **The Schwarzian of a declared jet**:
`S(f) = f₃/f₁ − (3/2)(f₂/f₁)²`. -/
theorem schwarzian_eq_of_jet {f f₁ f₂ f₃ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hj : Jet3On f f₁ f₂ f₃ U) (hne : ∀ w ∈ U, f₁ w ≠ 0) {z : ℂ} (hz : z ∈ U) :
    schwarzian f z = f₃ z / f₁ z - 3 / 2 * (f₂ z / f₁ z) ^ 2 := by
  have hev : preSchwarzian f =ᶠ[𝓝 z] fun w => f₂ w / f₁ w :=
    Filter.eventually_of_mem (hU.mem_nhds hz) fun v hv => hj.preSchwarzian_eq hU hv
  have hd : HasDerivAt (fun w => f₂ w / f₁ w)
      ((f₃ z * f₁ z - f₂ z * f₂ z) / f₁ z ^ 2) z :=
    (hj.d₂ z hz).div (hj.d₁ z hz) (hne z hz)
  rw [schwarzian, hev.deriv_eq, hd.deriv, hj.preSchwarzian_eq hU hz]
  have := hne z hz
  field_simp
  ring

/-- [definition] The Möbius map `w ↦ (aw + b)/(cw + d)`, the affine chart of
`RatioPresentation.blockTransport a b c d` at `(w : 1)`. -/
def mobius (a b c d : ℂ) (w : ℂ) : ℂ := (a * w + b) / (c * w + d)

/-- [proved-derived; formal-checked] **The Möbius transport of a 3-jet**, with
`D = ad − bc` and `u = cf + d`: `(M∘f)' = D f₁/u²`, `(M∘f)'' = D f₂/u² − 2cD f₁²/u³`,
`(M∘f)''' = D f₃/u² − 6cD f₁f₂/u³ + 6c²D f₁³/u⁴`. -/
theorem mobius_jet {f f₁ f₂ f₃ : ℂ → ℂ} {U : Set ℂ} (hj : Jet3On f f₁ f₂ f₃ U)
    (a b c d : ℂ) (hden : ∀ w ∈ U, c * f w + d ≠ 0) :
    Jet3On (fun w => mobius a b c d (f w))
      (fun w => (a * d - b * c) * f₁ w / (c * f w + d) ^ 2)
      (fun w => (a * d - b * c) * f₂ w / (c * f w + d) ^ 2
        - 2 * c * (a * d - b * c) * f₁ w ^ 2 / (c * f w + d) ^ 3)
      (fun w => (a * d - b * c) * f₃ w / (c * f w + d) ^ 2
        - 6 * c * (a * d - b * c) * f₁ w * f₂ w / (c * f w + d) ^ 3
        + 6 * c ^ 2 * (a * d - b * c) * f₁ w ^ 3 / (c * f w + d) ^ 4) U := by
  constructor
  · intro w hw
    have hu := hden w hw
    have hn : HasDerivAt (fun v => a * f v + b) (a * f₁ w) w := ((hj.d₀ w hw).const_mul a).add_const b
    have hdn : HasDerivAt (fun v => c * f v + d) (c * f₁ w) w := ((hj.d₀ w hw).const_mul c).add_const d
    refine (hn.div hdn hu).congr_deriv ?_
    field_simp
    ring
  · intro w hw
    have hu := hden w hw
    have hdn : HasDerivAt (fun v => c * f v + d) (c * f₁ w) w :=
      ((hj.d₀ w hw).const_mul c).add_const d
    refine (((hj.d₁ w hw).const_mul (a * d - b * c)).fun_div (hdn.fun_pow 2)
      (pow_ne_zero 2 hu)).congr_deriv ?_
    field_simp
    ring
  · intro w hw
    have hu := hden w hw
    have hdn : HasDerivAt (fun v => c * f v + d) (c * f₁ w) w :=
      ((hj.d₀ w hw).const_mul c).add_const d
    have h1 := ((hj.d₂ w hw).const_mul (a * d - b * c)).fun_div (hdn.fun_pow 2)
      (pow_ne_zero 2 hu)
    have h2 := ((((hj.d₁ w hw).fun_pow 2).const_mul (2 * c * (a * d - b * c))).fun_div
      (hdn.fun_pow 3) (pow_ne_zero 3 hu))
    refine (h1.sub h2).congr_deriv ?_
    field_simp
    ring

/-- [proved-derived; formal-checked] **Möbius invariance: `S(M ∘ f) = S(f)`.** -/
theorem schwarzian_mobius_comp {f f₁ f₂ f₃ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hj : Jet3On f f₁ f₂ f₃ U) (hne : ∀ w ∈ U, f₁ w ≠ 0)
    {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) (hden : ∀ w ∈ U, c * f w + d ≠ 0)
    {z : ℂ} (hz : z ∈ U) :
    schwarzian (fun w => mobius a b c d (f w)) z = schwarzian f z := by
  have hg1 : ∀ w ∈ U, (a * d - b * c) * f₁ w / (c * f w + d) ^ 2 ≠ 0 := fun w hw =>
    div_ne_zero (mul_ne_zero hdet (hne w hw)) (pow_ne_zero 2 (hden w hw))
  rw [schwarzian_eq_of_jet hU (mobius_jet hj a b c d hden) hg1 hz,
    schwarzian_eq_of_jet hU hj hne hz]
  have h1 := hne z hz
  have hu := hden z hz
  field_simp
  ring

/-- [proved-derived; formal-checked] **`S(M) = 0`** off the pole of `M`. -/
theorem schwarzian_mobius {a b c d : ℂ} (hdet : a * d - b * c ≠ 0) {z : ℂ}
    (hz : c * z + d ≠ 0) : schwarzian (mobius a b c d) z = 0 := by
  have hU : IsOpen {w : ℂ | c * w + d ≠ 0} :=
    isOpen_ne_fun (by fun_prop) continuous_const
  have hj : Jet3On (fun w : ℂ => w) (fun _ => 1) (fun _ => 0) (fun _ => 0) {w | c * w + d ≠ 0} :=
    ⟨fun w _ => hasDerivAt_id w, fun w _ => hasDerivAt_const w 1,
      fun w _ => hasDerivAt_const w 0⟩
  have h := schwarzian_mobius_comp hU hj (fun _ _ => one_ne_zero) hdet (fun w hw => hw) hz
  rw [schwarzian_eq_of_jet hU hj (fun _ _ => one_ne_zero) hz] at h
  simpa using h

/-- [proved-derived; formal-checked] Witness: `S(exp) = −1/2`. -/
theorem schwarzian_exp (z : ℂ) : schwarzian Complex.exp z = -1 / 2 := by
  have hj : Jet3On Complex.exp Complex.exp Complex.exp Complex.exp Set.univ :=
    ⟨fun w _ => Complex.hasDerivAt_exp w, fun w _ => Complex.hasDerivAt_exp w,
      fun w _ => Complex.hasDerivAt_exp w⟩
  rw [schwarzian_eq_of_jet isOpen_univ hj (fun w _ => Complex.exp_ne_zero w) (Set.mem_univ z)]
  have := Complex.exp_ne_zero z
  field_simp
  norm_num

/-- [proved-derived; formal-checked] Witness: `S(w²) = −3/(2w²) ≠ 0`; the square is not a
projective transport. -/
theorem schwarzian_sq {z : ℂ} (hz : z ≠ 0) : schwarzian (fun w => w ^ 2) z = -3 / (2 * z ^ 2) := by
  have hj : Jet3On (fun w : ℂ => w ^ 2) (fun w => 2 * w) (fun _ => 2) (fun _ => 0) {w | w ≠ 0} :=
    ⟨fun w _ => by simpa [mul_comm] using hasDerivAt_pow 2 w,
      fun w _ => by simpa using (hasDerivAt_id w).const_mul (2 : ℂ),
      fun w _ => hasDerivAt_const w 2⟩
  rw [schwarzian_eq_of_jet (isOpen_ne) hj (fun w hw => mul_ne_zero two_ne_zero hw) hz]
  field_simp
  ring
end Schwarzian

/-! ## 4. The cross ratio of undivided pairs is Möbius invariant -/

section CrossRatio

variable {K : Type*} [Field K]

/-- [definition] The bracket (determinant) of two undivided pairs. -/
def bracket (p q : RatioPresentation K) : K := p.num * q.den - q.num * p.den

/-- [proved-derived; formal-checked] **The bracket scales by the determinant of the transport.** -/
theorem bracket_blockTransport (a b c d : K) (p q : RatioPresentation K) :
    bracket (p.blockTransport a b c d) (q.blockTransport a b c d) =
      (a * d - b * c) * bracket p q := by
  simp only [bracket, RatioPresentation.blockTransport]; ring

/-- [definition] The swing pair of four projective points, undivided. -/
def projectiveSwing (p₁ p₂ p₃ p₄ : RatioPresentation K) : RatioPresentation K :=
  ⟨bracket p₃ p₁ * bracket p₄ p₂, bracket p₃ p₂ * bracket p₄ p₁⟩

/-- [definition] The affine point `(z : 1)`. -/
def point (z : K) : RatioPresentation K := ⟨z, 1⟩

/-- [proved-derived; formal-checked] On affine points the projective swing pair is the owner's
`swingPair`. -/
theorem projectiveSwing_points (a b c d : K) :
    projectiveSwing (point a) (point b) (point c) (point d) = swingPair a b c d := by
  apply RatioPresentation.ext <;> simp [projectiveSwing, bracket, point, swingPair]

/-- [proved-derived; formal-checked] **A Möbius transport scales the swing pair by `(ad − bc)²`**,
so the pair is projectively unchanged; no division is performed. -/
theorem projectiveSwing_mobius (A B C D : K) (p₁ p₂ p₃ p₄ : RatioPresentation K) :
    projectiveSwing (p₁.blockTransport A B C D) (p₂.blockTransport A B C D)
      (p₃.blockTransport A B C D) (p₄.blockTransport A B C D) =
      (projectiveSwing p₁ p₂ p₃ p₄).scale ((A * D - B * C) ^ 2) := by
  apply RatioPresentation.ext <;>
    simp only [projectiveSwing, bracket_blockTransport, RatioPresentation.scale] <;> ring

/-- [proved-derived; formal-checked] **The scalar cross ratio is Möbius invariant**, extending
`crossRatio_affine` from affine maps to the whole projective group. -/
theorem crossRatio_mobius {A B C D a b c d : K} (hdet : A * D - B * C ≠ 0)
    (ha : C * a + D ≠ 0) (hb : C * b + D ≠ 0) (hc : C * c + D ≠ 0) (hd : C * d + D ≠ 0)
    (hcb : c - b ≠ 0) (hda : d - a ≠ 0) :
    crossRatio ((A * a + B) / (C * a + D)) ((A * b + B) / (C * b + D))
      ((A * c + B) / (C * c + D)) ((A * d + B) / (C * d + D)) = crossRatio a b c d := by
  have key : ∀ x y : K, C * x + D ≠ 0 → C * y + D ≠ 0 →
      (A * x + B) / (C * x + D) - (A * y + B) / (C * y + D) =
        (A * D - B * C) * (x - y) / ((C * x + D) * (C * y + D)) := by
    intro x y hx hy
    rw [div_sub_div _ _ hx hy]
    congr 1
    ring
  simp only [crossRatio, swingPair]
  rw [key c a hc ha, key d b hd hb, key c b hc hb, key d a hd ha]
  field_simp

/-- [proved-derived; formal-checked] **The Möbius map is the affine chart of the block
transport**: `mobius a b c d w` is `blockTransport a b c d (w : 1)` divided out. -/
theorem mobius_eq_blockTransport_chart (a b c d w : ℂ) :
    mobius a b c d w = (RatioPresentation.blockTransport a b c d (point w)).num /
      (RatioPresentation.blockTransport a b c d (point w)).den := by
  simp [mobius, RatioPresentation.blockTransport, point]

end CrossRatio

section Audit

#print axioms hasDerivAt_det_entries
#print axioms detDeriv_one
#print axioms hasDerivAt_det_line
#print axioms hasDerivAt_det_curve
#print axioms logDerivative_det_line
#print axioms det_exp
#print axioms trace_log_mem_logFibre
#print axioms trace_log_eq_log_det_mod
#print axioms trace_log_carries_the_winding
#print axioms schwarzian_eq_of_jet
#print axioms mobius_jet
#print axioms schwarzian_mobius_comp
#print axioms schwarzian_mobius
#print axioms schwarzian_exp
#print axioms schwarzian_sq
#print axioms bracket_blockTransport
#print axioms projectiveSwing_points
#print axioms projectiveSwing_mobius
#print axioms crossRatio_mobius
#print axioms mobius_eq_blockTransport_chart

end Audit

end Holonics.Objects.RatioBlock

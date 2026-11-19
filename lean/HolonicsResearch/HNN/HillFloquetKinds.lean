import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Hill's Floquet kinds: a lossless period of ticks is a move of `SL(2)`, read by its trace, and past the tongue's edge the pumped tick selects the two sheets

[proved-standard] The source is #410's box "Pump/Floquet locking: the pumped tick selects the two sheets as
attracting basins, and Hill's Floquet kinds hold (turn, boost in a tongue, shear at its edge; trace below −2)",
beside `Holonics/HNN/Floquet` (the pump's axes, the bifurcation and the growth certificate) and
`Objects/ParametronLock`; the guide's swing (`docs/ELEMENTARY_OBJECTS.md`: every `SL(2)` move is a turn, a boost
or a shear) and the parametron's period doubling owed in #410's box on the synchronous two-cycle.

The model. One cell's displacement and rate, `x ∈ ℝ²`, and one period of the pump's ticks, its monodromy `M`, a
real `2 × 2` matrix. A lossless tick keeps the area of a cell of states, `det M = 1` (Liouville's law for Hill's
equation; for the Cayley tick of a traceless rate, `lossless_cayley_det`), so the monodromy is a move of `SL(2, ℝ)`
and its multipliers `ν` are the roots of `ν² − τν + 1`, `τ = tr M` (`multiplier_quadratic`).

The kinds themselves are `Compression/Landmark/SiteKind`'s, read on any real `2 × 2` move: a rotation exactly when no
real number is an eigenvalue (`rotation_iff_no_real_eigenvalue`), a boost exactly when two real eigenvalues share a
sign (`boost_iff_two_real_eigenvalues`), null exactly when the traceless part is nilpotent (`null_iff_traceless_nilpotent`),
and a boost of determinant one is a Lorentz boost with Doppler ratio `k` (`boost_doppler_ratio`). This file reads them as
Hill's kinds of a period of the pump: it separates the boost below `−2`, whose multiplier is negative and flips the cell
each period, from the tongue's boost above `2`, names the shear at the edge, joins the lossless tick to `SL(2)`, and
states what the tongue's boost does to a state.

What is proved.

1. **Cayley–Hamilton on a move** (`sq_eq_trace_sub`): `M² = τ M − det M · 1`.
2. **A lossless period is a move of `SL(2)`** (`lossless_cayley_det`, `monodromy_det_one`): the Cayley tick
   `(2 − hA)⁻¹(2 + hA)` of a traceless rate `A` has determinant one, and so does any product of such ticks.
3. **Hill's kinds by the trace.**
   - *The turn* (`turn_no_real_multiplier`, `turn_multiplier_on_circle`): for `|τ| < 2` no state is carried to a
     real multiple of itself, and every complex multiplier has modulus one and is not real.
   - *The boost in a tongue* (`boost_multiplier`): for `τ > 2` a state is carried to `ν` times itself with
     `ν = (τ + √(τ² − 4))/2 > 1`, and another to `ν⁻¹` times itself.
   - *The subharmonic below `−2`* (`subharmonic_multiplier`, `subharmonic_flips_and_grows`): for `τ < −2` a state
     is carried to `ν` times itself with `ν = (τ − √(τ² − 4))/2 < −1`: it flips each period and grows, `Mⁿv = νⁿv`,
     the period doubling of the parametron (`HNN/SynchronousTwoCycle.flip_each_pass` reads the same multiplier on
     the sign chart).
   - *The shear at the edge* (`edge_shear_plus`, `edge_shear_minus`): at `τ = 2`, `(M − 1)² = 0`; at `τ = −2`,
     `(M + 1)² = 0`: a double multiplier `±1`, a shear unless `M = ±1`.
4. **The pumped tick selects the two sheets** (`sheet_selected`): in a tongue, with `M v = ν v`, `M w = ν⁻¹ w` and
   `ν > 1`, every state `x = α v + β w` read at the growth's own clock, `ν⁻ⁿ Mⁿ x`, tends to `α v`: the two sheets
   `±v` attract the two open half-planes on either side of the squeezed axis `ℝ w`, and the sign of `α`, the input's
   in-phase coordinate, selects the sheet (`HNN/Floquet.inphase_growing_coordinate` gives that covector in the
   continuous chart).

Limits. The trace is taken as given: which pump strengths and detunings put `τ` above `2` (the Mathieu tongues'
boundaries) is not computed here, nor the rotating pump's principal resonance below `−2`. The sheets attract in
direction at the growth's clock; a saturating constitution that holds them at a finite amplitude is not modelled.

The computational object is the helical pair interaction: one period of the pump is the cell holonomy of the
pump's cycle, its trace the cross ratio of the move's two pivots, and the sheets the half-turn pair of the lock. Of
the winding guide's six general objects this touches the cell holonomy (the monodromy) and the helix (the pump's
clock, whose half-period the subharmonic counts); the pair, the faces and placement, the tube and the tower thread
stay attached.

Consumers: the atlas row `parametron.hill-floquet-kinds` (beside `landmark.site-kind-matrix`), `HNN/Floquet`'s open line on the
subharmonic multiplier, and `HNN/SynchronousTwoCycle`'s owed period doubling.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.HillFloquetKinds

open Matrix Filter Topology

variable (M : Matrix (Fin 2) (Fin 2) ℝ)

/-- [proved-standard] **Cayley–Hamilton on a move:** `M² = (tr M) M − (det M) 1`. -/
theorem sq_eq_trace_sub : M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

/-- [proved-standard] The determinant of `s · 1 + B` for a `2 × 2` block: `s² + s tr B + det B`. -/
theorem det_smul_one_add (s : ℝ) (B : Matrix (Fin 2) (Fin 2) ℝ) :
    (s • (1 : Matrix (Fin 2) (Fin 2) ℝ) + B).det = s ^ 2 + s * B.trace + B.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

/-- [proved-derived] **A lossless tick keeps area:** the Cayley tick `(2 − hA)⁻¹(2 + hA)` of a traceless rate `A`
has determinant one, wherever `2 − hA` is invertible. -/
theorem lossless_cayley_det {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.trace = 0) (h : ℝ)
    (hinv : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - h • A).det ≠ 0) :
    (((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - h • A)⁻¹ *
      ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + h • A)).det = 1 := by
  have hm : ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - h • A) =
      (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (-h) • A := by
    rw [neg_smul, ← sub_eq_add_neg]
  have hdet : ∀ s : ℝ, ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + s • A).det = 4 + s ^ 2 * A.det := by
    intro s
    rw [det_smul_one_add, Matrix.trace_smul, hA, Matrix.det_smul]
    simp [Fintype.card_fin]
    ring
  rw [hm] at hinv ⊢
  rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdet (-h), hdet h, neg_sq]
  rw [hdet (-h), neg_sq] at hinv
  exact inv_mul_cancel₀ hinv

/-- [proved-standard] **A period of lossless ticks is a move of `SL(2)`:** a product of determinant-one ticks has
determinant one. -/
theorem monodromy_det_one (ticks : List (Matrix (Fin 2) (Fin 2) ℝ)) (h : ∀ T ∈ ticks, T.det = 1) :
    ticks.prod.det = 1 := by
  induction ticks with
  | nil => simp
  | cons T ts ih =>
    rw [List.prod_cons, Matrix.det_mul, h T (List.mem_cons_self), ih (fun S hS => h S (List.mem_cons_of_mem T hS)),
      one_mul]

/-- [proved-standard] **A multiplier is a root of the trace's quadratic:** for `det M = 1`, a state carried to
`ν` times itself has `ν² − τν + 1 = 0`. -/
theorem multiplier_quadratic (hdet : M.det = 1) {ν : ℝ} {v : Fin 2 → ℝ} (hv : v ≠ 0) (hMv : M *ᵥ v = ν • v) :
    ν ^ 2 - M.trace * ν + 1 = 0 := by
  have h2 : (M * M) *ᵥ v = (ν ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, hMv, smul_smul, sq]
  rw [sq_eq_trace_sub, hdet, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hMv,
    Matrix.one_mulVec, smul_smul, one_smul] at h2
  have h3 : (ν ^ 2 - M.trace * ν + 1) • v = 0 := by
    rw [sub_add, sub_smul, sub_smul, one_smul, ← h2]
    module
  rcases smul_eq_zero.mp h3 with h | h
  · exact h
  · exact absurd h hv

/-- [proved-standard] **A root of the trace's quadratic is a multiplier:** a real root `ν` of `ν² − τν + 1` with
`det M = 1` carries some state `v ≠ 0` to `ν v`. -/
theorem exists_multiplier (hdet : M.det = 1) {ν : ℝ} (hν : ν ^ 2 - M.trace * ν + 1 = 0) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M *ᵥ v = ν • v := by
  have hd : (M - ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 0 := by
    have h := det_smul_one_add (-ν) M
    have hneg : (-ν) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + M = M - ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [neg_smul]; abel
    rw [hneg, hdet] at h
    rw [h]
    linarith
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

/-- [proved-standard] **The turn, on the real chart:** for `|τ| < 2` and `det M = 1` no state is carried to a real
multiple of itself. -/
theorem turn_no_real_multiplier (hdet : M.det = 1) (hτ : |M.trace| < 2) {ν : ℝ} {v : Fin 2 → ℝ} (hv : v ≠ 0) :
    M *ᵥ v ≠ ν • v := by
  intro hMv
  have hq := multiplier_quadratic M hdet hv hMv
  have hsq : M.trace ^ 2 < 4 := by
    have := abs_lt.mp hτ
    nlinarith
  nlinarith [sq_nonneg (2 * ν - M.trace)]

/-- [proved-standard] **The turn, on the complex chart:** for a real `τ` with `|τ| < 2`, every root of
`ν² − τν + 1` has modulus one and is not real: the multipliers are `e^(±iθ)`, `cos θ = τ/2`. -/
theorem turn_multiplier_on_circle {τ : ℝ} (hτ : |τ| < 2) {ν : ℂ} (hν : ν ^ 2 - τ * ν + 1 = 0) :
    ‖ν‖ = 1 ∧ ν.im ≠ 0 := by
  have hre := congrArg Complex.re hν
  have him := congrArg Complex.im hν
  simp [sq, Complex.mul_re, Complex.mul_im] at hre him
  have hsq : τ ^ 2 < 4 := by
    have := abs_lt.mp hτ
    nlinarith
  have hy : ν.im ≠ 0 := by
    intro hy0
    rw [hy0] at hre
    nlinarith [sq_nonneg (2 * ν.re - τ)]
  have hx : ν.re = τ / 2 := by
    have : ν.im * (2 * ν.re - τ) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hy
    · linarith
  refine ⟨?_, hy⟩
  have hn : Complex.normSq ν = 1 := by
    rw [Complex.normSq_apply]
    rw [hx] at hre ⊢
    nlinarith
  rw [← Complex.sq_norm] at hn
  have h0 : 0 ≤ ‖ν‖ := norm_nonneg ν
  nlinarith

/-- [proved-standard] **The boost in a tongue:** for `τ > 2` and `det M = 1`, `ν = (τ + √(τ² − 4))/2 > 1` and its
inverse are multipliers, each carrying some state to that multiple of itself. -/
theorem boost_multiplier (hdet : M.det = 1) (hτ : 2 < M.trace) :
    let ν := (M.trace + Real.sqrt (M.trace ^ 2 - 4)) / 2
    1 < ν ∧ (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M *ᵥ v = ν • v) ∧ ∃ w : Fin 2 → ℝ, w ≠ 0 ∧ M *ᵥ w = ν⁻¹ • w := by
  intro ν
  have hd : 0 ≤ M.trace ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (M.trace ^ 2 - 4)
  have hν1 : 1 < ν := by
    show 1 < (M.trace + Real.sqrt (M.trace ^ 2 - 4)) / 2
    linarith
  have hq : ν ^ 2 - M.trace * ν + 1 = 0 := by
    show ((M.trace + Real.sqrt (M.trace ^ 2 - 4)) / 2) ^ 2 -
      M.trace * ((M.trace + Real.sqrt (M.trace ^ 2 - 4)) / 2) + 1 = 0
    nlinarith
  have hν0 : ν ≠ 0 := by linarith
  have hq' : ν⁻¹ ^ 2 - M.trace * ν⁻¹ + 1 = 0 := by
    have : ν⁻¹ ^ 2 - M.trace * ν⁻¹ + 1 = (ν ^ 2 - M.trace * ν + 1) / ν ^ 2 := by
      field_simp
      ring
    rw [this, hq, zero_div]
  exact ⟨hν1, exists_multiplier M hdet hq, exists_multiplier M hdet hq'⟩

/-- [proved-standard] **The subharmonic below `−2`:** for `τ < −2` and `det M = 1`, `ν = (τ − √(τ² − 4))/2 < −1`
is a multiplier. -/
theorem subharmonic_multiplier (hdet : M.det = 1) (hτ : M.trace < -2) :
    let ν := (M.trace - Real.sqrt (M.trace ^ 2 - 4)) / 2
    ν < -1 ∧ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ M *ᵥ v = ν • v := by
  intro ν
  have hd : 0 ≤ M.trace ^ 2 - 4 := by nlinarith
  have hs := Real.sq_sqrt hd
  have hs0 := Real.sqrt_nonneg (M.trace ^ 2 - 4)
  have hν1 : ν < -1 := by
    show (M.trace - Real.sqrt (M.trace ^ 2 - 4)) / 2 < -1
    linarith
  have hq : ν ^ 2 - M.trace * ν + 1 = 0 := by
    show ((M.trace - Real.sqrt (M.trace ^ 2 - 4)) / 2) ^ 2 -
      M.trace * ((M.trace - Real.sqrt (M.trace ^ 2 - 4)) / 2) + 1 = 0
    nlinarith
  exact ⟨hν1, exists_multiplier M hdet hq⟩

/-- [proved-standard] A state carried to `ν` times itself is carried to `νⁿ` times itself in `n` periods. -/
theorem pow_mulVec_eigen {ν : ℝ} {v : Fin 2 → ℝ} (hMv : M *ᵥ v = ν • v) (n : ℕ) :
    (M ^ n) *ᵥ v = (ν ^ n) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

/-- [proved-derived] **The subharmonic flips each period and grows:** for a multiplier `ν < −1`, after `n` periods
the state is `νⁿ v`, of sign `(−1)ⁿ` and modulus `|ν|ⁿ > 1` for `n ≥ 1`: the period doubles. -/
theorem subharmonic_flips_and_grows {ν : ℝ} (hν : ν < -1) {v : Fin 2 → ℝ} (hMv : M *ᵥ v = ν • v) (n : ℕ) :
    (M ^ n) *ᵥ v = ((-1) ^ n * |ν| ^ n) • v ∧ (1 ≤ n → 1 < |ν| ^ n) := by
  refine ⟨?_, fun hn => ?_⟩
  · rw [pow_mulVec_eigen M hMv, abs_of_neg (by linarith), ← mul_pow]
    congr 1
    ring
  · have h1 : 1 < |ν| := by rw [abs_of_neg (by linarith)]; linarith
    exact one_lt_pow₀ h1 (by omega)

/-- [proved-standard] **The shear at the tongue's edge, `τ = 2`:** `(M − 1)² = 0`. -/
theorem edge_shear_plus (hdet : M.det = 1) (hτ : M.trace = 2) :
    (M - 1) * (M - 1) = 0 := by
  have h := sq_eq_trace_sub M
  rw [hdet, hτ] at h
  have : (M - 1) * (M - 1) = M * M - (2 : ℝ) • M + 1 := by
    rw [two_smul]; noncomm_ring
  rw [this, h, one_smul]
  abel

/-- [proved-standard] **The shear at the edge below, `τ = −2`:** `(M + 1)² = 0`. -/
theorem edge_shear_minus (hdet : M.det = 1) (hτ : M.trace = -2) :
    (M + 1) * (M + 1) = 0 := by
  have h := sq_eq_trace_sub M
  rw [hdet, hτ] at h
  have : (M + 1) * (M + 1) = M * M + (2 : ℝ) • M + 1 := by
    rw [two_smul]; noncomm_ring
  rw [this, h, one_smul, neg_smul, two_smul]
  abel

/-- [proved-derived] **The pumped tick selects the two sheets:** in a tongue, with `M v = ν v`, `M w = ν⁻¹ w` and
`ν > 1`, a state `x = α v + β w` read at the growth's clock tends to `α v`, so the sheet `+v` attracts the
half-plane `α > 0` and `−v` the half-plane `α < 0`, the squeezed axis `ℝ w` between them. -/
theorem sheet_selected {ν : ℝ} (hν : 1 < ν) {v w : Fin 2 → ℝ} (hv : M *ᵥ v = ν • v) (hw : M *ᵥ w = ν⁻¹ • w)
    (α β : ℝ) :
    Tendsto (fun n : ℕ => (ν ^ n)⁻¹ • ((M ^ n) *ᵥ (α • v + β • w))) atTop (𝓝 (α • v)) := by
  have hν0 : ν ≠ 0 := by linarith
  have hform : ∀ n : ℕ, (ν ^ n)⁻¹ • ((M ^ n) *ᵥ (α • v + β • w)) = α • v + ((ν⁻¹ ^ 2) ^ n * β) • w := by
    intro n
    have hpn : ν ^ n ≠ 0 := pow_ne_zero n hν0
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, pow_mulVec_eigen M hv,
      pow_mulVec_eigen M hw]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← pow_mul, inv_pow, inv_pow]
    field_simp
    ring
  simp_rw [hform]
  have hr : ν⁻¹ ^ 2 < 1 := by
    have h1 : 0 < ν⁻¹ := inv_pos.mpr (by linarith)
    have h2 : ν⁻¹ < 1 := inv_lt_one_of_one_lt₀ hν
    nlinarith
  have hr0 : 0 ≤ ν⁻¹ ^ 2 := sq_nonneg _
  have hlim : Tendsto (fun n : ℕ => (ν⁻¹ ^ 2) ^ n * β) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).mul_const β
  have := (hlim.smul_const w).const_add (α • v)
  simpa using this

end Holonics.HNN.HillFloquetKinds

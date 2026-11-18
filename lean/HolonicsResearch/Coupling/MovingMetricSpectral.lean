import Mathlib
import Holonics.Foundation.CausalChord

/-!
# The moving metric's spectral reading

A positive form that the motion keeps exists if and only if the generator is semisimple with its
modes on the locus.

[tree] `Holonics/Foundation/CausalChord` holds the rate form `Σ_G = Aᴴ G + G A` (`rateForm`), the
implication "`G ≻ 0` and `Σ_G = 0` put every mode on the imaginary axis"
(`gSkew_eigenvalue_re_eq_zero`), its corollary on the seam (`seam_eigenvalue_re_eq_half`), the
certificate of a diagonalized generator (`semisimple_imaginary_has_conserving_receiver`) and the
Jordan block that has no conserving receiver (`jordan_has_no_conserving_receiver`). Its header
names one direction as not formalized: a generator that is `G`-skew for some positive definite `G`
is semisimple, "the spectral theorem for skew-adjoint operators transported through `G^{1/2}`".
This file proves that direction and closes the biconditionals. It is the box of #410 "the moving
metric's spectral reading: the implication needing `G ≻ 0` and its converse needing
semisimplicity".

## What is proved

Every statement is over `Matrix (Fin n) (Fin n) ℂ`, with a chart a unit `S` and modes a diagonal
`d`, the shapes of `CausalChord`, so the statements compose with the tree's.

1. [proved-derived; formal-checked] **A positive definite form is a Gram form**
   (`exists_unit_conjTranspose_mul_self`): `G = Cᴴ C` with `C` invertible, read from `G`'s own
   spectral theorem as `C = √Λ · Uᴴ`.
2. [proved-derived; formal-checked] **The self-adjoint side** (`diagonalizable_of_gSelfAdjoint`,
   `gSelfAdjoint_of_chart`, `gSelfAdjoint_iff_real_chart`): a positive definite `G` with
   `Aᴴ G = G A` exists if and only if `A = S D S⁻¹` with every mode real. A boost's generator.
3. [proved-derived; formal-checked] **The skew side, the direction the tree named**
   (`diagonalizable_of_gSkew`, `gSkew_iff_imaginary_chart`): a positive definite `G` with
   `rateForm A G = 0` exists if and only if `A = S D S⁻¹` with every mode purely imaginary.
4. [proved-derived; formal-checked] **The seam, the half in generator form**
   (`seam_iff_half_chart`): a positive definite `G` with `Lᴴ G + G L = G` exists if and only if
   `L = S D S⁻¹` with every mode on the line `Re = 1/2`.
5. [proved-derived; formal-checked] **No Jordan block** (`no_jordan_block_of_chart`,
   `no_jordan_block_of_gSkew`): under item 3's hypotheses `(A − μ)² v = 0` gives `(A − μ) v = 0`;
   and the tree's counterexample read through item 3 (`jordanI_has_no_imaginary_chart`): the
   Jordan block has no chart with imaginary modes.
6. [proved-derived; formal-checked] **The group form** (`exists_cayley_unit`,
   `diagonalizable_of_gUnitary`, `diagonalizable_of_similitude`, `similitude_of_chart`,
   `similitude_iff_circle_chart`): for `q > 0`, a positive definite `G` with `Bᴴ G B = q G`
   exists if and only if `B = S D S⁻¹` with every mode at `|d i|² = q`. This is the row
   `key.scaled-form-places-modes` with the form's existence made equivalent to semisimplicity
   and the locus; `HolonicsResearch/Coupling/KreinForm` holds the forward readings on one mode
   (`normSq_eigenvalue_of_posDef`, `no_jordan_block_of_similitude`) and the certificate in its own
   shape (`certificate_of_diagonalizable`).
7. [proved-derived; formal-checked] **A real generator has a real receiver**
   (`posDef_map_ofReal`, `posDef_map_re`, `real_gSkew_iff_imaginary_chart`): for a real `A`, a real
   symmetric positive definite `G` with `Aᵀ G + G A = 0` exists if and only if `A`, read over `ℂ`,
   has a chart with purely imaginary modes. The real part of a complex receiver is a receiver.

## How

[from training] The spectral theorem for a Hermitian matrix (here Mathlib's
`Matrix.IsHermitian.spectral_theorem`), Lyapunov's criterion for a conserved quadratic form, and
Cayley's transform between a unitary and a Hermitian operator. The joins are `agent-inferred`.

- With `G = Cᴴ C`, the relation `Aᴴ G = G A` says `C A C⁻¹` is Hermitian, so it has a unitary chart
  with real modes, and `A` has the chart `C⁻¹ V`.
- If `rateForm A G = 0` then `i·A` is `G`-self-adjoint, and the modes of `A` are `−i` times real
  numbers. The seam is the same statement about `L − 1/2` (`seam_iff_gSkew`).
- If `Wᴴ G W = G`, take a real `t` with `P = (t − i) − (t + i) W` invertible: the spectrum is
  finite and `t ↦ (t − i)/(t + i)` is injective, so all but finitely many `t` serve. Then
  `H = i · ((t − i) + (t + i) W) · P⁻¹` is `G`-self-adjoint, because
  `Pᴴ G Q = −Qᴴ G P` for `Q = (t − i) + (t + i) W`. In `H`'s chart, `W` has the modes
  `(t − i)(h − i) / ((t + i)(h + i))`, of modulus one. A move with `Bᴴ G B = q G` is `√q · W`.
- For a real `A`, the complexified real form is positive definite because
  `x* G x = uᵀGu + vᵀGv` at `x = u + i v`, and the real part of a complex receiver satisfies the
  same linear equation because `A` is real.

## On the objects

[interpretation] `G` is a receiver's metric: the quadratic reading `x* G x` of a state at that
receiver. `rateForm A G = 0` says the reading is conserved along the flow of `A`: against this
receiver the motion is a turn in every plane and nothing boosts (the Swing's split of a rate into
a skew turn and a self-adjoint boost). The theorems say when such a receiver exists: if and only if
the motion is semisimple with its modes on the axis. A mode off the axis, or a Jordan block on it,
is a motion that no positive receiver reads as conserved. The self-adjoint side is the receiver
against which the motion is all boost; the seam is the half; the group form is one tick of a move
that scales the receiver's reading by `q`, with its modes on the circle `|α|² = q`.

## What this does not state

Finite dimension only. Nothing here reaches an unbounded generator, where a positive form needs
its domain and a spectral measure takes the place of a diagonal chart. Nothing says which `G` a
receiver holds or how one is located from readings: the chart `S` comes from the spectral theorem
and is not computed. The moving term `Ġ` of the moving metric's law is not carried; every
statement fixes `G`, as `CausalChord`'s do. No statement is made about the zeros of a zeta
function: for an unending family the object to construct is the positive form itself.
-/

noncomputable section

namespace Holonics.Coupling.MovingMetricSpectral

open Matrix
open scoped ComplexOrder
open Holonics.Foundation.CausalChord (rateForm)

variable {n : ℕ}

/-! ## The calculus of a diagonalizing chart -/

section Chart

variable (S : (Matrix (Fin n) (Fin n) ℂ)ˣ)

/-- [proved-derived; formal-checked] In one chart, modes multiply place by place. -/
theorem chart_mul (d e : Fin n → ℂ) :
    (S.val * diagonal d * S.inv) * (S.val * diagonal e * S.inv)
      = S.val * diagonal (fun i => d i * e i) * S.inv := by
  have h : diagonal (fun i => d i * e i) = diagonal d * diagonal e :=
    (diagonal_mul_diagonal d e).symm
  have hR : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.inv * (S.val * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, S.inv_val, Matrix.one_mul]
  rw [h]
  simp only [Matrix.mul_assoc, hR]

/-- [proved-derived; formal-checked] In any chart, the modes `1` are the identity. -/
theorem chart_one : S.val * diagonal (fun _ => (1 : ℂ)) * S.inv = 1 := by
  rw [diagonal_one, Matrix.mul_one, S.val_inv]

/-- [proved-derived; formal-checked] In one chart, a scalar multiplies every mode. -/
theorem chart_smul (c : ℂ) (d : Fin n → ℂ) :
    c • (S.val * diagonal d * S.inv) = S.val * diagonal (fun i => c * d i) * S.inv := by
  have h : diagonal (fun i => c * d i) = c • diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [h, Matrix.mul_smul, Matrix.smul_mul]

/-- [proved-derived; formal-checked] In one chart, modes add place by place. -/
theorem chart_add (d e : Fin n → ℂ) :
    S.val * diagonal d * S.inv + S.val * diagonal e * S.inv
      = S.val * diagonal (fun i => d i + e i) * S.inv := by
  rw [← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]

/-- [proved-derived; formal-checked] Adding `c • 1` shifts every mode by `c`. -/
theorem chart_add_smul_one (d : Fin n → ℂ) (c : ℂ) :
    S.val * diagonal d * S.inv + c • (1 : Matrix (Fin n) (Fin n) ℂ)
      = S.val * diagonal (fun i => d i + c) * S.inv := by
  have h1 : c • (1 : Matrix (Fin n) (Fin n) ℂ) = S.val * diagonal (fun _ => c) * S.inv := by
    have h2 := chart_smul S c (fun _ => (1 : ℂ))
    rw [chart_one] at h2
    simpa using h2
  rw [h1, chart_add]

/-- [proved-derived; formal-checked] The chart's own form `S⁻ᴴ S⁻¹` is positive definite: the Gram
form of an injective map. -/
theorem cert_posDef : (S.invᴴ * S.inv).PosDef := by
  have hinj : Function.Injective S.inv.mulVec := by
    intro x y hxy
    have h := congrArg (fun w => S.val *ᵥ w) hxy
    simpa [Matrix.mulVec_mulVec, S.val_inv] using h
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

/-- [proved-derived; formal-checked] Against the chart's own form, the adjoint of one diagonalized
matrix times another is diagonal in the form's frame:
`(S D S⁻¹)ᴴ (S⁻ᴴ S⁻¹) (S E S⁻¹) = S⁻ᴴ (D̄ E) S⁻¹`. -/
theorem chart_conjTranspose_mul_cert_mul (d e : Fin n → ℂ) :
    (S.val * diagonal d * S.inv)ᴴ * (S.invᴴ * S.inv) * (S.val * diagonal e * S.inv)
      = S.invᴴ * diagonal (fun i => star (d i) * e i) * S.inv := by
  have hL : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.valᴴ * (S.invᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, S.inv_val, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hR : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.inv * (S.val * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, S.inv_val, Matrix.one_mul]
  have hd : diagonal (fun i => star (d i) * e i) = (diagonal d)ᴴ * diagonal e := by
    rw [diagonal_conjTranspose, diagonal_mul_diagonal]
    rfl
  rw [hd]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hL, hR]

/-- [proved-derived; formal-checked] `(S D S⁻¹)ᴴ (S⁻ᴴ S⁻¹) = S⁻ᴴ D̄ S⁻¹`. -/
theorem chart_conjTranspose_mul_cert (d : Fin n → ℂ) :
    (S.val * diagonal d * S.inv)ᴴ * (S.invᴴ * S.inv)
      = S.invᴴ * diagonal (fun i => star (d i)) * S.inv := by
  have hL : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.valᴴ * (S.invᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, S.inv_val, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hd : diagonal (fun i => star (d i)) = (diagonal d)ᴴ := by
    rw [diagonal_conjTranspose]
    rfl
  rw [hd]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc, hL]

/-- [proved-derived; formal-checked] `(S⁻ᴴ S⁻¹)(S E S⁻¹) = S⁻ᴴ E S⁻¹`. -/
theorem cert_mul_chart (e : Fin n → ℂ) :
    (S.invᴴ * S.inv) * (S.val * diagonal e * S.inv) = S.invᴴ * diagonal e * S.inv := by
  have hR : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.inv * (S.val * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, S.inv_val, Matrix.one_mul]
  simp only [Matrix.mul_assoc, hR]

end Chart

/-! ## A positive definite form is a Gram form -/

/-- [proved-derived; formal-checked] **A positive definite form is a Gram form.** `G = Cᴴ C` with
`C` invertible. From `G = U Λ Uᴴ` with `Λ` positive, take `C = √Λ · Uᴴ`, whose inverse is
`U · √Λ⁻¹`. This is the `G^{1/2}` that `CausalChord`'s header asks for, up to a unitary. -/
theorem exists_unit_conjTranspose_mul_self {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    ∃ C : (Matrix (Fin n) (Fin n) ℂ)ˣ, G = C.valᴴ * C.val := by
  have hH : G.IsHermitian := hG.isHermitian
  let U : Matrix (Fin n) (Fin n) ℂ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hUU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUU' : U * Uᴴ = 1 := Unitary.coe_mul_star_self hH.eigenvectorUnitary
  let r : Fin n → ℂ := fun i => ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ)
  have hr0 : ∀ i, r i ≠ 0 := fun i =>
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hG.eigenvalues_pos i)).ne'
  have hrr : (fun i => r i * r i) = fun i => ((hH.eigenvalues i : ℝ) : ℂ) := by
    funext i
    show ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ) * ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hG.eigenvalues_pos i).le]
  have hstar_r : star r = r := by
    funext i
    show star ((Real.sqrt (hH.eigenvalues i) : ℝ) : ℂ) = _
    rw [Complex.star_def, Complex.conj_ofReal]
  have hspec : G = U * diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hCC : diagonal r * Uᴴ * (U * diagonal (fun i => (r i)⁻¹)) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hUU, Matrix.one_mul, diagonal_mul_diagonal]
    have : (fun i => r i * (r i)⁻¹) = fun _ => (1 : ℂ) := by
      funext i
      exact mul_inv_cancel₀ (hr0 i)
    rw [this, diagonal_one]
  have hCC' : U * diagonal (fun i => (r i)⁻¹) * (diagonal r * Uᴴ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diagonal_mul_diagonal]
    have : (fun i => (r i)⁻¹ * r i) = fun _ => (1 : ℂ) := by
      funext i
      exact inv_mul_cancel₀ (hr0 i)
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨⟨diagonal r * Uᴴ, U * diagonal (fun i => (r i)⁻¹), hCC, hCC'⟩, ?_⟩
  show G = (diagonal r * Uᴴ)ᴴ * (diagonal r * Uᴴ)
  rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose, hstar_r,
    Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal r), diagonal_mul_diagonal, hrr]
  exact hspec.trans (Matrix.mul_assoc _ _ _)

/-! ## The self-adjoint side -/

/-- [proved-derived; formal-checked] **A `G`-self-adjoint generator is semisimple with real modes.**
With `G = Cᴴ C`, `Aᴴ G = G A` says `C A C⁻¹` is Hermitian; its unitary chart `V` gives `A` the chart
`C⁻¹ V`. No hypothesis beyond `G ≻ 0`. -/
theorem diagonalizable_of_gSelfAdjoint {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : Aᴴ * G = G * A) :
    ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
      (∀ i, (d i).im = 0) ∧ A = S.val * diagonal d * S.inv := by
  obtain ⟨C, hC⟩ := exists_unit_conjTranspose_mul_self hG
  have hCinvH : C.invᴴ * C.valᴴ = 1 := by
    rw [← conjTranspose_mul, C.val_inv, conjTranspose_one]
  have h1 : Aᴴ * C.valᴴ * C.val = C.valᴴ * C.val * A := by
    rw [Matrix.mul_assoc, ← hC, hA]
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℂ, N = C.val * A * C.inv := ⟨_, rfl⟩
  have hNH : N.IsHermitian := by
    show Nᴴ = N
    rw [hN, conjTranspose_mul, conjTranspose_mul]
    calc C.invᴴ * (Aᴴ * C.valᴴ)
        = C.invᴴ * (Aᴴ * C.valᴴ) * (C.val * C.inv) := by rw [C.val_inv, Matrix.mul_one]
      _ = C.invᴴ * (Aᴴ * C.valᴴ * C.val) * C.inv := by simp only [Matrix.mul_assoc]
      _ = C.invᴴ * (C.valᴴ * C.val * A) * C.inv := by rw [h1]
      _ = (C.invᴴ * C.valᴴ) * (C.val * A * C.inv) := by simp only [Matrix.mul_assoc]
      _ = C.val * A * C.inv := by rw [hCinvH, Matrix.one_mul]
  let V : Matrix (Fin n) (Fin n) ℂ := (hNH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
  have hVV : Vᴴ * V = 1 := Unitary.coe_star_mul_self hNH.eigenvectorUnitary
  have hVV' : V * Vᴴ = 1 := Unitary.coe_mul_star_self hNH.eigenvectorUnitary
  have hspec : N = V * diagonal (fun i => ((hNH.eigenvalues i : ℝ) : ℂ)) * Vᴴ := by
    have h := hNH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hA' : A = C.inv * N * C.val := by
    rw [hN]
    simp only [Matrix.mul_assoc]
    rw [C.inv_val, Matrix.mul_one, ← Matrix.mul_assoc, C.inv_val, Matrix.one_mul]
  refine ⟨⟨C.inv * V, Vᴴ * C.val, ?_, ?_⟩, fun i => ((hNH.eigenvalues i : ℝ) : ℂ),
    fun i => Complex.ofReal_im _, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hVV', Matrix.one_mul, C.inv_val]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C.val, C.val_inv, Matrix.one_mul, hVV]
  · show A = C.inv * V * diagonal _ * (Vᴴ * C.val)
    refine hA'.trans ?_
    have h2 := congrArg (fun X => C.inv * X * C.val) hspec
    refine h2.trans ?_
    simp only [Matrix.mul_assoc]

/-- [proved-derived; formal-checked] The converse certificate on the self-adjoint side: a chart with
real modes carries the positive form `S⁻ᴴ S⁻¹`, against which the generator is self-adjoint. -/
theorem gSelfAdjoint_of_chart (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ)
    (hd : ∀ i, (d i).im = 0) :
    (S.invᴴ * S.inv).PosDef ∧
      (S.val * diagonal d * S.inv)ᴴ * (S.invᴴ * S.inv)
        = (S.invᴴ * S.inv) * (S.val * diagonal d * S.inv) := by
  refine ⟨cert_posDef S, ?_⟩
  rw [chart_conjTranspose_mul_cert, cert_mul_chart]
  have h : (fun i => star (d i)) = d := by
    funext i
    rw [Complex.star_def]
    exact Complex.conj_eq_iff_im.mpr (hd i)
  rw [h]

/-- [proved-derived; formal-checked] **The self-adjoint side, both ways.** A positive definite `G`
with `Aᴴ G = G A` exists if and only if `A` is semisimple with real modes. -/
theorem gSelfAdjoint_iff_real_chart (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ G : Matrix (Fin n) (Fin n) ℂ, G.PosDef ∧ Aᴴ * G = G * A) ↔
      ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
        (∀ i, (d i).im = 0) ∧ A = S.val * diagonal d * S.inv := by
  constructor
  · rintro ⟨G, hG, hA⟩
    exact diagonalizable_of_gSelfAdjoint hG hA
  · rintro ⟨S, d, hd, rfl⟩
    exact ⟨_, (gSelfAdjoint_of_chart S d hd).1, (gSelfAdjoint_of_chart S d hd).2⟩

/-! ## The skew side: the direction the tree named as dropped -/

/-- [proved-derived; formal-checked] **The direction `CausalChord` named as not formalized.** If
`rateForm A G = 0` for a positive definite `G`, then `A` is semisimple with purely imaginary modes:
`i·A` is `G`-self-adjoint, and its real modes times `−i` are the modes of `A`. -/
theorem diagonalizable_of_gSkew {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) :
    ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
      (∀ i, (d i).re = 0) ∧ A = S.val * diagonal d * S.inv := by
  have hA' : Aᴴ * G + G * A = 0 := hA
  have hskew : Aᴴ * G = -(G * A) := eq_neg_of_add_eq_zero_left hA'
  have hIA : (Complex.I • A)ᴴ * G = G * (Complex.I • A) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hskew, Complex.star_def,
      Complex.conj_I, neg_smul, smul_neg, neg_neg]
  obtain ⟨S, d, hd, hS⟩ := diagonalizable_of_gSelfAdjoint hG hIA
  refine ⟨S, fun i => -Complex.I * d i, fun i => ?_, ?_⟩
  · simp [hd i]
  · have h : A = (-Complex.I) • (Complex.I • A) := by
      rw [smul_smul]
      simp
    rw [h, hS, chart_smul]

/-- [proved-derived; formal-checked] **The moving metric's spectral reading (#410).** A conserving
receiver, a positive definite `G` with `rateForm A G = 0`, exists if and only if `A` is semisimple
with purely imaginary modes. The reverse direction is the tree's
`semisimple_imaginary_has_conserving_receiver`. -/
theorem gSkew_iff_imaginary_chart (A : Matrix (Fin n) (Fin n) ℂ) :
    (∃ G : Matrix (Fin n) (Fin n) ℂ, G.PosDef ∧ rateForm A G = 0) ↔
      ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
        (∀ i, (d i).re = 0) ∧ A = S.val * diagonal d * S.inv := by
  constructor
  · rintro ⟨G, hG, hA⟩
    exact diagonalizable_of_gSkew hG hA
  · rintro ⟨S, d, hd, rfl⟩
    exact ⟨_, Holonics.Foundation.CausalChord.semisimple_imaginary_has_conserving_receiver S d hd⟩

/-! ## The seam: the half in generator form -/

/-- [proved-derived; formal-checked] The real part of `2⁻¹` is one half. -/
theorem two_inv_re : ((2 : ℂ)⁻¹).re = 1 / 2 := by
  rw [show ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]

/-- [proved-derived; formal-checked] **The half in generator form.** A positive definite `G` with
`Lᴴ G + G L = G` exists if and only if `L` is semisimple with every mode on the line `Re = 1/2`.
Through `seam_iff_gSkew` it is the skew side for `L − 1/2`. -/
theorem seam_iff_half_chart (L : Matrix (Fin n) (Fin n) ℂ) :
    (∃ G : Matrix (Fin n) (Fin n) ℂ, G.PosDef ∧ Lᴴ * G + G * L = G) ↔
      ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
        (∀ i, (d i).re = 1 / 2) ∧ L = S.val * diagonal d * S.inv := by
  constructor
  · rintro ⟨G, hG, hL⟩
    have hA := (Holonics.Foundation.CausalChord.seam_iff_gSkew L G).mpr hL
    obtain ⟨S, d, hd, hS⟩ := diagonalizable_of_gSkew hG hA
    refine ⟨S, fun i => d i + 2⁻¹, fun i => ?_, ?_⟩
    · rw [Complex.add_re, hd i, two_inv_re, zero_add]
    · have h := chart_add_smul_one S d (2⁻¹ : ℂ)
      rw [← h, ← hS, sub_add_cancel]
  · rintro ⟨S, d, hd, rfl⟩
    have hd' : ∀ i, (d i + -(2⁻¹ : ℂ)).re = 0 := by
      intro i
      rw [Complex.add_re, Complex.neg_re, hd i, two_inv_re]
      ring
    obtain ⟨hpos, hrate⟩ :=
      Holonics.Foundation.CausalChord.semisimple_imaginary_has_conserving_receiver S
        (fun i => d i + -(2⁻¹ : ℂ)) hd'
    refine ⟨_, hpos, (Holonics.Foundation.CausalChord.seam_iff_gSkew _ _).mp ?_⟩
    have h := chart_add_smul_one S d (-(2⁻¹ : ℂ))
    rw [← h, neg_smul, ← sub_eq_add_neg] at hrate
    exact hrate

/-! ## No Jordan block -/

/-- [proved-derived; formal-checked] A matrix with a diagonalizing chart has no Jordan block:
`(A − μ)² v = 0` gives `(A − μ) v = 0`, because in the chart a squared mode vanishes only where the
mode does. -/
theorem no_jordan_block_of_chart (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ) (μ : ℂ)
    (v : Fin n → ℂ)
    (h : (S.val * diagonal d * S.inv - μ • 1) *ᵥ
      ((S.val * diagonal d * S.inv - μ • 1) *ᵥ v) = 0) :
    (S.val * diagonal d * S.inv - μ • 1) *ᵥ v = 0 := by
  have hM : S.val * diagonal d * S.inv - μ • (1 : Matrix (Fin n) (Fin n) ℂ)
      = S.val * diagonal (fun i => d i + -μ) * S.inv := by
    have h0 := chart_add_smul_one S d (-μ)
    rw [← h0, neg_smul, sub_eq_add_neg]
  rw [hM] at h ⊢
  rw [Matrix.mulVec_mulVec, chart_mul] at h
  have e : ∀ f : Fin n → ℂ, S.inv * (S.val * diagonal f * S.inv) = diagonal f * S.inv := by
    intro f
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, S.inv_val, Matrix.one_mul]
  have h2 : diagonal (fun i => (d i + -μ) * (d i + -μ)) *ᵥ (S.inv *ᵥ v) = 0 := by
    have h3 := congrArg (fun x => S.inv *ᵥ x) h
    simp only [Matrix.mulVec_mulVec, e, Matrix.mulVec_zero] at h3
    rw [Matrix.mulVec_mulVec]
    exact h3
  have h4 : diagonal (fun i => d i + -μ) *ᵥ (S.inv *ᵥ v) = 0 := by
    funext i
    have h5 := congrFun h2 i
    rw [Matrix.mulVec_diagonal] at h5 ⊢
    simp only [Pi.zero_apply] at h5 ⊢
    rcases mul_eq_zero.mp h5 with h6 | h6
    · rw [mul_self_eq_zero.mp h6, zero_mul]
    · rw [h6, mul_zero]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]

/-- [proved-derived; formal-checked] **A conserving receiver leaves no Jordan block.** Under
`G ≻ 0` and `rateForm A G = 0`, `(A − μ)² v = 0` gives `(A − μ) v = 0` for every `μ`. -/
theorem no_jordan_block_of_gSkew {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) (μ : ℂ) (v : Fin n → ℂ)
    (h : (A - μ • 1) *ᵥ ((A - μ • 1) *ᵥ v) = 0) : (A - μ • 1) *ᵥ v = 0 := by
  obtain ⟨S, d, -, rfl⟩ := diagonalizable_of_gSkew hG hA
  exact no_jordan_block_of_chart S d μ v h

/-- [proved-derived; formal-checked] The tree's counterexample read through the biconditional: the
Jordan block `jordanI`, whose only mode is `i`, has no chart with purely imaginary modes, because
it has no conserving receiver (`jordan_has_no_conserving_receiver`). -/
theorem jordanI_has_no_imaginary_chart :
    ¬ ∃ (S : (Matrix (Fin 2) (Fin 2) ℂ)ˣ) (d : Fin 2 → ℂ),
      (∀ i, (d i).re = 0) ∧
        Holonics.Foundation.CausalChord.jordanI = S.val * diagonal d * S.inv :=
  fun h => Holonics.Foundation.CausalChord.jordan_has_no_conserving_receiver
    ((gSkew_iff_imaginary_chart _).mpr h)

/-! ## The group form: a move that scales a positive form -/

/-- [proved-derived; formal-checked] `t + i` is never zero for real `t`. -/
theorem ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro h
  have h2 := congrArg Complex.im h
  simp at h2

/-- [proved-derived; formal-checked] Cayley's map `t ↦ (t − i)/(t + i)` of the real line into the
unit circle is injective. -/
theorem cayley_point_injective :
    Function.Injective (fun t : ℝ => ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)) := by
  intro t s h
  have ht := ofReal_add_I_ne_zero t
  have hs := ofReal_add_I_ne_zero s
  simp only at h
  rw [div_eq_div_iff ht hs] at h
  have h2 : ((t : ℂ) - (s : ℂ)) * (2 * Complex.I) = 0 := by linear_combination h
  have h3 : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have h4 : (t : ℂ) - (s : ℂ) = 0 := (mul_eq_zero.mp h2).resolve_right h3
  exact Complex.ofReal_injective (sub_eq_zero.mp h4)

/-- [proved-derived; formal-checked] For any matrix `W` some real `t` makes `(t − i) − (t + i) W`
invertible: the spectrum of `W` is finite and Cayley's map takes infinitely many values. -/
theorem exists_cayley_unit (W : Matrix (Fin n) (Fin n) ℂ) :
    ∃ t : ℝ, IsUnit (((t : ℂ) - Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ)
      - ((t : ℂ) + Complex.I) • W) := by
  have hinf : (Set.range fun t : ℝ => ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)).Infinite :=
    Set.infinite_range_of_injective cayley_point_injective
  obtain ⟨ζ, ⟨t, rfl⟩, hζ⟩ := hinf.exists_notMem_finite (Matrix.finite_spectrum W)
  refine ⟨t, ?_⟩
  have hb := ofReal_add_I_ne_zero t
  rw [spectrum.mem_iff, not_not] at hζ
  have key : ((t : ℂ) - Complex.I) • (1 : Matrix (Fin n) (Fin n) ℂ) - ((t : ℂ) + Complex.I) • W
      = ((t : ℂ) + Complex.I) •
        (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)
          (((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)) - W) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, mul_div_cancel₀ _ hb]
  rw [key]
  have h := hζ.smul (Units.mk0 _ hb)
  simpa [Units.smul_def] using h

/-- [proved-derived; formal-checked] **A move that keeps a positive form is semisimple with modes on
the unit circle.** If `Wᴴ G W = G` with `G ≻ 0`, then `W = S D S⁻¹` with every `|d i|² = 1`.
Cayley's transform `H = i (a + b W)(a − b W)⁻¹`, `a = t − i`, `b = t + i`, is `G`-self-adjoint, and
in its chart `W` has the modes `a (h − i) / (b (h + i))`. -/
theorem diagonalizable_of_gUnitary {W G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hW : Wᴴ * G * W = G) :
    ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
      (∀ i, Complex.normSq (d i) = 1) ∧ W = S.val * diagonal d * S.inv := by
  obtain ⟨t, ht⟩ := exists_cayley_unit W
  obtain ⟨Pu, hPu⟩ := ht
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = (t : ℂ) - Complex.I := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℂ, b = (t : ℂ) + Complex.I := ⟨_, rfl⟩
  rw [← ha, ← hb] at hPu
  have hab : star a = b := by
    rw [ha, hb, Complex.star_def]
    apply Complex.ext <;> simp
  have hba : star b = a := by
    rw [ha, hb, Complex.star_def]
    apply Complex.ext <;> simp
  have hb0 : b ≠ 0 := hb ▸ ofReal_add_I_ne_zero t
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) ℂ, P = a • 1 - b • W := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q = a • 1 + b • W := ⟨_, rfl⟩
  rw [← hP] at hPu
  have hPH : Pᴴ = b • 1 - a • Wᴴ := by
    rw [hP, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hab, hba]
  have hQH : Qᴴ = b • 1 + a • Wᴴ := by
    rw [hQ, conjTranspose_add, conjTranspose_smul, conjTranspose_smul, conjTranspose_one, hab, hba]
  have hW' : Wᴴ * (G * W) = G := by
    rw [← Matrix.mul_assoc]
    exact hW
  have e1 : Pᴴ * G * Q = (b * b) • (G * W) - (a * a) • (Wᴴ * G) := by
    rw [hPH, hQ]
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hW']
    module
  have e2 : Qᴴ * G * P = (a * a) • (Wᴴ * G) - (b * b) • (G * W) := by
    rw [hQH, hP]
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc, hW']
    module
  have e3 : Pᴴ * G * Q = -(Qᴴ * G * P) := by
    rw [e1, e2, neg_sub]
  have hPP : P * Pu.inv = 1 := by
    rw [← hPu]
    exact Pu.val_inv
  have hPP' : Pu.inv * P = 1 := by
    rw [← hPu]
    exact Pu.inv_val
  have hPHinv : Pu.invᴴ * Pᴴ = 1 := by
    rw [← conjTranspose_mul, hPP, conjTranspose_one]
  have e4 : G * Q * Pu.inv = -(Pu.invᴴ * Qᴴ * G) := by
    calc G * Q * Pu.inv = (Pu.invᴴ * Pᴴ) * (G * Q * Pu.inv) := by rw [hPHinv, Matrix.one_mul]
      _ = Pu.invᴴ * (Pᴴ * G * Q) * Pu.inv := by simp only [Matrix.mul_assoc]
      _ = Pu.invᴴ * (-(Qᴴ * G * P)) * Pu.inv := by rw [e3]
      _ = -(Pu.invᴴ * Qᴴ * G * (P * Pu.inv)) := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(Pu.invᴴ * Qᴴ * G) := by rw [hPP, Matrix.mul_one]
  obtain ⟨H, hH⟩ : ∃ H : Matrix (Fin n) (Fin n) ℂ, H = Complex.I • (Q * Pu.inv) := ⟨_, rfl⟩
  have hHG : Hᴴ * G = G * H := by
    rw [hH, conjTranspose_smul, conjTranspose_mul, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_assoc G, e4, Complex.star_def, Complex.conj_I, neg_smul, smul_neg]
  obtain ⟨S, d, hd, hS⟩ := diagonalizable_of_gSelfAdjoint hG hHG
  have hHP : H * P = Complex.I • Q := by
    rw [hH, Matrix.smul_mul, Matrix.mul_assoc, hPP', Matrix.mul_one]
  have hMW : (b • (H + Complex.I • 1)) * W = a • (H + (-Complex.I) • 1) := by
    have h := hHP
    rw [hP, hQ] at h
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, smul_add, smul_smul] at h
    have h2 : b • (H * W) = a • H - ((Complex.I * a) • (1 : Matrix (Fin n) (Fin n) ℂ)
        + (Complex.I * b) • W) := by
      rw [← h]
      abel
    simp only [Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, smul_add, smul_smul, h2]
    module
  have hM : b • (H + Complex.I • 1)
      = S.val * diagonal (fun i => b * (d i + Complex.I)) * S.inv := by
    rw [hS, chart_add_smul_one, chart_smul]
  have hR : a • (H + (-Complex.I) • 1)
      = S.val * diagonal (fun i => a * (d i + -Complex.I)) * S.inv := by
    rw [hS, chart_add_smul_one, chart_smul]
  have hden : ∀ i, b * (d i + Complex.I) ≠ 0 := by
    intro i
    refine mul_ne_zero hb0 ?_
    intro h
    have h2 := congrArg Complex.im h
    simp [hd i] at h2
  have hMinv : (S.val * diagonal (fun i => (b * (d i + Complex.I))⁻¹) * S.inv)
      * (b • (H + Complex.I • 1)) = 1 := by
    rw [hM, chart_mul]
    have h : (fun i => (b * (d i + Complex.I))⁻¹ * (b * (d i + Complex.I))) = fun _ => (1 : ℂ) := by
      funext i
      exact inv_mul_cancel₀ (hden i)
    rw [h, chart_one]
  have hWchart : W = S.val
      * diagonal (fun i => (b * (d i + Complex.I))⁻¹ * (a * (d i + -Complex.I))) * S.inv := by
    calc W = (S.val * diagonal (fun i => (b * (d i + Complex.I))⁻¹) * S.inv)
          * ((b • (H + Complex.I • 1)) * W) := by
          rw [← Matrix.mul_assoc, hMinv, Matrix.one_mul]
      _ = _ := by rw [hMW, hR, chart_mul]
  refine ⟨S, _, fun i => ?_, hWchart⟩
  have hna : Complex.normSq a = t ^ 2 + 1 := by
    rw [ha, Complex.normSq_apply]
    simp
    ring
  have hnb : Complex.normSq b = t ^ 2 + 1 := by
    rw [hb, Complex.normSq_apply]
    simp
    ring
  have hnp : Complex.normSq (d i + Complex.I) = (d i).re ^ 2 + 1 := by
    rw [Complex.normSq_apply]
    simp [hd i]
    ring
  have hnm : Complex.normSq (d i + -Complex.I) = (d i).re ^ 2 + 1 := by
    rw [Complex.normSq_apply]
    simp [hd i]
    ring
  rw [map_mul, map_inv₀, map_mul, map_mul, hna, hnb, hnp, hnm]
  have h1 : (t ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  have h2 : ((d i).re ^ 2 + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- [proved-derived; formal-checked] **A move that scales a positive form by `q > 0` is semisimple
with its modes at `|α|² = q`.** `B / √q` keeps the form. -/
theorem diagonalizable_of_similitude {B G : Matrix (Fin n) (Fin n) ℂ} {q : ℝ} (hq : 0 < q)
    (hG : G.PosDef) (hB : Bᴴ * G * B = (q : ℂ) • G) :
    ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
      (∀ i, Complex.normSq (d i) = q) ∧ B = S.val * diagonal d * S.inv := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt q := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.mpr hq
  have hss : s * s = q := hs ▸ Real.mul_self_sqrt hq.le
  have hsc : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
  have hW : (((s : ℂ)⁻¹) • B)ᴴ * G * (((s : ℂ)⁻¹) • B) = G := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB,
      smul_smul]
    have h : star ((s : ℂ)⁻¹) * (s : ℂ)⁻¹ * (q : ℂ) = 1 := by
      rw [← hss, Complex.star_def, map_inv₀, Complex.conj_ofReal, Complex.ofReal_mul]
      field_simp
    rw [h, one_smul]
  obtain ⟨S, d, hd, hS⟩ := diagonalizable_of_gUnitary hG hW
  refine ⟨S, fun i => (s : ℂ) * d i, fun i => ?_, ?_⟩
  · rw [map_mul, hd i, mul_one, Complex.normSq_ofReal, hss]
  · rw [← chart_smul, ← hS, smul_smul, mul_inv_cancel₀ hsc, one_smul]

/-- [proved-derived; formal-checked] The converse certificate in the tree's shapes: a chart with
every `|d i|² = q` carries the positive form `S⁻ᴴ S⁻¹`, which the move scales by `q`. -/
theorem similitude_of_chart (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ) (q : ℝ)
    (hd : ∀ i, Complex.normSq (d i) = q) :
    (S.invᴴ * S.inv).PosDef ∧
      (S.val * diagonal d * S.inv)ᴴ * (S.invᴴ * S.inv) * (S.val * diagonal d * S.inv)
        = (q : ℂ) • (S.invᴴ * S.inv) := by
  refine ⟨cert_posDef S, ?_⟩
  rw [chart_conjTranspose_mul_cert_mul]
  have h : (fun i => star (d i) * d i) = fun _ => (q : ℂ) := by
    funext i
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hd i]
  have h2 : diagonal (fun _ : Fin n => (q : ℂ)) = (q : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [h, h2, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

/-- [proved-derived; formal-checked] **The group form, both ways.** For `q > 0`, a positive definite
`G` with `Bᴴ G B = q G` exists if and only if `B` is semisimple with every mode at `|α|² = q`. -/
theorem similitude_iff_circle_chart {q : ℝ} (hq : 0 < q) (B : Matrix (Fin n) (Fin n) ℂ) :
    (∃ G : Matrix (Fin n) (Fin n) ℂ, G.PosDef ∧ Bᴴ * G * B = (q : ℂ) • G) ↔
      ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
        (∀ i, Complex.normSq (d i) = q) ∧ B = S.val * diagonal d * S.inv := by
  constructor
  · rintro ⟨G, hG, hB⟩
    exact diagonalizable_of_similitude hq hG hB
  · rintro ⟨S, d, hd, rfl⟩
    exact ⟨_, (similitude_of_chart S d q hd).1, (similitude_of_chart S d q hd).2⟩

/-! ## A real generator and a real receiver -/

/-- [proved-derived; formal-checked] A real symmetric positive definite form is positive definite
over `ℂ`: at `x = u + i v`, `x* G x = uᵀGu + vᵀGv`. -/
theorem posDef_map_ofReal {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) :
    (G.map Complex.ofRealHom).PosDef := by
  have hsymm : ∀ i j, G j i = G i j := by
    intro i j
    simpa using hG.isHermitian.apply i j
  have hGt : Gᵀ = G := by
    ext i j
    exact hsymm i j
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    simp only [conjTranspose_apply, map_apply, Complex.ofRealHom_eq_coe, Complex.star_def,
      Complex.conj_ofReal]
    rw [hsymm i j]
  · intro x hx
    obtain ⟨u, hu⟩ : ∃ u : Fin n → ℝ, u = fun i => (x i).re := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v : Fin n → ℝ, v = fun i => (x i).im := ⟨_, rfl⟩
    have hxd : x = (Complex.ofRealHom ∘ u) + Complex.I • (Complex.ofRealHom ∘ v) := by
      funext i
      simp only [hu, hv, Pi.add_apply, Pi.smul_apply, Function.comp_apply,
        Complex.ofRealHom_eq_coe, smul_eq_mul]
      rw [mul_comm]
      exact (Complex.re_add_im (x i)).symm
    have hsx : star x = (Complex.ofRealHom ∘ u) - Complex.I • (Complex.ofRealHom ∘ v) := by
      funext i
      simp only [hu, hv, Pi.star_apply, Pi.sub_apply, Pi.smul_apply, Function.comp_apply,
        Complex.ofRealHom_eq_coe, smul_eq_mul, Complex.star_def]
      apply Complex.ext <;> simp
    have hGu : ∀ w : Fin n → ℝ, G.map Complex.ofRealHom *ᵥ (Complex.ofRealHom ∘ w)
        = Complex.ofRealHom ∘ (G *ᵥ w) := by
      intro w
      funext i
      exact (RingHom.map_mulVec Complex.ofRealHom G w i).symm
    have d1 : ∀ p w : Fin n → ℝ,
        (Complex.ofRealHom ∘ p) ⬝ᵥ (Complex.ofRealHom ∘ w) = ((p ⬝ᵥ w : ℝ) : ℂ) :=
      fun p w => (RingHom.map_dotProduct Complex.ofRealHom p w).symm
    have hsym : u ⬝ᵥ (G *ᵥ v) = v ⬝ᵥ (G *ᵥ u) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hGt, dotProduct_comm]
    have key : star x ⬝ᵥ (G.map Complex.ofRealHom *ᵥ x)
        = ((u ⬝ᵥ (G *ᵥ u) + v ⬝ᵥ (G *ᵥ v) : ℝ) : ℂ) := by
      rw [hsx]
      conv_lhs => rw [hxd]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, sub_dotProduct, dotProduct_add,
        smul_dotProduct, dotProduct_smul, hGu, d1, smul_eq_mul, hsym]
      push_cast
      linear_combination (-((v ⬝ᵥ (G *ᵥ v) : ℝ) : ℂ)) * Complex.I_sq
    rw [key, Complex.zero_lt_real]
    have hu0 : 0 ≤ u ⬝ᵥ (G *ᵥ u) := by
      simpa using hG.posSemidef.dotProduct_mulVec_nonneg u
    have hv0 : 0 ≤ v ⬝ᵥ (G *ᵥ v) := by
      simpa using hG.posSemidef.dotProduct_mulVec_nonneg v
    by_cases hu' : u = 0
    · have hv' : v ≠ 0 := by
        intro hv'
        apply hx
        rw [hxd, hu', hv']
        funext i
        simp
      have h := hG.dotProduct_mulVec_pos hv'
      have h2 : 0 < v ⬝ᵥ (G *ᵥ v) := by simpa using h
      linarith
    · have h := hG.dotProduct_mulVec_pos hu'
      have h2 : 0 < u ⬝ᵥ (G *ᵥ u) := by simpa using h
      linarith

/-- [proved-derived; formal-checked] The entrywise real part of a complex positive definite form is
a real positive definite form: on a real vector the two readings agree. -/
theorem posDef_map_re {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    (G.map Complex.re).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    have h := congrArg Complex.re (hG.isHermitian.apply i j)
    simpa using h
  · intro x hx
    have hxc : (Complex.ofRealHom ∘ x) ≠ 0 := by
      intro h
      apply hx
      funext i
      have h2 := congrFun h i
      simpa using h2
    have hpos := hG.re_dotProduct_pos hxc
    have key : star x ⬝ᵥ (G.map Complex.re *ᵥ x)
        = (star (Complex.ofRealHom ∘ x) ⬝ᵥ (G *ᵥ (Complex.ofRealHom ∘ x))).re := by
      simp only [dotProduct, mulVec, Pi.star_apply, Function.comp_apply,
        Complex.ofRealHom_eq_coe, Matrix.map_apply, star_trivial, Complex.star_def,
        Complex.conj_ofReal, Complex.re_sum, Complex.re_ofReal_mul, Complex.re_mul_ofReal]
    rw [key]
    exact hpos

/-- [proved-derived; formal-checked] **A real generator has a real receiver.** For a real `A`, a
real symmetric positive definite `G` with `Aᵀ G + G A = 0` exists if and only if `A`, read over
`ℂ`, is semisimple with purely imaginary modes (Lyapunov's criterion for a conserved quadratic
form). -/
theorem real_gSkew_iff_imaginary_chart (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ G : Matrix (Fin n) (Fin n) ℝ, G.PosDef ∧ Aᵀ * G + G * A = 0) ↔
      ∃ (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ),
        (∀ i, (d i).re = 0) ∧ A.map Complex.ofRealHom = S.val * diagonal d * S.inv := by
  constructor
  · rintro ⟨G, hG, hAG⟩
    have hrate : rateForm (A.map Complex.ofRealHom) (G.map Complex.ofRealHom) = 0 := by
      show (A.map Complex.ofRealHom)ᴴ * G.map Complex.ofRealHom
        + G.map Complex.ofRealHom * A.map Complex.ofRealHom = 0
      ext i j
      have h := congrArg (fun r : ℝ => (r : ℂ)) (congrFun (congrFun hAG i) j)
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
        Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero] at h
      simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
        Complex.ofRealHom_eq_coe, Complex.star_def, Complex.conj_ofReal, Matrix.zero_apply]
      exact h
    exact diagonalizable_of_gSkew (posDef_map_ofReal hG) hrate
  · intro h
    obtain ⟨G, hG, hrate⟩ := (gSkew_iff_imaginary_chart _).mpr h
    refine ⟨G.map Complex.re, posDef_map_re hG, ?_⟩
    ext i j
    have hrate' : (A.map Complex.ofRealHom)ᴴ * G + G * A.map Complex.ofRealHom = 0 := hrate
    have h2 := congrArg Complex.re (congrFun (congrFun hrate' i) j)
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply,
      Complex.ofRealHom_eq_coe, Complex.star_def, Complex.conj_ofReal, Matrix.zero_apply,
      Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.re_mul_ofReal,
      Complex.zero_re] at h2
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.zero_apply]
    exact h2

/-! ## Audit -/

section Audit

#print axioms exists_unit_conjTranspose_mul_self
#print axioms diagonalizable_of_gSelfAdjoint
#print axioms gSelfAdjoint_iff_real_chart
#print axioms diagonalizable_of_gSkew
#print axioms gSkew_iff_imaginary_chart
#print axioms seam_iff_half_chart
#print axioms no_jordan_block_of_gSkew
#print axioms jordanI_has_no_imaginary_chart
#print axioms exists_cayley_unit
#print axioms diagonalizable_of_gUnitary
#print axioms diagonalizable_of_similitude
#print axioms similitude_iff_circle_chart
#print axioms posDef_map_ofReal
#print axioms posDef_map_re
#print axioms real_gSkew_iff_imaginary_chart

end Audit

end Holonics.Coupling.MovingMetricSpectral

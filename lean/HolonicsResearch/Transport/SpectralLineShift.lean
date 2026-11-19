import Mathlib

/-!
# A load moves a simple line by its weight on the mode over the pencil's slope there

Source: #410's box "Information spectroscopy (#404)", its clause "the first-order line shift
`δs = −vᵀ(s²ΔC + sΔD + ΔK)v / vᵀ(2sC + D)v` at a simple line", and the record
`research/records/2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md`,
§1 ("One line, two numbers"). A mode of a constitution is a line `s` of its pencil `P(s) = s²C + sD + K` with
`P(s)v = 0`; a load `(ΔC, ΔD, ΔK)` enters as `P_ε(s) = P(s) + ε(s²ΔC + sΔD + ΔK)`.

[proved-derived; formal-checked] What is proved, over any nontrivially normed field (`ℝ`, `ℂ`).

1. **The left mode is the right mode** (`pencil_transpose`, `vecMul_pencil_eq_zero`): with `Cᵀ = C`, `Dᵀ = D`,
   `Kᵀ = K` the pencil is transpose-symmetric at every `s`, so `P(s)v = 0` gives `vᵀP(s) = 0`. Over `ℂ` this is the
   record's "the left vector is `vᵀ` because `P` is symmetric" (a transpose, not a conjugate transpose).
2. **The line shift** (`hasDerivAt_loaded_apply`, `line_shift_mul`, `line_shift`): if the line `s(ε)` and its mode
   `v(ε)` are differentiable at `ε = 0` and `P_ε(s(ε)) v(ε) = 0` for every `ε` near `0`, then
   `s′(0) · vᵀ(2sC + D)v = −vᵀ(s²ΔC + sΔD + ΔK)v` at `s = s(0)`, `v = v(0)`; where the slope `vᵀ(2sC + D)v` is not
   zero (the simple line) this is the record's `δs`. The proof differentiates `vᵀP_ε(s(ε))v(ε) = 0` and drops the
   term `vᵀP(s)v′(0)` by item 1, so the mode's own motion `v′(0)` never enters.
3. **The shifts add** (`shift_add`, `shift_smul`): `δs` is linear in the load, so a mass, a viscosity and a stiffness
   applied together move the line by the sum of their shifts (the record's "the shifts add").
4. **A lossless line separates the three loads** (`shift_lossless`, `lossless_separates`): with `D = 0` and
   `s = iω`, `ω ≠ 0`, `δs = −iω ΔC_v/(2C_v) − ΔD_v/(2C_v) + i ΔK_v/(2ω C_v)` with `X_v = vᵀXv`: mass slows the turn,
   stiffness quickens it, viscosity alone moves the decay.
5. **The record's witness** (`witness_mass_five`, `witness_mass_thirteen`): `C = I`, `D = 0`, modes `(3, 4)/5` and
   `(−4, 3)/5` on the lossless lines `5i` and `13i`; a unit mass at site 0 moves them by `−9i/10` and `−104i/25`.

Limits. The existence of a differentiable line `s(ε)` and mode `v(ε)` near a simple root of `det P_ε` (the implicit
function theorem on `det`, and a mode chosen from the adjugate) is assumed, not proved: the theorem says what the
derivative is wherever such a branch exists. The record's lossy witness (Rayleigh damping, lines `−3 ± 4i`,
`−5 ± 12i`, "`det P_ε(s + εδs)` has no `ε⁰` and no `ε¹` term") and the microbalance's overtone law are not reproduced,
and the first-order ratio shift `δ log(s₁/s₂)` of §2 is not stated. Second-order shifts are not stated.

The computational object is the helical pair interaction: a line is a pair's move per tick, its boost rate and turn
rate the real and imaginary parts of `s`, and a load reweights the pair's material along the one mode that carries
the line. Of the winding guide's six general objects this touches the pair (the line as the pair's multiplier and
its shift under a change of material) and faces and placement (the mode `v` as the face on which the load is read);
the helix, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `spectro.load-line-shift` (and `spectro.clock-gauge` beside it, whose clock is the shift a
proportional load makes on every line at once); `Transport/InformationSpectroscopy`, whose Limits named this clause;
#410's spectroscopy box.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Transport.SpectralLineShift

open Matrix Finset Filter
open scoped Topology

section Shift

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : Type*} [Fintype n]

/-- [definition] The pencil `P(s) = s²C + sD + K` of a constitution. -/
def pencil (C D K : Matrix n n 𝕜) (s : 𝕜) : Matrix n n 𝕜 := s ^ 2 • C + s • D + K

/-- [definition] The pencil's slope `P′(s) = 2sC + D`. -/
def slope (C D : Matrix n n 𝕜) (s : 𝕜) : Matrix n n 𝕜 := (2 * s) • C + D

/-- [definition] The loaded pencil `P_ε(s) = P(s) + ε(s²ΔC + sΔD + ΔK)`. -/
def loaded (C D K ΔC ΔD ΔK : Matrix n n 𝕜) (ε s : 𝕜) : Matrix n n 𝕜 :=
  pencil C D K s + ε • pencil ΔC ΔD ΔK s

/-- [definition] The first-order line shift `δs = −vᵀ(s²ΔC + sΔD + ΔK)v / vᵀ(2sC + D)v`. -/
def shift (C D : Matrix n n 𝕜) (v : n → 𝕜) (s : 𝕜) (ΔC ΔD ΔK : Matrix n n 𝕜) : 𝕜 :=
  -(v ⬝ᵥ (pencil ΔC ΔD ΔK s *ᵥ v)) / (v ⬝ᵥ (slope C D s *ᵥ v))

omit [Fintype n] in
/-- [proved-standard; formal-checked] A pencil of transpose-symmetric matrices is transpose-symmetric. -/
theorem pencil_transpose {C D K : Matrix n n 𝕜} (hC : Cᵀ = C) (hD : Dᵀ = D) (hK : Kᵀ = K) (s : 𝕜) :
    (pencil C D K s)ᵀ = pencil C D K s := by
  simp [pencil, transpose_add, transpose_smul, hC, hD, hK]

/-- [proved-standard; formal-checked] **The left mode is the right mode**: for a symmetric pencil, `P(s)v = 0` gives
`vᵀP(s) = 0`. -/
theorem vecMul_pencil_eq_zero {C D K : Matrix n n 𝕜} (hC : Cᵀ = C) (hD : Dᵀ = D) (hK : Kᵀ = K)
    {s : 𝕜} {v : n → 𝕜} (hv : pencil C D K s *ᵥ v = 0) : v ᵥ* pencil C D K s = 0 := by
  rw [← pencil_transpose hC hD hK s, vecMul_transpose, hv]

omit [Fintype n] in
/-- [proved-standard; formal-checked] Each entry of the loaded pencil along a differentiable line has the derivative
`(s′P′(s) + ΔP(s))_ij` at `ε = 0`. -/
theorem hasDerivAt_loaded_apply (C D K ΔC ΔD ΔK : Matrix n n 𝕜) {s : 𝕜 → 𝕜} {s' : 𝕜}
    (hs : HasDerivAt s s' 0) (i j : n) :
    HasDerivAt (fun ε => loaded C D K ΔC ΔD ΔK ε (s ε) i j)
      ((s' • slope C D (s 0) + pencil ΔC ΔD ΔK (s 0)) i j) 0 := by
  have h1 := (((hs.fun_pow 2).mul_const (C i j)).fun_add (hs.mul_const (D i j))).add_const (K i j)
  have h2 := (hasDerivAt_id' (x := (0 : 𝕜))).fun_mul
    ((((hs.fun_pow 2).mul_const (ΔC i j)).fun_add (hs.mul_const (ΔD i j))).add_const (ΔK i j))
  refine ((h1.fun_add h2).congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => ?_)
  · simp [slope, pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · simp [loaded, pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- [proved-derived; formal-checked] **The line shift, multiplied out.** If the line `s(ε)` and its mode `v(ε)` are
differentiable at `0` and `P_ε(s(ε)) v(ε) = 0` near `0`, then `s′(0) · vᵀ(2sC + D)v = −vᵀ(s²ΔC + sΔD + ΔK)v`. -/
theorem line_shift_mul {C D K ΔC ΔD ΔK : Matrix n n 𝕜} (hC : Cᵀ = C) (hD : Dᵀ = D) (hK : Kᵀ = K)
    {s : 𝕜 → 𝕜} {v : 𝕜 → n → 𝕜} {s' : 𝕜} {v' : n → 𝕜}
    (hs : HasDerivAt s s' 0) (hv : HasDerivAt v v' 0)
    (hroot : ∀ᶠ ε in 𝓝 0, loaded C D K ΔC ΔD ΔK ε (s ε) *ᵥ v ε = 0) :
    s' * (v 0 ⬝ᵥ (slope C D (s 0) *ᵥ v 0)) = -(v 0 ⬝ᵥ (pencil ΔC ΔD ΔK (s 0) *ᵥ v 0)) := by
  set M' := s' • slope C D (s 0) + pencil ΔC ΔD ΔK (s 0) with hM'
  have hv' : ∀ j, HasDerivAt (fun ε => v ε j) (v' j) 0 := hasDerivAt_pi.1 hv
  -- the reading `f(ε) = v(0)ᵀ P_ε(s(ε)) v(ε)` and its derivative
  have hF : HasDerivAt (fun ε => ∑ i, v 0 i * ∑ j, loaded C D K ΔC ΔD ΔK ε (s ε) i j * v ε j)
      (∑ i, v 0 i * ∑ j, (M' i j * v 0 j + loaded C D K ΔC ΔD ΔK 0 (s 0) i j * v' j)) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.const_mul
    apply HasDerivAt.fun_sum
    intro j _
    exact (hasDerivAt_loaded_apply C D K ΔC ΔD ΔK hs i j).mul (hv' j)
  have h0 : HasDerivAt (fun ε => ∑ i, v 0 i * ∑ j, loaded C D K ΔC ΔD ΔK ε (s ε) i j * v ε j) 0 0 := by
    refine (hasDerivAt_const (0 : 𝕜) (0 : 𝕜)).congr_of_eventuallyEq ?_
    filter_upwards [hroot] with ε hε
    have : v 0 ⬝ᵥ (loaded C D K ΔC ΔD ΔK ε (s ε) *ᵥ v ε) = 0 := by rw [hε, dotProduct_zero]
    simpa [dotProduct, mulVec] using this
  have huniq := hF.unique h0
  -- the mode's own motion drops out: `v(0)ᵀ P(s(0)) = 0`
  have hP0 : loaded C D K ΔC ΔD ΔK 0 (s 0) = pencil C D K (s 0) := by simp [loaded]
  have hnull : pencil C D K (s 0) *ᵥ v 0 = 0 := by
    have := hroot.self_of_nhds
    rwa [hP0] at this
  have hleft : v 0 ⬝ᵥ (pencil C D K (s 0) *ᵥ v') = 0 := by
    rw [dotProduct_mulVec, vecMul_pencil_eq_zero hC hD hK hnull, zero_dotProduct]
  have hsplit : (∑ i, v 0 i * ∑ j, (M' i j * v 0 j + loaded C D K ΔC ΔD ΔK 0 (s 0) i j * v' j)) =
      v 0 ⬝ᵥ (M' *ᵥ v 0) + v 0 ⬝ᵥ (pencil C D K (s 0) *ᵥ v') := by
    rw [hP0]
    simp only [dotProduct, mulVec, Finset.sum_add_distrib, mul_add]
  rw [hsplit, hleft, add_zero, hM', add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul] at huniq
  linear_combination huniq

/-- [proved-derived; formal-checked] **The first-order line shift** at a simple line: where the slope
`vᵀ(2sC + D)v` is not zero, `s′(0) = −vᵀ(s²ΔC + sΔD + ΔK)v / vᵀ(2sC + D)v`. -/
theorem line_shift {C D K ΔC ΔD ΔK : Matrix n n 𝕜} (hC : Cᵀ = C) (hD : Dᵀ = D) (hK : Kᵀ = K)
    {s : 𝕜 → 𝕜} {v : 𝕜 → n → 𝕜} {s' : 𝕜} {v' : n → 𝕜}
    (hs : HasDerivAt s s' 0) (hv : HasDerivAt v v' 0)
    (hroot : ∀ᶠ ε in 𝓝 0, loaded C D K ΔC ΔD ΔK ε (s ε) *ᵥ v ε = 0)
    (hsimple : v 0 ⬝ᵥ (slope C D (s 0) *ᵥ v 0) ≠ 0) :
    s' = shift C D (v 0) (s 0) ΔC ΔD ΔK := by
  rw [shift, eq_div_iff hsimple]
  exact line_shift_mul hC hD hK hs hv hroot

/-- [proved-derived; formal-checked] **The shifts add**: the shift of a sum of loads is the sum of their shifts. -/
theorem shift_add (C D : Matrix n n 𝕜) (v : n → 𝕜) (s : 𝕜) (ΔC ΔD ΔK ΔC' ΔD' ΔK' : Matrix n n 𝕜) :
    shift C D v s (ΔC + ΔC') (ΔD + ΔD') (ΔK + ΔK') =
      shift C D v s ΔC ΔD ΔK + shift C D v s ΔC' ΔD' ΔK' := by
  have h : pencil (ΔC + ΔC') (ΔD + ΔD') (ΔK + ΔK') s = pencil ΔC ΔD ΔK s + pencil ΔC' ΔD' ΔK' s := by
    simp only [pencil, smul_add]
    abel
  simp only [shift, h, add_mulVec, dotProduct_add, neg_add, add_div]

/-- [proved-derived; formal-checked] The shift scales with the load. -/
theorem shift_smul (C D : Matrix n n 𝕜) (v : n → 𝕜) (s c : 𝕜) (ΔC ΔD ΔK : Matrix n n 𝕜) :
    shift C D v s (c • ΔC) (c • ΔD) (c • ΔK) = c * shift C D v s ΔC ΔD ΔK := by
  have h : pencil (c • ΔC) (c • ΔD) (c • ΔK) s = c • pencil ΔC ΔD ΔK s := by
    simp only [pencil, smul_add, smul_comm c]
  simp only [shift, h, smul_mulVec, dotProduct_smul, smul_eq_mul, neg_mul_eq_mul_neg, mul_div_assoc]

end Shift

/-! ## A lossless line -/

section Lossless

open Complex

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] On a lossless constitution (`D = 0`) the shift at a nonzero line is
`−(s²ΔC_v + sΔD_v + ΔK_v)/(2s C_v)`. -/
theorem shift_lossless (C : Matrix n n ℂ) (v : n → ℂ) (s : ℂ) (ΔC ΔD ΔK : Matrix n n ℂ) :
    shift C 0 v s ΔC ΔD ΔK =
      -(s ^ 2 * (v ⬝ᵥ (ΔC *ᵥ v)) + s * (v ⬝ᵥ (ΔD *ᵥ v)) + v ⬝ᵥ (ΔK *ᵥ v)) /
        (2 * s * (v ⬝ᵥ (C *ᵥ v))) := by
  simp only [shift, pencil, slope, add_zero, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul]

/-- [proved-derived; formal-checked] **A lossless line separates the three loads**: at `s = iω`, `ω ≠ 0`, with
`C_v ≠ 0`, `δs = −iω ΔC_v/(2C_v) − ΔD_v/(2C_v) + i ΔK_v/(2ω C_v)`: mass slows the turn, stiffness quickens it,
viscosity alone moves the decay. -/
theorem lossless_separates (C : Matrix n n ℂ) (v : n → ℂ) {ω : ℝ} (hω : ω ≠ 0)
    (hC : v ⬝ᵥ (C *ᵥ v) ≠ 0) (ΔC ΔD ΔK : Matrix n n ℂ) :
    shift C 0 v (I * ω) ΔC ΔD ΔK =
      -(I * ω * (v ⬝ᵥ (ΔC *ᵥ v))) / (2 * (v ⬝ᵥ (C *ᵥ v))) - (v ⬝ᵥ (ΔD *ᵥ v)) / (2 * (v ⬝ᵥ (C *ᵥ v))) +
        I * (v ⬝ᵥ (ΔK *ᵥ v)) / (2 * ω * (v ⬝ᵥ (C *ᵥ v))) := by
  rw [shift_lossless]
  have hω' : (ω : ℂ) ≠ 0 := ofReal_ne_zero.2 hω
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- [proved-derived; formal-checked] **The record's witness, line `5i`**: with `C = I`, `D = 0` and mode `(3, 4)/5`, a
unit mass at site 0 moves the lossless line `5i` by `−9i/10`. -/
theorem witness_mass_five :
    shift (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 ![3 / 5, 4 / 5] (5 * I) !![1, 0; 0, 0] 0 0 = -(9 * I) / 10 := by
  rw [shift_lossless]
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  field_simp
  ring_nf

/-- [proved-derived; formal-checked] **The record's witness, line `13i`**: with mode `(−4, 3)/5`, the same mass moves
the lossless line `13i` by `−104i/25`. -/
theorem witness_mass_thirteen :
    shift (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 ![-4 / 5, 3 / 5] (13 * I) !![1, 0; 0, 0] 0 0 =
      -(104 * I) / 25 := by
  rw [shift_lossless]
  simp [dotProduct, mulVec, Fin.sum_univ_two]
  field_simp
  ring_nf

end Lossless

end Holonics.Transport.SpectralLineShift

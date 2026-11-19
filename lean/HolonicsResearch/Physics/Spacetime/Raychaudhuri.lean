import Holonics.Geometry.Motion
import Holonics.Physics.HolonicFieldTheoryPassage
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-!
# Raychaudhuri's equation: a congruence's rate is a boost and a turn, and the tidal trace focuses it

[definition] The box of #410, "Curvature's strain and rotation: the Weyl tensor's electric/magnetic
split and Petrov's classification; Raychaudhuri's equation from a Lorentzian metric, connection and
congruence", owed since the Swing record
(`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`
§5.6: "a free-falling congruence focuses by strain and resists by rotation"; §9, owed: "the Weyl
split and Petrov; Raychaudhuri"). This module takes the part that is finite algebra and one
ordinary differential equation. Sources: `Geometry/Motion` item 1 (the record's §3.2: against a
receiver's metric a rate splits into a skew turn and a self-adjoint boost; atlas
`motion.turn-boost-split`); the open slots of
`Physics/HolonicFieldTheoryPassage.CongruenceLedger` ("A geometric realization must supply these from
a Lorentzian metric, connection, and congruence"; atlas `coupling.holonic-field-theory-passage`,
`coupling.holonic-focusing-sectors`); the scalar deviation equation and its focus,
`HolonicsResearch/Geometry/Deviation` (atlas `coupling.deviation-focus`); the trace reversal
`R₀₀ = κ(ε + 3p)/2` of `Physics/Spacetime/StressEnergy`; `docs/ELEMENTARY_OBJECTS.md` ("tidal
curvature and frame dragging are the Weyl tensor's strain and rotation parts"); and, in the fluid's
chart, strain against vorticity (atlas `ns.aligned-strain-budget`).

A congruence of free fall is read through its **deviation** `J(τ)`, an `n × n` matrix carrying the
displacements to neighbouring geodesics along proper time `τ`, obeying the deviation (Jacobi)
equation `J″ = −R J` with the tidal matrix `R_ij = R_(i a j b) u^a u^b`. Its rate is the
**deformation** `B = J′J⁻¹` (`deformation`), the logarithmic derivative of the transport `J`. The
comoving receiver reads `B` (metric `G = 1`) as the **expansion** `θ = tr B` (`expansion`), the
**shear** `σ = ½(B + Bᵀ) − (θ/n)·1` (`shear`) and the **rotation** `ω = ½(B − Bᵀ)` (`rotation`),
with the Frobenius pairing `⟨X, Y⟩ = tr(XᵀY)` (`frobenius`) and Raychaudhuri's right side
`−θ²/n − ⟨σ, σ⟩ + ⟨ω, ω⟩ − tr R` (`raychaudhuriRate`). In an orthonormal frame
(`η = diag(−1, 1, 1, 1)`, `minkowskiSign`) a tensor `C` with the curvature symmetries and vanishing
`η`-trace (`WeylSymmetries`) is read by the observer `u = e₀` as its **electric part**
`E_ij = C_(0i0j)` (`electric`) and **magnetic part** `H_ij = ½ Σ_(k,l) ε_(ikl) C_(kl0j)` (`magnetic`,
with `leviCivita`).

[proved-standard; formal-checked] What is proved. Item 1 and the algebra of item 4 hold over any
field of characteristic zero; items 2 and 3, the rates of item 4, and item 5 over ℝ; item 6 over ℚ.

1. **The kinematic split** (`split_eq`, `shear_transpose`, `shear_trace`, `rotation_transpose`,
   `split_unique`, `trace_mul_self_of_split`, `trace_mul_self`). `B = (θ/n)·1 + σ + ω` with `σ`
   symmetric and traceless and `ω` antisymmetric, and any triple `(c, S, W)` of that kind adding to
   `B` is `(θ/n, σ, ω)`. Then `tr(B²) = θ²/n + ⟨σ, σ⟩ − ⟨ω, ω⟩`: the boost parts add and the turn
   part subtracts (with `trace_eq_zero_of_skew`, `trace_mul_symm_skew`). The rotation is
   `Geometry/Motion.turn 1 B` and the symmetric part `Motion.boost 1 B` (`rotation_eq_turn`,
   `symPart_eq_boost`, [proved-derived]), so this split is Motion's at the comoving metric, with the
   boost's trace taken apart.
2. **Raychaudhuri's equation from the deviation equation** (`hasDerivAt_ringInverse_comp`,
   `riccati`, `hasDerivAt_linearMap`, `matrix_riccati`, `trace_riccati`, `raychaudhuri`). In any
   complete normed `ℝ`-algebra, `(J⁻¹)′ = −J⁻¹J′J⁻¹` (from Mathlib's `hasFDerivAt_ringInverse`), so
   `J″ = −RJ` with `J(τ)` a unit gives the Riccati equation `B′ = −B² − R` for `B = J′J⁻¹`. On real
   `n × n` matrices (Mathlib's `linftyOp` normed algebra, as local instances) its trace is
   **Raychaudhuri's equation** `θ′ = −θ²/n − ⟨σ, σ⟩ + ⟨ω, ω⟩ − tr R`.
3. **Focusing and the caustic** (`frobenius_self_nonneg`, `raychaudhuriRate_le`,
   `inv_expansion_ge`, `caustic_within`, `no_negative_expansion_past_caustic`,
   `caustic_of_deviation`, `caustic_sharp`). Where the rotation vanishes and `tr R ≥ 0` (the strong
   energy condition read as a trace), `θ′ ≤ −θ²/n`. A real `θ`, continuous on `[0, T]`,
   differentiable inside it with `θ′ ≤ −θ²/n` and negative on `[0, T]`, has
   `1/θ(τ) ≥ 1/θ(0) + τ/n` there, hence `T < n/|θ(0)|`: no such solution exists on `[0, T]` for
   `T ≥ n/|θ(0)|`. From the deviation equation directly: a rotation-free congruence with `tr R ≥ 0`
   and `θ < 0` on `[0, T]` has `T < n/|θ(0)|`, the caustic within proper time `n/|θ₀|`. The bound
   cannot be lowered: `θ(t) = nθ₀/(n + θ₀t)` starts at `θ₀ < 0`, solves `θ′ = −θ²/n` and stays
   negative for every `t < n/|θ₀|`.
4. **The rotation's and the shear's own laws** (`rotation_mul_self`, `symPart_mul_self`,
   `rotation_of_symm`, `shear_mul_self`, `rotation_law`, `rotation_rate_zero`, `shear_law`). With
   `S = (θ/n)·1 + σ` the symmetric part and `R` symmetric, the antisymmetric part of the Riccati
   equation is `ω′ = −(Sω + ωS)`: the rotation's rate is linear in the rotation, so `ω(τ) = 0`
   gives `ω′(τ) = 0`. Its symmetric traceless part is the shear's law
   `σ′ = −(2θ/n)σ − (σσ + ωω) + (tr(σσ + ωω)/n)·1 − (R − (tr R/n)·1)`.
5. **The electric and magnetic parts** (`electric_symm`, `electric_traceless`, `magnetic_traceless`,
   `magnetic_symm`, `electric_transpose`, `electric_trace`, `raychaudhuriRate_electric`). `E` is
   symmetric (pair exchange) and traceless (the `η`-trace at `(0, 0)` and antisymmetry); `H` is
   traceless (the cyclic identity) and symmetric (the `η`-trace at `(0, m)`). Read as a tidal
   matrix, as the vacuum's tidal matrix is read, `E` is symmetric, so the rotation's law applies,
   and traceless, so it leaves Raychaudhuri's rate as at `R = 0`: the expansion is then focused by
   the shear alone, and the tide reaches it through the shear's law.

[proved-derived; formal-checked]

6. **The ledger's slots are filled** (`ledger_eq_raychaudhuriRate`, `tidal_trace_reads_sector`).
   Over ℚ with `n = 3`, the owner's `CongruenceLedger.returnedExpansionRate` with slots
   `(θ, ⟨σ, σ⟩, ⟨ω, ω⟩, tr R, 0)` is `raychaudhuriRate B R` (a geodesic congruence: zero
   acceleration divergence); where `tr R = (κ/2)(ε + 3p)` (the trace-reversed time component of
   `Physics/Spacetime/StressEnergy` on a perfect sector, taken here as a hypothesis), `−tr R` is
   that sector's `expansionContribution`.

What is not claimed. Petrov's classification (the eigenvalue types of `E + iH`) is stated in `PetrovTypes`. The
deviation equation is a hypothesis: neither `J″ = −RJ` nor `R_ij = R_(i a j b) u^a u^b` is derived
from a Lorentzian metric and its connection, and the tidal matrix's symmetry is assumed where it is
used. A `C` with the curvature symmetries built from a metric's 2-jet, the first nonzero instance of
`WeylSymmetries` (a plane wave), and the vacuum's tidal matrix as `E` stand in `CurvatureJets`, at
one point; here they are read, not derived. The null (Sachs) form, with its two-dimensional screen and
`−θ²/2`, is not stated; nor is an accelerated congruence. A caustic is not exhibited as a point
of a manifold: the statement is that no solution with `θ` negative on `[0, T]` exists past
`n/|θ₀|`. That `ω` vanishing at one instant vanishes along the congruence needs uniqueness for the
rotation's linear law and is not stated; the focusing theorems take `ω = 0` on `[0, T]` as a
hypothesis. Jacobi's formula `θ = (log det J)′` is not stated. The derivatives are taken in
Mathlib's `linftyOp` norm on matrices.

The computational object is the helical pair interaction read on a congruence: two neighbouring
geodesics are a pair, and the deviation `J` is the pair's displacement carried along the tube by
the tidal constitution `J″ = −RJ`, the oscillator of `Geometry/Deviation` with the curvature as its
stiffness. The deformation `B = J′J⁻¹` is the pair's rate read through its own transport, a
logarithmic derivative (the ratio object's `dR·R⁻¹`), and the comoving receiver splits it as Motion
does: the boost (expansion and shear, self-adjoint) carries the expansion, and the turn (rotation,
skew and so traceless, `trace_eq_zero_of_skew`) carries none and enters the expansion's rate with
the opposite sign. Of the winding guide's six general objects this touches the pair (the deviation
between neighbouring strands), the tube (the congruence along proper time) and faces and placement
(the expansion, shear and rotation as the comoving receiver's faces of `B`, and `E`, `H` as the
observer's faces of `C`); the helix, the cell holonomy (the rotation's circulation around a cell is
not read here) and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.Raychaudhuri

open Matrix Set

/-! ## 1. The kinematic split -/

section Split

variable {K : Type*} [Field K] {n : ℕ}

/-- [definition] The **expansion** of a rate: `θ = tr B`. -/
def expansion (B : Matrix (Fin n) (Fin n) K) : K := B.trace

/-- [definition] The **symmetric part** of a rate: `½(B + Bᵀ)`, the boost at the comoving metric. -/
def symPart (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := (2⁻¹ : K) • (B + Bᵀ)

/-- [definition] The **shear** of a rate: `σ = ½(B + Bᵀ) − (θ/n)·1`. -/
def shear (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  (2⁻¹ : K) • (B + Bᵀ) - (expansion B / n) • (1 : Matrix (Fin n) (Fin n) K)

/-- [definition] The **rotation** of a rate: `ω = ½(B − Bᵀ)`, the turn at the comoving metric. -/
def rotation (B : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K := (2⁻¹ : K) • (B - Bᵀ)

/-- [definition] The **Frobenius pairing** `⟨X, Y⟩ = tr(XᵀY)`. -/
def frobenius (X Y : Matrix (Fin n) (Fin n) K) : K := (Xᵀ * Y).trace

/-- [proved-standard; formal-checked] **The split adds back**: `(θ/n)·1 + σ + ω = B`. -/
theorem split_eq [CharZero K] (B : Matrix (Fin n) (Fin n) K) :
    (expansion B / n) • (1 : Matrix (Fin n) (Fin n) K) + shear B + rotation B = B := by
  ext i j
  simp only [shear, rotation, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.transpose_apply, smul_eq_mul]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The shear is symmetric.** -/
theorem shear_transpose (B : Matrix (Fin n) (Fin n) K) : (shear B)ᵀ = shear B := by
  simp only [shear, transpose_sub, transpose_smul, transpose_add, transpose_transpose,
    transpose_one, add_comm Bᵀ B]

/-- [proved-standard; formal-checked] **The shear is traceless.** -/
theorem shear_trace [CharZero K] (hn : (n : K) ≠ 0) (B : Matrix (Fin n) (Fin n) K) :
    (shear B).trace = 0 := by
  simp only [shear, expansion, trace_sub, trace_smul, trace_add, trace_transpose, trace_one,
    Fintype.card_fin, smul_eq_mul]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The rotation is antisymmetric.** -/
theorem rotation_transpose (B : Matrix (Fin n) (Fin n) K) : (rotation B)ᵀ = -rotation B := by
  simp only [rotation, transpose_smul, transpose_sub, transpose_transpose, ← smul_neg, neg_sub]

/-- [proved-standard; formal-checked] An antisymmetric matrix is traceless. -/
theorem trace_eq_zero_of_skew [CharZero K] {W : Matrix (Fin n) (Fin n) K} (hW : Wᵀ = -W) :
    W.trace = 0 := by
  have h := trace_transpose W
  rw [hW, trace_neg] at h
  exact neg_eq_self.mp h

/-- [proved-standard; formal-checked] A symmetric times an antisymmetric matrix is traceless. -/
theorem trace_mul_symm_skew [CharZero K] {S W : Matrix (Fin n) (Fin n) K} (hS : Sᵀ = S)
    (hW : Wᵀ = -W) : (S * W).trace = 0 := by
  have h := trace_transpose (S * W)
  rw [transpose_mul, hS, hW, neg_mul, trace_neg, trace_mul_comm] at h
  exact neg_eq_self.mp h

/-- [proved-standard; formal-checked] **The split is unique**: a scalar, a symmetric traceless and an
antisymmetric part adding to `B` are `θ/n`, `σ` and `ω`. -/
theorem split_unique [CharZero K] (hn : (n : K) ≠ 0) {B : Matrix (Fin n) (Fin n) K} {c : K}
    {S W : Matrix (Fin n) (Fin n) K} (hS : Sᵀ = S) (hS0 : S.trace = 0) (hW : Wᵀ = -W)
    (h : c • (1 : Matrix (Fin n) (Fin n) K) + S + W = B) :
    c = expansion B / n ∧ S = shear B ∧ W = rotation B := by
  have hW0 := trace_eq_zero_of_skew hW
  have hc : c = expansion B / n := by
    rw [expansion, ← h]
    simp only [trace_add, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hS0, hW0, add_zero]
    field_simp
  have hBt : Bᵀ = c • (1 : Matrix (Fin n) (Fin n) K) + S - W := by
    rw [← h]; simp only [transpose_add, transpose_smul, transpose_one, hS, hW, sub_eq_add_neg]
  refine ⟨hc, ?_, ?_⟩
  · rw [shear, hBt, ← hc]
    conv_rhs => rw [← h]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · rw [rotation, hBt]
    conv_rhs => rw [← h]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- [proved-standard; formal-checked] `tr((c·1 + S + W)²) = c²n + ⟨S, S⟩ − ⟨W, W⟩` for `S` symmetric
traceless and `W` antisymmetric. -/
theorem trace_mul_self_of_split [CharZero K] (c : K) {S W : Matrix (Fin n) (Fin n) K}
    (hS : Sᵀ = S) (hS0 : S.trace = 0) (hW : Wᵀ = -W) :
    ((c • (1 : Matrix (Fin n) (Fin n) K) + S + W) * (c • 1 + S + W)).trace
      = c ^ 2 * n + frobenius S S - frobenius W W := by
  have hW0 := trace_eq_zero_of_skew hW
  have hSW := trace_mul_symm_skew hS hW
  have hWS : (W * S).trace = 0 := by rw [trace_mul_comm]; exact hSW
  simp only [frobenius, hS, hW, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, trace_add, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, hS0, hW0,
    hSW, hWS, Matrix.neg_mul, trace_neg]
  ring

/-- [proved-standard; formal-checked] **The boosts add and the turn subtracts**:
`tr(B²) = θ²/n + ⟨σ, σ⟩ − ⟨ω, ω⟩`. -/
theorem trace_mul_self [CharZero K] (hn : (n : K) ≠ 0) (B : Matrix (Fin n) (Fin n) K) :
    (B * B).trace = expansion B ^ 2 / n + frobenius (shear B) (shear B)
      - frobenius (rotation B) (rotation B) := by
  conv_lhs => rw [← split_eq B]
  rw [trace_mul_self_of_split _ (shear_transpose B) (shear_trace hn B) (rotation_transpose B)]
  field_simp

/-- [proved-derived; formal-checked] **The rotation is Motion's turn** at the comoving metric `1`. -/
theorem rotation_eq_turn [Invertible (2 : K)] (B : Matrix (Fin n) (Fin n) K) :
    rotation B = Holonics.Geometry.Motion.turn 1 B := by
  simp [rotation, Holonics.Geometry.Motion.turn, Holonics.Geometry.Motion.adjointIn, invOf_eq_inv]

/-- [proved-derived; formal-checked] **The symmetric part is Motion's boost** at the metric `1`. -/
theorem symPart_eq_boost [Invertible (2 : K)] (B : Matrix (Fin n) (Fin n) K) :
    symPart B = Holonics.Geometry.Motion.boost 1 B := by
  simp [symPart, Holonics.Geometry.Motion.boost, Holonics.Geometry.Motion.adjointIn, invOf_eq_inv]

/-- [proved-standard; formal-checked] The turn of a square: `rot(B²) = S ω + ω S`, `S = sym B`. -/
theorem rotation_mul_self [CharZero K] (B : Matrix (Fin n) (Fin n) K) :
    rotation (B * B) = symPart B * rotation B + rotation B * symPart B := by
  simp only [rotation, symPart, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    sub_mul, mul_sub]
  module

/-- [proved-standard; formal-checked] The boost of a square: `sym(B²) = S S + ω ω`. -/
theorem symPart_mul_self [CharZero K] (B : Matrix (Fin n) (Fin n) K) :
    symPart (B * B) = symPart B * symPart B + rotation B * rotation B := by
  simp only [rotation, symPart, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    sub_mul, mul_sub]
  module

/-- [proved-standard; formal-checked] A symmetric matrix has no rotation. -/
theorem rotation_of_symm {R : Matrix (Fin n) (Fin n) K} (hR : Rᵀ = R) : rotation R = 0 := by
  simp [rotation, hR]

/-- [proved-standard; formal-checked] The shear of a square:
`shear(B²) = (2θ/n)σ + (σσ + ωω) − (tr(σσ + ωω)/n)·1`. -/
theorem shear_mul_self [CharZero K] (hn : (n : K) ≠ 0) (B : Matrix (Fin n) (Fin n) K) :
    shear (B * B) = (2 * expansion B / n) • shear B
      + (shear B * shear B + rotation B * rotation B)
      - ((shear B * shear B + rotation B * rotation B).trace / n)
        • (1 : Matrix (Fin n) (Fin n) K) := by
  have hS : symPart B = (expansion B / n) • (1 : Matrix (Fin n) (Fin n) K) + shear B := by
    simp only [shear, symPart]; abel
  have h1 : shear (B * B)
      = symPart (B * B) - ((B * B).trace / n) • (1 : Matrix (Fin n) (Fin n) K) := rfl
  rw [h1, symPart_mul_self, hS, trace_mul_self hn]
  simp only [frobenius, shear_transpose, rotation_transpose, neg_mul, trace_neg, add_mul, mul_add,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, trace_add,
    sub_neg_eq_add]
  module

/-- [definition] The shear as a linear map. -/
def shearₗ : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := shear
  map_add' X Y := by
    simp only [shear, expansion, transpose_add, trace_add, add_div, add_smul]
    module
  map_smul' c X := by
    simp only [shear, expansion, transpose_smul, trace_smul, smul_eq_mul, RingHom.id_apply]
    rw [mul_div_assoc, ← smul_smul]
    module

/-- [definition] The rotation as a linear map. -/
def rotationₗ : Matrix (Fin n) (Fin n) K →ₗ[K] Matrix (Fin n) (Fin n) K where
  toFun := rotation
  map_add' X Y := by
    simp only [rotation, transpose_add]
    module
  map_smul' c X := by
    simp only [rotation, transpose_smul, RingHom.id_apply]
    module

/-- [definition] **Raychaudhuri's right side** `−θ²/n − ⟨σ, σ⟩ + ⟨ω, ω⟩ − tr R`. -/
def raychaudhuriRate (B R : Matrix (Fin n) (Fin n) K) : K :=
  -(expansion B ^ 2 / n) - frobenius (shear B) (shear B) + frobenius (rotation B) (rotation B)
    - R.trace

/-- [proved-standard; formal-checked] The trace of the Riccati right side is Raychaudhuri's. -/
theorem trace_riccati [CharZero K] (hn : (n : K) ≠ 0) (B R : Matrix (Fin n) (Fin n) K) :
    (-(B * B) - R).trace = raychaudhuriRate B R := by
  rw [trace_sub, trace_neg, trace_mul_self hn, raychaudhuriRate]
  ring

end Split

/-! ## 2. Raychaudhuri's equation from the deviation equation -/

section Algebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [HasSummableGeomSeries A]

/-- [proved-standard; formal-checked] **The inverse's rate**: `(J⁻¹)′ = −J⁻¹ J′ J⁻¹` at a unit. -/
theorem hasDerivAt_ringInverse_comp {J : ℝ → A} {J' : A} {τ : ℝ} (hJ : HasDerivAt J J' τ)
    (hu : IsUnit (J τ)) :
    HasDerivAt (fun t => Ring.inverse (J t))
      (-(Ring.inverse (J τ) * J' * Ring.inverse (J τ))) τ := by
  obtain ⟨u, hu⟩ := hu
  have hR : HasFDerivAt Ring.inverse (-(ContinuousLinearMap.mulLeftRight ℝ A ↑u⁻¹ ↑u⁻¹)) (J τ) :=
    hu ▸ hasFDerivAt_ringInverse (𝕜 := ℝ) u
  have h := hR.comp_hasDerivAt τ hJ
  rw [← hu, Ring.inverse_unit]
  simpa [Function.comp_def] using h

/-- [proved-standard; formal-checked] **The Riccati equation**: `J″ = −RJ` gives `B′ = −B² − R` for
`B = J′J⁻¹`, in any complete normed `ℝ`-algebra. -/
theorem riccati {J J' R : ℝ → A} {τ : ℝ} (hJ : HasDerivAt J (J' τ) τ)
    (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ)) :
    HasDerivAt (fun t => J' t * Ring.inverse (J t))
      (-(J' τ * Ring.inverse (J τ) * (J' τ * Ring.inverse (J τ))) - R τ) τ := by
  have h := hJ'.mul (hasDerivAt_ringInverse_comp hJ hu)
  have hJJ : J τ * Ring.inverse (J τ) = 1 := Ring.mul_inverse_cancel _ hu
  convert h using 1
  · rfl
  · simp only [neg_mul, mul_neg, mul_assoc, hJJ, mul_one]
    abel

end Algebra

section MatrixCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

/-- [definition] The **deformation** `B = J′J⁻¹` of a deviation `J` with rate `J′`. -/
def deformation (J J' : ℝ → Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  J' t * (J t)⁻¹

/-- [proved-standard; formal-checked] A linear map of matrices carries rates. -/
theorem hasDerivAt_linearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] F) {B : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {B' : Matrix (Fin n) (Fin n) ℝ} {τ : ℝ} (h : HasDerivAt B B' τ) :
    HasDerivAt (fun t => L (B t)) (L B') τ :=
  (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt τ h

/-- [proved-standard; formal-checked] **The matrix Riccati equation** `B′ = −B² − R`. -/
theorem matrix_riccati {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hJ : HasDerivAt J (J' τ) τ) (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ).det) :
    HasDerivAt (deformation J J')
      (-(deformation J J' τ * deformation J J' τ) - R τ) τ := by
  have h := riccati hJ hJ' ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  have hB : deformation J J' = fun t => J' t * Ring.inverse (J t) := by
    funext t; simp only [deformation, nonsing_inv_eq_ringInverse]
  rw [hB]
  exact h

/-- [proved-standard; formal-checked] **Raychaudhuri's equation**
`θ′ = −θ²/n − ⟨σ, σ⟩ + ⟨ω, ω⟩ − tr R`. -/
theorem raychaudhuri (hn : (n : ℝ) ≠ 0) {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hJ : HasDerivAt J (J' τ) τ) (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ).det) :
    HasDerivAt (fun t => expansion (deformation J J' t))
      (raychaudhuriRate (deformation J J' τ) (R τ)) τ := by
  have h := hasDerivAt_linearMap (traceLinearMap (Fin n) ℝ ℝ) (matrix_riccati hJ hJ' hu)
  simp only [traceLinearMap_apply, trace_riccati hn] at h
  exact h

/-- [proved-standard; formal-checked] **The rotation's law** `ω′ = −(Sω + ωS)` for a symmetric
tidal matrix. -/
theorem rotation_law {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hJ : HasDerivAt J (J' τ) τ) (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ).det)
    (hR : (R τ)ᵀ = R τ) :
    HasDerivAt (fun t => rotation (deformation J J' t))
      (-(symPart (deformation J J' τ) * rotation (deformation J J' τ)
        + rotation (deformation J J' τ) * symPart (deformation J J' τ))) τ := by
  have h := hasDerivAt_linearMap rotationₗ (matrix_riccati hJ hJ' hu)
  refine HasDerivAt.congr_deriv (f := fun t => rotation (deformation J J' t)) h ?_
  rw [map_sub, map_neg]
  change -rotation _ - rotation _ = _
  rw [rotation_mul_self, rotation_of_symm hR, sub_zero]

/-- [proved-standard; formal-checked] **A rotation-free instant has no rotation rate.** -/
theorem rotation_rate_zero {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hJ : HasDerivAt J (J' τ) τ) (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ).det)
    (hR : (R τ)ᵀ = R τ) (hω : rotation (deformation J J' τ) = 0) :
    HasDerivAt (fun t => rotation (deformation J J' t)) 0 τ := by
  have h := rotation_law hJ hJ' hu hR
  rwa [hω, mul_zero, zero_mul, add_zero, neg_zero] at h

/-- [proved-standard; formal-checked] **The shear's law**
`σ′ = −(2θ/n)σ − (σσ + ωω) + (tr(σσ + ωω)/n)·1 − shear R`. -/
theorem shear_law (hn : (n : ℝ) ≠ 0) {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {τ : ℝ}
    (hJ : HasDerivAt J (J' τ) τ) (hJ' : HasDerivAt J' (-(R τ * J τ)) τ) (hu : IsUnit (J τ).det) :
    HasDerivAt (fun t => shear (deformation J J' t))
      (-((2 * expansion (deformation J J' τ) / n) • shear (deformation J J' τ)
        + (shear (deformation J J' τ) * shear (deformation J J' τ)
          + rotation (deformation J J' τ) * rotation (deformation J J' τ))
        - ((shear (deformation J J' τ) * shear (deformation J J' τ)
          + rotation (deformation J J' τ) * rotation (deformation J J' τ)).trace / n)
          • (1 : Matrix (Fin n) (Fin n) ℝ))
        - shear (R τ)) τ := by
  have h := hasDerivAt_linearMap shearₗ (matrix_riccati hJ hJ' hu)
  refine HasDerivAt.congr_deriv (f := fun t => shear (deformation J J' t)) h ?_
  rw [map_sub, map_neg]
  change -shear _ - shear _ = _
  rw [shear_mul_self hn]

/-! ## 3. Focusing and the caustic -/

/-- [proved-standard; formal-checked] `⟨X, X⟩ ≥ 0` over ℝ. -/
theorem frobenius_self_nonneg (X : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobenius X X := by
  simp only [frobenius, trace, diag, mul_apply, transpose_apply]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- [proved-standard; formal-checked] **Focusing**: no rotation and `tr R ≥ 0` give a rate at most
`−θ²/n`. -/
theorem raychaudhuriRate_le {B R : Matrix (Fin n) (Fin n) ℝ} (hω : rotation B = 0)
    (hR : 0 ≤ R.trace) : raychaudhuriRate B R ≤ -(expansion B ^ 2 / n) := by
  have h0 : frobenius (0 : Matrix (Fin n) (Fin n) ℝ) 0 = 0 := by simp [frobenius]
  have hσ := frobenius_self_nonneg (shear B)
  rw [raychaudhuriRate, hω, h0]
  linarith

end MatrixCalculus

section Focusing

/-- [proved-standard; formal-checked] **The reciprocal bound** `1/θ(τ) ≥ 1/θ(0) + τ/n` under
`θ′ ≤ −θ²/n` with `θ < 0`. -/
theorem inv_expansion_ge {θ θ' : ℝ → ℝ} {n T : ℝ} (hn : 0 < n)
    (hcont : ContinuousOn θ (Icc 0 T)) (hd : ∀ t ∈ Ioo 0 T, HasDerivAt θ (θ' t) t)
    (hfoc : ∀ t ∈ Ioo 0 T, θ' t ≤ -(θ t ^ 2 / n)) (hneg : ∀ t ∈ Icc 0 T, θ t < 0) :
    ∀ τ ∈ Icc 0 T, 1 / θ 0 + τ / n ≤ 1 / θ τ := by
  have hmono : MonotoneOn (fun t => (θ t)⁻¹ - t / n) (Icc 0 T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => -θ' t / θ t ^ 2 - 1 / n)
      (convex_Icc 0 T) ?_ ?_ ?_
    · exact (hcont.inv₀ fun t ht => (hneg t ht).ne).sub (continuousOn_id.div_const n)
    · intro t ht
      rw [interior_Icc] at ht
      have ht' : θ t ≠ 0 := (hneg t (Ioo_subset_Icc_self ht)).ne
      exact (((hd t ht).fun_inv ht').fun_sub ((hasDerivAt_id' t).div_const n)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hθ : θ t < 0 := hneg t (Ioo_subset_Icc_self ht)
      have hθ2 : 0 < θ t ^ 2 := sq_pos_of_neg hθ
      have hf := hfoc t ht
      have hθ' : θ t ≠ 0 := hθ.ne
      have hn' : n ≠ 0 := hn.ne'
      have : -θ' t / θ t ^ 2 - 1 / n = (-θ' t - θ t ^ 2 / n) / θ t ^ 2 := by
        field_simp
      rw [this]
      exact div_nonneg (by linarith) hθ2.le
  intro τ hτ
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hτ.1.trans hτ.2⟩
  have := hmono h0 hτ hτ.1
  simp only [zero_div, sub_zero] at this
  rw [one_div, one_div]
  linarith

/-- [proved-standard; formal-checked] **The caustic within `n/|θ₀|`**: a negative expansion under
`θ′ ≤ −θ²/n` lasts less than `n/|θ(0)|`. -/
theorem caustic_within {θ θ' : ℝ → ℝ} {n T : ℝ} (hn : 0 < n)
    (hcont : ContinuousOn θ (Icc 0 T)) (hd : ∀ t ∈ Ioo 0 T, HasDerivAt θ (θ' t) t)
    (hfoc : ∀ t ∈ Ioo 0 T, θ' t ≤ -(θ t ^ 2 / n)) (hneg : ∀ t ∈ Icc 0 T, θ t < 0) :
    T < n / |θ 0| := by
  by_contra hT
  push Not at hT
  have hθ0 : θ 0 < 0 := hneg 0 ⟨le_rfl, (div_nonneg hn.le (abs_nonneg _)).trans hT⟩
  have habs : |θ 0| = -θ 0 := abs_of_neg hθ0
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = n / |θ 0| := ⟨_, rfl⟩
  have hτ : τ ∈ Icc 0 T := ⟨hτdef ▸ div_nonneg hn.le (abs_nonneg _), hτdef ▸ hT⟩
  have hb := inv_expansion_ge hn hcont hd hfoc hneg τ hτ
  have hτn : τ / n = -(1 / θ 0) := by
    rw [hτdef, habs]; field_simp
  rw [hτn, add_neg_cancel] at hb
  have : 1 / θ τ < 0 := one_div_neg.mpr (hneg τ hτ)
  linarith

/-- [proved-standard; formal-checked] **No negative expansion past the caustic**: for
`T ≥ n/|θ(0)|` no solution of `θ′ ≤ −θ²/n` stays negative on `[0, T]`. -/
theorem no_negative_expansion_past_caustic {θ θ' : ℝ → ℝ} {n T : ℝ} (hn : 0 < n)
    (hcont : ContinuousOn θ (Icc 0 T)) (hd : ∀ t ∈ Ioo 0 T, HasDerivAt θ (θ' t) t)
    (hfoc : ∀ t ∈ Ioo 0 T, θ' t ≤ -(θ t ^ 2 / n)) (hT : n / |θ 0| ≤ T) :
    ¬ ∀ t ∈ Icc 0 T, θ t < 0 :=
  fun hneg => (caustic_within hn hcont hd hfoc hneg).not_ge hT

/-- [proved-standard; formal-checked] **The bound is attained**: `θ(t) = nθ₀/(n + θ₀t)` solves
`θ′ = −θ²/n`, starts at `θ₀` and stays negative before `n/|θ₀|`. -/
theorem caustic_sharp {n θ₀ t : ℝ} (hn : 0 < n) (hθ₀ : θ₀ < 0) (htc : t < n / |θ₀|) :
    HasDerivAt (fun s => n * θ₀ / (n + θ₀ * s)) (-((n * θ₀ / (n + θ₀ * t)) ^ 2 / n)) t
      ∧ n * θ₀ / (n + θ₀ * 0) = θ₀ ∧ n * θ₀ / (n + θ₀ * t) < 0 := by
  have hn' : n ≠ 0 := hn.ne'
  have hpos : 0 < n + θ₀ * t := by
    rw [abs_of_neg hθ₀, lt_div_iff₀ (by linarith)] at htc
    nlinarith
  refine ⟨?_, by rw [mul_zero, add_zero]; field_simp, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hn hθ₀) hpos⟩
  have h := (hasDerivAt_const t (n * θ₀)).div (((hasDerivAt_id' t).const_mul θ₀).const_add n)
    hpos.ne'
  refine h.congr_deriv ?_
  field_simp
  ring

section Deviation

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- [proved-standard; formal-checked] **Focusing from the deviation equation**: a rotation-free
congruence with `tr R ≥ 0` and `θ < 0` on `[0, T]` has `T < n/|θ(0)|`. -/
theorem caustic_of_deviation {n : ℕ} (hn : 0 < n) {J J' R : ℝ → Matrix (Fin n) (Fin n) ℝ} {T : ℝ}
    (hJ : ∀ t ∈ Icc 0 T, HasDerivAt J (J' t) t)
    (hJ' : ∀ t ∈ Icc 0 T, HasDerivAt J' (-(R t * J t)) t)
    (hu : ∀ t ∈ Icc 0 T, IsUnit (J t).det)
    (hω : ∀ t ∈ Icc 0 T, rotation (deformation J J' t) = 0)
    (hR : ∀ t ∈ Icc 0 T, 0 ≤ (R t).trace)
    (hneg : ∀ t ∈ Icc 0 T, expansion (deformation J J' t) < 0) :
    T < n / |expansion (deformation J J' 0)| := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hd : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => expansion (deformation J J' s))
      (raychaudhuriRate (deformation J J' t) (R t)) t :=
    fun t ht => raychaudhuri hn'.ne' (hJ t ht) (hJ' t ht) (hu t ht)
  refine caustic_within (θ' := fun t => raychaudhuriRate (deformation J J' t) (R t)) hn'
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => hd t (Ioo_subset_Icc_self ht))
    (fun t ht => raychaudhuriRate_le (hω t (Ioo_subset_Icc_self ht)) (hR t (Ioo_subset_Icc_self ht)))
    hneg

end Deviation

end Focusing

/-! ## 4. The electric and magnetic parts -/

section ElectricMagnetic

/-- [definition] The orthonormal frame's signs `η = diag(−1, 1, 1, 1)`. -/
def minkowskiSign : Fin 4 → ℝ := ![-1, 1, 1, 1]

/-- [definition] The curvature symmetries and the vanishing `η`-trace of a Weyl tensor in an
orthonormal frame. -/
structure WeylSymmetries (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : Prop where
  anti_left : ∀ a b c d, C b a c d = -C a b c d
  anti_right : ∀ a b c d, C a b d c = -C a b c d
  pair : ∀ a b c d, C c d a b = C a b c d
  cyclic : ∀ a b c d, C a b c d + C a c d b + C a d b c = 0
  traceless : ∀ b d, ∑ a, minkowskiSign a * C a b a d = 0

/-- [definition] The **electric part** `E_ij = C_(0i0j)` read by the observer `u = e₀`. -/
def electric (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (i j : Fin 3) : ℝ := C 0 i.succ 0 j.succ

/-- [definition] The Levi-Civita symbol on three indices, `ε₀₁₂ = 1`. -/
def leviCivita : Fin 3 → Fin 3 → Fin 3 → ℝ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

/-- [definition] The **magnetic part** `H_ij = ½ Σ_(k,l) ε_(ikl) C_(kl0j)`. -/
def magnetic (C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) (i j : Fin 3) : ℝ :=
  2⁻¹ * ∑ k, ∑ l, leviCivita i k l * C k.succ l.succ 0 j.succ

variable {C : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ}

/-- [proved-standard; formal-checked] **`E` is symmetric** (pair exchange). -/
theorem electric_symm (h : WeylSymmetries C) (i j : Fin 3) : electric C i j = electric C j i :=
  (h.pair 0 i.succ 0 j.succ).symm

/-- [proved-standard; formal-checked] **`E` is traceless** (the `η`-trace at `(0, 0)`). -/
theorem electric_traceless (h : WeylSymmetries C) : ∑ i, electric C i i = 0 := by
  have ht := h.traceless 0 0
  rw [Fin.sum_univ_succ] at ht
  have h00 : C 0 0 0 0 = 0 := by have := h.anti_left 0 0 0 0; linarith
  have hsign : ∀ i : Fin 3, minkowskiSign i.succ = 1 := by intro i; fin_cases i <;> rfl
  have hsw : ∀ i : Fin 3, C i.succ 0 i.succ 0 = C 0 i.succ 0 i.succ := by
    intro i; rw [h.anti_left 0 i.succ i.succ 0, h.anti_right 0 i.succ 0 i.succ, neg_neg]
  simp only [hsign, one_mul, hsw, h00, mul_zero, zero_add] at ht
  exact ht

/-- [proved-standard; formal-checked] **`H` is traceless** (the cyclic identity). -/
theorem magnetic_traceless (h : WeylSymmetries C) : ∑ i, magnetic C i i = 0 := by
  simp only [magnetic, Fin.sum_univ_three, leviCivita]
  simp
  linarith [h.anti_left 2 3 0 1, h.anti_left 3 1 0 2, h.anti_left 1 2 0 3, h.pair 0 1 2 3,
    h.pair 0 2 3 1, h.pair 0 3 1 2, h.cyclic 0 1 2 3]

/-- [proved-standard; formal-checked] **`H` is symmetric** (the `η`-trace at `(0, m)`). -/
theorem magnetic_symm (h : WeylSymmetries C) (i j : Fin 3) : magnetic C i j = magnetic C j i := by
  have t1 := h.traceless 0 1
  have t2 := h.traceless 0 2
  have t3 := h.traceless 0 3
  simp [Fin.sum_univ_four, minkowskiSign] at t1 t2 t3
  fin_cases i <;> fin_cases j <;> simp [magnetic, Fin.sum_univ_three, leviCivita] <;>
  linarith [h.anti_left 0 0 0 1, h.anti_left 0 0 0 2, h.anti_left 0 0 0 3,
    h.anti_right 1 0 1 1, h.anti_right 2 0 2 2, h.anti_right 3 0 3 3,
    h.anti_left 2 3 0 2, h.anti_left 3 1 0 1, h.anti_left 0 1 1 3, h.anti_right 0 1 3 1,
    h.pair 0 1 3 1, h.anti_left 0 2 2 3, h.pair 0 2 2 3,
    h.anti_left 2 3 0 3, h.anti_left 1 2 0 1, h.pair 0 1 1 2, h.anti_left 0 1 1 2,
    h.anti_left 0 3 3 2, h.anti_right 0 3 2 3, h.pair 0 3 2 3,
    h.anti_left 3 1 0 3, h.anti_left 1 2 0 2, h.pair 0 2 1 2, h.anti_left 0 2 2 1,
    h.anti_right 0 2 1 2, h.pair 0 3 3 1, h.anti_left 0 3 3 1]

/-- [proved-standard; formal-checked] `E` read as a matrix is symmetric. -/
theorem electric_transpose (h : WeylSymmetries C) :
    (Matrix.of (electric C))ᵀ = Matrix.of (electric C) := by
  ext i j
  exact electric_symm h j i

/-- [proved-standard; formal-checked] `E` read as a matrix is traceless. -/
theorem electric_trace (h : WeylSymmetries C) : (Matrix.of (electric C)).trace = 0 :=
  electric_traceless h

/-- [proved-standard; formal-checked] **The vacuum tide leaves the expansion's rate as at `R = 0`.** -/
theorem raychaudhuriRate_electric (h : WeylSymmetries C) (B : Matrix (Fin 3) (Fin 3) ℝ) :
    raychaudhuriRate B (Matrix.of (electric C)) = raychaudhuriRate B 0 := by
  simp only [raychaudhuriRate, electric_trace h, trace_zero]

end ElectricMagnetic

/-! ## 5. The ledger's slots -/

section Ledger

open Holonics.Physics.HolonicFieldTheoryPassage

/-- [proved-derived; formal-checked] **The ledger's slots are filled**: over ℚ in three dimensions
the owner's returned rate is `raychaudhuriRate B R` for a geodesic congruence. -/
theorem ledger_eq_raychaudhuriRate (B R : Matrix (Fin 3) (Fin 3) ℚ) :
    (⟨expansion B, frobenius (shear B) (shear B), frobenius (rotation B) (rotation B), R.trace, 0⟩ :
      CongruenceLedger).returnedExpansionRate = raychaudhuriRate B R := by
  simp only [CongruenceLedger.returnedExpansionRate, raychaudhuriRate, Nat.cast_ofNat]
  ring

/-- [proved-derived; formal-checked] **The tidal trace reads the sector**: `tr R = (κ/2)(ε + 3p)`
makes `−tr R` the sector's `expansionContribution`. -/
theorem tidal_trace_reads_sector (κ : ℚ) (s : PerfectFieldSector) {R : Matrix (Fin 3) (Fin 3) ℚ}
    (hR : R.trace = κ / 2 * s.activeDensity) : -R.trace = s.expansionContribution κ := by
  rw [hR, PerfectFieldSector.expansionContribution]
  ring

end Ledger

end Holonics.Physics.Spacetime.Raychaudhuri

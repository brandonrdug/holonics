import Holonics.Objects.RatioPhase
import Holonics.Objects.Ratio.CarriedPower
import Holonics.Aeon.Clock.Winding
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# HNN.Ratio: the Holon ratio at the receiver's face, and the carried power

[definition] Item 5 of the step 4 design (`docs/plans/THE_REBUILD.md`, "The laws stated in Lean
first", and "Exact charts"). At receiving phase `j` the produced Holon `|H⟩` (the logits `f_j` read
from the receiving ring's anchor through `R P_R^(τ_R)`) is compared with the target `|T⟩` read
through the same encoder and clock: `R_j = Ĝ_(T←H)`, `ℓ_j = log R_j` with the winding as its
branch. The receiver reads each exponent at its grain `L_R`, `f = n + k/L_R + ε`, builds the face
exactly in `ℚ(θ_R)`, `θ_R^(L_R) = 2`, and returns `ε` as its fibre. Nothing rounds;
`Objects/CommitRebase` is not used.

[proved-derived; formal-checked] What is proved.

1. **A common rechart leaves the ratio** (`receivingPhase_ratio`): shifting target and produced
   phases by one receiving-clock rechart leaves every `ℓ_j` and the lifted cross-entropy excess
   (the owner's `liftedCrossEntropy_commonPhase`), and `ℓ_j` stays in the log fibre of the
   recharted pair (`logRatio_mem_logFibre`). A rechart of the produced side alone moves `ℓ_j`
   (`produced_rechart_moves_the_ratio`).
2. **The pullback to the anchor** (`receivingPhase_pullback`): through the read `R P^τ`,
   `⟨g, R P^τ v⟩ = ⟨(P^τ)⁻¹ R† g, v⟩`; on a closing ring (`P^d = 1`) the inverse is the
   nonnegative power `P^((d−1)τ)`. Along the anchor line `v + x δ` the excess moves by the owner's
   `hasDerivAt_excess_curve`, whose code-length face is `Σ_j (p̂_j − q_j)(Re R P^τ δ)_j / ln 2`
   (`excessCovector_re`) and whose signed phase reading is `excessCovector_im`
   (`receivingPhase_magnitude_pullback`); the implemented phase descent moves by
   `Σ_c −½ q_c Δ_c (Im R P^τ δ)_c` (`receivingPhase_phase_pullback`), whose coordinate form is the
   owner's `hasDerivAt_alignCost`. The closing period is load-bearing
   (`closing_period_is_load_bearing`).
3. **The phase cost in turns, in the cut's frame** (`alignCost_turns`): with the receiving clock
   `τ_R(j) = d_R·w + ρ_j`, `w = ⌊λ_R/d_R⌋` the cut's winding, the absolute gap is `w` plus the
   windowed gap `ρ_j/d_R − φ^H`; `w` is the branch of the log and never a magnitude of the cost,
   which is exact over `ℚ` on the windowed gap; the owner's gradient `−½ q_c Δ_c` holds there, so
   the phase covector stays at the window's scale however long the stream; a common winding
   cancels. `ρ/d` splits by `Winding.ratio_split`.
4. **The carried power** is its owner's, `Objects/Ratio/CarriedPower` (`carriedPower_exact`): in
   `ℚ(θ) = ℚ[X]/(X^L − 2)`, `θ^L = 2`; the carried power `2^n θ^k` carries by multiplication by `2`
   and multiplies with carry; `ℚ(θ)` is a field; the real chart sends `2^n θ^k` to `2^(n + k/L)`.
5. **The face is constant on the receiver's fibre** (`face_constant_on_fibre`): the grain read
   `f ↦ (⌊f⌋, ⌊L fract f⌋)` has fibre exactly the half-open cell `[n + k/L, n + (k+1)/L)` and
   `f = n + k/L + ε`, `0 ≤ ε < 1/L` (composing `Winding.split_unique`); reading every exponent
   down within its cell moves each code length `−log₂ p̂(t)` by less than `1/L` bits
   (`face_code_length_within_grain`, with `codeLength_eq_face` the owner's face), so a code
   tolerance `ε_bits` is met by `L_R = ⌈1/ε_bits⌉` (`grain_of_tolerance`; `1/16 ↦ 16`). Reading
   beyond the grain moves a code length by a whole bit (`reading_beyond_the_grain_moves_the_code`),
   and `L = 0` has no fibre bound (`grain_needs_positive_L`).

6. **The covector's odometer chart** (`odometer_covector_descends`,
   `odometer_eq_face_at_integer_cells`, `face_weight_le_odometer`): the declared masses
   `p̃_c ∝ 2^(n_c)(1 + k_c/L)` pair positively with the scored face's gradient,
   `⟨p̂ − q, p̃ − q⟩ = Σ_(c≠t) p̂_c p̃_c + (1 − p̂_t)(1 − p̃_t) > 0`, so `−(p̃ − q)` is a strict
   descent direction of the scored code length; at integer cells (`k = 0`) the chart is the
   face; inside a carry the chart's weight lies above the face's, `2^(n + k/L) ≤ 2^n(1 + k/L)`
   (Bernoulli). A single class leaves nothing to descend (`odometer_descent_needs_two_classes`).

[definition] **The real-part covector is `R⁻¹dR` read in the declared odometer chart**
`2^(n + k/L) ↦ 2^n (1 + k/L)` (design, "Exact charts"; R2 M2): rational, exact at every carry,
continuous across it and monotone. It is not the face's derivative: the face is constant on each
grain cell, so its own derivative vanishes almost everywhere. What is proved of the chart is item
6. `receivingPhase_magnitude_pullback` (item 2) is the derivative of the exact face on the logits
`f`, not of the chart; the theorems of item 2 are stated on `f`, not through the grain.
-/

noncomputable section

namespace Holonics.HNN.Ratio

open Holonics
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.Physics.InformationDifference
open Holonics.Objects.Ratio
open Holonics.Objects.RatioPhase
open Holonics.Objects.Ratio.CarriedPower
open Holonics.Aeon.Clock.Winding

/-! ## 1. A common rechart leaves the ratio -/

section Rechart

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **A common rechart leaves `ℓ_j`.** Shifting target and
produced phases by the same receiving-clock rechart leaves each channel's log ratio, keeps it in the
log fibre of the recharted amplitude pair, and leaves the lifted cross-entropy excess
(`liftedCrossEntropy_commonPhase`). -/
theorem receivingPhase_ratio (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase shift : Index → ℝ) (i : Index) :
    logRatio target produced (fun c => targetPhase c + shift c)
        (fun c => producedPhase c + shift c) i =
      logRatio target produced targetPhase producedPhase i ∧
    logRatio target produced targetPhase producedPhase i ∈
      logFibre (holonRatio (amplitude target (fun c => targetPhase c + shift c) i)
        (amplitude produced (fun c => producedPhase c + shift c) i)) ∧
    liftedCrossEntropy target produced (fun c => producedPhase c + shift c) -
        liftedCrossEntropy target target (fun c => targetPhase c + shift c) =
      liftedCrossEntropy target produced producedPhase -
        liftedCrossEntropy target target targetPhase := by
  have hℓ : logRatio target produced (fun c => targetPhase c + shift c)
      (fun c => producedPhase c + shift c) i = logRatio target produced targetPhase producedPhase i := by
    apply Complex.ext <;> simp [logRatio, liftedLog]
  refine ⟨hℓ, ?_, liftedCrossEntropy_commonPhase target produced targetPhase producedPhase shift⟩
  rw [← hℓ]
  exact logRatio_mem_logFibre _ _ _ _ i

/-- [counterexample; formal-checked] **A one-sided rechart moves the ratio.** Shifting the
produced phase alone by `s_i ≠ 0` moves the phase face of `ℓ_i` by `−s_i`: the common rechart is
load-bearing. -/
theorem produced_rechart_moves_the_ratio (target produced : PositiveProbabilitySection Index)
    (targetPhase producedPhase shift : Index → ℝ) (i : Index) (hs : shift i ≠ 0) :
    (logRatio target produced targetPhase (fun c => producedPhase c + shift c) i).im =
        (logRatio target produced targetPhase producedPhase i).im - shift i ∧
      logRatio target produced targetPhase (fun c => producedPhase c + shift c) i ≠
        logRatio target produced targetPhase producedPhase i := by
  have him : (logRatio target produced targetPhase (fun c => producedPhase c + shift c) i).im =
      (logRatio target produced targetPhase producedPhase i).im - shift i := by
    simp [logRatio, liftedLog]; ring
  refine ⟨him, fun h => hs ?_⟩
  have := congrArg Complex.im h
  linarith

end Rechart

/-! ## 2. The pullback to the receiving anchor -/

section Pullback

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- [proved-derived; formal-checked] **The covector on the receiving anchor.** For the read
`f = R (P^τ v)` with `P` the receiving ring's port isometry, every covector `g` on the logits pulls
back to `(P^τ)⁻¹ R† g` on the anchor; on a closing ring (`P^d = 1`, `0 < d`) that inverse is the
nonnegative power `P^((d−1)τ)`, so the return needs no inverse transport. -/
theorem receivingPhase_pullback (R : V →L[ℝ] F) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (g : F) (v : V) :
    inner ℝ g (R ((P ^ τ) v)) = inner ℝ ((P ^ τ).symm (R.adjoint g)) v ∧
      ∀ d : ℕ, 0 < d → P ^ d = 1 →
        inner ℝ g (R ((P ^ τ) v)) = inner ℝ ((P ^ ((d - 1) * τ)) (R.adjoint g)) v := by
  have h1 : inner ℝ g (R ((P ^ τ) v)) = inner ℝ ((P ^ τ).symm (R.adjoint g)) v := by
    rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm,
      LinearIsometryEquiv.inner_map_eq_flip, real_inner_comm]
  refine ⟨h1, fun d hd hP => ?_⟩
  have hinv : (P ^ τ)⁻¹ = P ^ ((d - 1) * τ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_add, show τ + (d - 1) * τ = d * τ by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring, pow_mul, hP, one_pow]
  rw [h1, ← LinearIsometryEquiv.inv_def, hinv]

/-- [counterexample; formal-checked] **The closing period is load-bearing.** For the half-turn
`P = −1` on `ℝ`, `P¹ ≠ 1`, and the closing formula at the wrong period `d = 1` reads `+1` where the
pullback reads `−1`. -/
theorem closing_period_is_load_bearing :
    (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) ^ 1 ≠ 1 ∧
      inner ℝ (1 : ℝ) ((ContinuousLinearMap.id ℝ ℝ) (((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) ^ 1) 1)) ≠
        inner ℝ (((LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ) ^ ((1 - 1) * 1))
          ((ContinuousLinearMap.id ℝ ℝ).adjoint 1)) (1 : ℝ) := by
  refine ⟨fun h => ?_, ?_⟩
  · have := congrArg (fun e : ℝ ≃ₗᵢ[ℝ] ℝ => e 1) h
    simp at this
    norm_num at this
  · simp [ContinuousLinearMap.adjoint_id]
    norm_num

variable {Index : Type*} [Fintype Index] [Nonempty Index]

omit [CompleteSpace V] [Fintype Index] [Nonempty Index] in
theorem read_line (A : V →ₗ[ℝ] (Index → ℝ)) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v δ : V) (i : Index) :
    HasDerivAt (fun x : ℝ => A ((P ^ τ) (v + x • δ)) i) (A ((P ^ τ) δ) i) 0 := by
  have hfun : (fun x : ℝ => A ((P ^ τ) (v + x • δ)) i) =
      fun x => A ((P ^ τ) v) i + x * A ((P ^ τ) δ) i := by
    funext x; simp [map_add, map_smul]
  rw [hfun]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A ((P ^ τ) δ) i)).const_add (A ((P ^ τ) v) i)

omit [CompleteSpace V] in
/-- [proved-derived; formal-checked] **The magnitude and signed phase faces along the anchor.**
Moving the receiving anchor along `v + x δ` moves the produced logits by `Re R P^τ δ` and the
produced phases by `½ Im R P^τ δ`; the owner's `hasDerivAt_excess_curve` gives the excess
derivative, whose code-length face is `Σ_j (p̂_j − q_j)(Re R P^τ δ)_j / ln 2` (`excessCovector_re`:
the magnitude part `p̂ − q`, pulled back through `R` then `P^τ`) and whose signed phase reading is
`−(2/ln 2) Σ_i q_i (½ Im R P^τ δ)_i` (`excessCovector_im`). -/
theorem receivingPhase_magnitude_pullback (target : PositiveProbabilitySection Index)
    (targetPhase : Index → ℝ) (Rre Rim : V →ₗ[ℝ] (Index → ℝ)) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ)
    (v δ : V) :
    ∃ D : ℂ,
      HasDerivAt (fun x : ℝ => liftedCrossEntropy target (face (Rre ((P ^ τ) (v + x • δ))))
          (fun i => Rim ((P ^ τ) (v + x • δ)) i / 2) -
            liftedCrossEntropy target target targetPhase) D 0 ∧
        D.re = (∑ j, ((face (Rre ((P ^ τ) v))).mass j - target.mass j) *
          Rre ((P ^ τ) δ) j) / Real.log 2 ∧
        D.im = -(2 / Real.log 2) * ∑ i, target.mass i * (Rim ((P ^ τ) δ) i / 2) := by
  have hs : ∀ i, HasDerivAt (fun x : ℝ => Rre ((P ^ τ) (v + x • δ)) i) (Rre ((P ^ τ) δ) i) 0 :=
    read_line Rre P τ v δ
  have hφ : ∀ i, HasDerivAt (fun x : ℝ => Rim ((P ^ τ) (v + x • δ)) i / 2)
      (Rim ((P ^ τ) δ) i / 2) 0 := fun i => (read_line Rim P τ v δ i).div_const 2
  have hD := hasDerivAt_excess_curve (s := fun x => Rre ((P ^ τ) (v + x • δ)))
    (φ := fun x i => Rim ((P ^ τ) (v + x • δ)) i / 2) target targetPhase hs hφ
  refine ⟨_, hD, ?_, ?_⟩
  · rw [excessCovector_re]
    simp only [zero_smul, add_zero, expectation, ← Finset.sum_sub_distrib, sub_mul]
  · rw [excessCovector_im]

omit [Nonempty Index] [CompleteSpace V] in
/-- [proved-derived; formal-checked] **The implemented phase descent along the anchor.** Along
`v + x δ` the alignment cost `½ Σ_c q_c Δ_c²` of the imaginary logits `Im R P^τ v` moves by
`Σ_c −½ q_c Δ_c (Im R P^τ δ)_c`: the phase part `−q_c Δ_c` (per unit of `Im f / 2`), pulled back
through `R` then `P^τ`. At a coordinate direction this is the owner's `hasDerivAt_alignCost`. -/
theorem receivingPhase_phase_pullback (q φT : Index → ℝ) (Rim : V →ₗ[ℝ] (Index → ℝ))
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v δ : V) :
    HasDerivAt (fun x : ℝ => alignCost q φT (Rim ((P ^ τ) (v + x • δ))))
      (∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)) c * Rim ((P ^ τ) δ) c) 0 := by
  have hterm : ∀ c ∈ (Finset.univ : Finset Index),
      HasDerivAt (fun x : ℝ => q c * phaseGap φT (Rim ((P ^ τ) (v + x • δ))) c ^ 2)
        (q c * (2 * phaseGap φT (Rim ((P ^ τ) v)) c * (-(Rim ((P ^ τ) δ) c) / 2))) 0 := by
    intro c _
    have hgap : HasDerivAt (fun x : ℝ => phaseGap φT (Rim ((P ^ τ) (v + x • δ))) c)
        (-(Rim ((P ^ τ) δ) c) / 2) 0 := by
      have := ((read_line Rim P τ v δ c).div_const 2).const_sub (φT c)
      refine this.congr_deriv ?_
      ring
    have hsq := hgap.pow 2
    have hv : phaseGap φT (Rim ((P ^ τ) (v + (0 : ℝ) • δ))) c = phaseGap φT (Rim ((P ^ τ) v)) c := by
      simp
    rw [hv] at hsq
    refine (hsq.const_mul (q c)).congr_deriv ?_
    push_cast; ring
  have hsum := (HasDerivAt.fun_sum hterm).const_mul (1 / 2 : ℝ)
  refine hsum.congr_deriv ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

end Pullback

/-! ## 3. The phase cost in turns -/

section Turns

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [proved-derived; formal-checked] **The receiving phase in turns, read in the cut's frame.**
The receiving clock of a `d`-step ring is `τ_i = d·w + ρ_i`, where `w = ⌊λ_R/d⌋` is the cut's
winding (the anchor's whole turns since the stream began) and `ρ_i` the lift measured from `d·w`.
The windowed target phase `ρ/d`:
* splits into its own winding `ρ / d` and open phase with `d · open = ρ mod d`
  (`Winding.ratio_split`);
* carries the stream's winding only as the branch: the absolute gap is `w` plus the windowed gap,
  `Δ^abs_c = w + (ρ_c/d − y_c/2)`, so the cut's winding is the log's branch `2πn` and never a
  magnitude of the cost;
* has an exact rational alignment cost `½ Σ_c q_c (ρ_c/d − y_c/2)²` on the windowed gap;
* has the owner's gradient `−½ q_c (ρ_c/d − y_c/2)` there (`hasDerivAt_alignCost`), so the phase
  covector stays at the scale of the window (`ρ` is the anchor's open phase plus the window's
  ticks), not of the stream's length;
* and a common winding of target and produced cancels from the windowed gap. -/
theorem alignCost_turns (d : ℕ) (hd : 0 < d) (w : ℤ) (ρ : Index → ℤ) (q y : Index → ℚ)
    (c : Index) :
    (∀ i, windings ((ρ i : ℚ) / d) = ρ i / (d : ℤ) ∧
      (d : ℚ) * openPhase ((ρ i : ℚ) / d) = ((ρ i % (d : ℤ) : ℤ) : ℚ)) ∧
    phaseGap (fun i => (((((d : ℤ) * w + ρ i : ℤ) : ℚ) / d : ℚ) : ℝ)) (fun i => (y i : ℝ)) c =
      (w : ℝ) + phaseGap (fun i => (((ρ i : ℚ) / d : ℚ) : ℝ)) (fun i => (y i : ℝ)) c ∧
    alignCost (fun i => (q i : ℝ)) (fun i => (((ρ i : ℚ) / d : ℚ) : ℝ)) (fun i => (y i : ℝ)) =
      (((1 / 2 : ℚ) * ∑ i, q i * ((ρ i : ℚ) / d - y i / 2) ^ 2 : ℚ) : ℝ) ∧
    HasDerivAt (fun t => alignCost (fun i => (q i : ℝ)) (fun i => (((ρ i : ℚ) / d : ℚ) : ℝ))
        (fun i => (y i : ℝ) + t * (Pi.single c (1 : ℝ) : Index → ℝ) i))
      (((-(1 / 2) * q c * ((ρ c : ℚ) / d - y c / 2) : ℚ) : ℝ)) 0 ∧
    ∀ n : Index → ℤ,
      phaseGap (fun i => (((ρ i : ℚ) / d : ℚ) : ℝ) + n i) (fun i => (y i : ℝ) + 2 * n i) c =
        phaseGap (fun i => (((ρ i : ℚ) / d : ℚ) : ℝ)) (fun i => (y i : ℝ)) c := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨fun i => ⟨(ratio_split (ρ i) d hd).1, (ratio_split (ρ i) d hd).2.1⟩, ?_, ?_, ?_,
    fun n => ?_⟩
  · simp only [phaseGap]
    push_cast
    field_simp
    ring
  · unfold alignCost phaseGap; push_cast; ring
  · refine (hasDerivAt_alignCost _ _ _ c).congr_deriv ?_
    unfold phaseGap; push_cast; ring
  · unfold phaseGap; ring

/-- [counterexample; formal-checked] **The period is load-bearing for the split.** At `d = 0`
the remainder identity `d · open = τ mod d` fails for `τ = 1`. -/
theorem turns_need_a_period :
    (0 : ℚ) * openPhase ((1 : ℤ) / (0 : ℕ) : ℚ) ≠ (((1 : ℤ) % ((0 : ℕ) : ℤ) : ℤ) : ℚ) := by
  simp

end Turns

/-! ## 5. The face is constant on the receiver's fibre -/

section Grain

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

/-- [definition] **The receiver's grain read** `f ↦ (n, k) = (⌊f⌋, ⌊L · fract f⌋)`. -/
def grainRead (L : ℕ) (f : K) : ℤ × ℤ := (⌊f⌋, ⌊(L : K) * Int.fract f⌋)

/-- [definition] The unresolved fibre `ε = f − n − k/L`. -/
def grainFibre (L : ℕ) (f : K) : K := f - (grainRead L f).1 - (grainRead L f).2 / L

/-- [proved-derived; formal-checked] **The face is constant on the fibre.**
* every exponent is `f = n + k/L + ε` with `0 ≤ k < L` and `0 ≤ ε < 1/L`;
* the fibre of the read over `(n, k)` is exactly the half-open cell `[n + k/L, n + (k+1)/L)`
  (composing `Winding.split_unique` for the carry `n`);
* hence every face built from `(n, k)` is constant on the fibre. -/
theorem face_constant_on_fibre {L : ℕ} (hL : 0 < L) (f : K) :
    f = (grainRead L f).1 + (grainRead L f).2 / L + grainFibre L f ∧
      0 ≤ (grainRead L f).2 ∧ (grainRead L f).2 < L ∧
      0 ≤ grainFibre L f ∧ grainFibre L f < 1 / L ∧
      (∀ (n k : ℤ) (f' : K), 0 ≤ k → k < L →
        (grainRead L f' = (n, k) ↔ (n : K) + k / L ≤ f' ∧ f' < n + (k + 1) / L)) ∧
      ∀ {Face : Type*} (face : ℤ × ℤ → Face) (f' : K),
        grainRead L f' = grainRead L f → face (grainRead L f') = face (grainRead L f) := by
  have hLpos : (0 : K) < L := by exact_mod_cast hL
  have hfr0 := Int.fract_nonneg f
  have hfr1 := Int.fract_lt_one f
  have hk0 : (0 : ℤ) ≤ ⌊(L : K) * Int.fract f⌋ := Int.floor_nonneg.mpr (by positivity)
  have hk1 : ⌊(L : K) * Int.fract f⌋ < L := by
    rw [Int.floor_lt]; push_cast; nlinarith
  have hkle := Int.floor_le ((L : K) * Int.fract f)
  have hklt := Int.lt_floor_add_one ((L : K) * Int.fract f)
  have hsplit : (⌊f⌋ : K) + Int.fract f = f := Int.floor_add_fract f
  refine ⟨by simp [grainFibre], hk0, hk1, ?_, ?_, ?_, fun _ _ h => by rw [h]⟩
  · simp only [grainFibre, grainRead]
    rw [show f - ⌊f⌋ = Int.fract f by rw [Int.fract]]
    rw [sub_nonneg, div_le_iff₀ hLpos]; linarith
  · simp only [grainFibre, grainRead]
    rw [show f - ⌊f⌋ = Int.fract f by rw [Int.fract], sub_lt_iff_lt_add, ← add_div,
      lt_div_iff₀ hLpos]
    linarith
  · intro n k f' hk0' hk1'
    have hkL : (k : K) + 1 ≤ L := by exact_mod_cast hk1'
    constructor
    · intro h
      have h1 : ⌊f'⌋ = n := congrArg Prod.fst h
      have h2 : ⌊(L : K) * Int.fract f'⌋ = k := congrArg Prod.snd h
      have hf := Int.floor_add_fract f'
      rw [h1] at hf
      have e1 := Int.floor_le ((L : K) * Int.fract f')
      have e2 := Int.lt_floor_add_one ((L : K) * Int.fract f')
      rw [h2] at e1 e2
      constructor
      · rw [← hf, add_le_add_iff_left, div_le_iff₀ hLpos]; linarith
      · rw [← hf, add_lt_add_iff_left, lt_div_iff₀ hLpos]; linarith
    · rintro ⟨hlo, hhi⟩
      have hr0 : 0 ≤ f' - n := by
        have : (0 : K) ≤ k / L := div_nonneg (by exact_mod_cast hk0') hLpos.le
        linarith
      have hr1 : f' - n < 1 := by
        have : ((k : K) + 1) / L ≤ 1 := by rw [div_le_one hLpos]; exact hkL
        linarith
      obtain ⟨hn, hr⟩ := split_unique (t := f') n (f' - n) (by ring) hr0 hr1
      have hn' : ⌊f'⌋ = n := hn.symm
      have hfr : Int.fract f' = f' - n := by rw [hr]; rfl
      simp only [grainRead, Prod.mk.injEq]
      refine ⟨hn', ?_⟩
      rw [Int.floor_eq_iff, hfr]
      constructor
      · rw [← div_le_iff₀' hLpos]; linarith
      · have : f' - n < (k + 1) / L := by linarith
        rw [lt_div_iff₀ hLpos] at this
        linarith

/-- [counterexample; formal-checked] **A positive grain is load-bearing for the fibre.** At
`L = 0` the fibre of `1/2` is `1/2`, not below `1/0 = 0`. -/
theorem grain_needs_positive_L : ¬ grainFibre (K := ℚ) 0 (1 / 2) < 1 / (0 : ℕ) := by
  simp [grainFibre, grainRead]

variable {Index : Type*} [Fintype Index]

/-- [definition] The code length of cell `t` under the face of exponents `f`:
`−log₂ p̂(t) = −f_t + log₂ Σ_c 2^(f_c)`. -/
def codeLength (f : Index → ℝ) (t : Index) : ℝ := -f t + Real.logb 2 (∑ c, (2 : ℝ) ^ f c)

theorem two_rpow_eq_exp (x : ℝ) : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num), mul_comm]

/-- [proved-derived; formal-checked] The code length is `−log₂` of the owner's normalized face at
the potentials `f ln 2`. -/
theorem codeLength_eq_face [Nonempty Index] (f : Index → ℝ) (t : Index) :
    codeLength f t = -Real.logb 2 ((face fun c => f c * Real.log 2).mass t) := by
  have hZ : 0 < ∑ c, (2 : ℝ) ^ f c :=
    Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hmass : (face fun c => f c * Real.log 2).mass t = (2 : ℝ) ^ f t / ∑ c, (2 : ℝ) ^ f c := by
    simp only [face, NormalizedExponential.partition, two_rpow_eq_exp]
  rw [hmass, Real.logb_div (by positivity) hZ.ne', codeLength, Real.logb_rpow (by norm_num)
    (by norm_num)]
  ring

/-- [proved-derived; formal-checked] **Reading every exponent down within its grain moves each
code length by less than `1/L` bits.** If `0 ≤ ε_c < 1/L` for every `c`, then
`|codeLength (f − ε) t − codeLength f t| < 1/L`. -/
theorem face_code_length_within_grain [Nonempty Index] {L : ℕ}
    (f ε : Index → ℝ) (hε0 : ∀ c, 0 ≤ ε c) (hε1 : ∀ c, ε c < 1 / L) (t : Index) :
    |codeLength (fun c => f c - ε c) t - codeLength f t| < 1 / L := by
  set S := ∑ c, (2 : ℝ) ^ f c
  set S' := ∑ c, (2 : ℝ) ^ (f c - ε c)
  have hS : 0 < S := Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hle : S' ≤ S := Finset.sum_le_sum fun c _ =>
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hε0 c])
  have hlt : (2 : ℝ) ^ (-(1 / (L : ℝ))) * S < S' := by
    rw [Finset.mul_sum]
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => ?_
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith [hε1 c])
  have hS' : 0 < S' := lt_of_le_of_lt (by positivity) hlt
  have hlog1 : Real.logb 2 S' ≤ Real.logb 2 S := Real.logb_le_logb_of_le (by norm_num) hS' hle
  have hlog2 : -(1 / (L : ℝ)) + Real.logb 2 S < Real.logb 2 S' := by
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hlt
    rwa [Real.logb_mul (by positivity) hS.ne', Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hdiff : codeLength (fun c => f c - ε c) t - codeLength f t =
      ε t + (Real.logb 2 S' - Real.logb 2 S) := by
    simp only [codeLength, S, S']; ring
  rw [hdiff, abs_lt]
  constructor <;> linarith [hε0 t, hε1 t]

/-- [counterexample; formal-checked] **Reading beyond the grain moves the code by a whole bit.**
Two classes at exponent `0`, one read down by `2 ≥ 1/1`: the code length of that class moves by
`1 + log₂(5/4) ≥ 1`, so the bound `ε < 1/L` of `face_code_length_within_grain` is load-bearing. -/
theorem reading_beyond_the_grain_moves_the_code :
    1 ≤ |codeLength (fun c => (fun _ : Bool => (0 : ℝ)) c -
        (fun b : Bool => if b then (2 : ℝ) else 0) c) true -
      codeLength (fun _ : Bool => (0 : ℝ)) true| := by
  have h4 : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
    rw [Real.rpow_neg (by norm_num)]; norm_num
  have hval : codeLength (fun c => (fun _ : Bool => (0 : ℝ)) c -
        (fun b : Bool => if b then (2 : ℝ) else 0) c) true -
      codeLength (fun _ : Bool => (0 : ℝ)) true = 1 + Real.logb 2 (5 / 4) := by
    simp only [codeLength, Fintype.sum_bool, if_true]
    norm_num [h4]
    ring
  rw [hval]
  have : 0 < Real.logb 2 (5 / 4) := Real.logb_pos (by norm_num) (by norm_num)
  rw [abs_of_pos (by linarith)]
  linarith

/-- [proved-derived; formal-checked] **The grain from the code tolerance** (R2 M2): for a declared
tolerance `ε_bits > 0`, `L_R = ⌈1/ε_bits⌉` is positive and `1/L_R ≤ ε_bits`, so every code length
read at that grain is within `ε_bits`; campaign 1's `1/16` bit gives `L_R = 16`. -/
theorem grain_of_tolerance (εbits : ℝ) (hε : 0 < εbits) :
    0 < ⌈1 / εbits⌉₊ ∧ 1 / (⌈1 / εbits⌉₊ : ℝ) ≤ εbits ∧ ⌈1 / (1 / 16 : ℝ)⌉₊ = 16 := by
  have hpos : 0 < ⌈1 / εbits⌉₊ := Nat.ceil_pos.mpr (by positivity)
  refine ⟨hpos, ?_, by norm_num⟩
  have hc : 1 / εbits ≤ (⌈1 / εbits⌉₊ : ℝ) := Nat.le_ceil _
  have hcpos : (0 : ℝ) < ⌈1 / εbits⌉₊ := by exact_mod_cast hpos
  rw [div_le_iff₀ hcpos]
  rw [div_le_iff₀ hε] at hc
  linarith

end Grain

/-! ## 6. The covector's odometer chart -/

section Odometer

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [definition] **The odometer chart of a carried power**: `2^(n + k/L) ↦ 2^n (1 + k/L)`. It is
rational, exact at every carry (`k = 0`), continuous across one (`2^n · 2 = 2^(n+1) · 1`) and
monotone in the cell. The covector's magnitude part is read on the masses it normalizes. -/
def odometerWeight (n : ℤ) (k L : ℕ) : ℝ := (2 : ℝ) ^ n * (1 + (k : ℝ) / L)

/-- [proved-derived; formal-checked] **The odometer chart is a strict descent direction of the
scored face.** Let `p` be the exact face `p̂` and `r` the odometer masses `p̃` (both positive,
each summing to one) and `q` the one-hot target at `t`, with at least one other class. The code
length's logit gradient is `p̂ − q` (`receivingPhase_magnitude_pullback`); the declared covector
is `p̃ − q`; their pairing is `Σ_(c≠t) p̂_c p̃_c + (1 − p̂_t)(1 − p̃_t) > 0`. So a step along
`−(p̃ − q)` strictly lowers the scored code length to first order, although `p̃ − q` is not the
face's derivative. -/
theorem odometer_covector_descends (p r : Index → ℝ) (hp : ∀ c, 0 < p c) (hr : ∀ c, 0 < r c)
    (hp1 : ∑ c, p c = 1) (hr1 : ∑ c, r c = 1) (t : Index) (hc : ∃ c, c ≠ t) :
    0 < ∑ c, (p c - (Pi.single t (1 : ℝ) : Index → ℝ) c) *
      (r c - (Pi.single t (1 : ℝ) : Index → ℝ) c) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  have hpt : p t ≤ 1 := hp1 ▸ Finset.single_le_sum (fun c _ => (hp c).le) (Finset.mem_univ t)
  have hrt : r t ≤ 1 := hr1 ▸ Finset.single_le_sum (fun c _ => (hr c).le) (Finset.mem_univ t)
  have htarget : 0 ≤ (p t - (Pi.single t (1 : ℝ) : Index → ℝ) t) *
      (r t - (Pi.single t (1 : ℝ) : Index → ℝ) t) := by
    simp only [Pi.single_eq_same]
    nlinarith
  have hrest : 0 < ∑ c ∈ Finset.univ.erase t,
      (p c - (Pi.single t (1 : ℝ) : Index → ℝ) c) *
        (r c - (Pi.single t (1 : ℝ) : Index → ℝ) c) := by
    obtain ⟨c, hct⟩ := hc
    refine Finset.sum_pos (fun i hi => ?_) ⟨c, Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩⟩
    have hit : i ≠ t := (Finset.mem_erase.mp hi).1
    simp only [Pi.single_eq_of_ne hit, sub_zero]
    exact mul_pos (hp i) (hr i)
  linarith

/-- [counterexample; formal-checked] **A second class is load-bearing.** With one class the face
and the chart are both `1` and the pairing vanishes: there is nothing to descend. -/
theorem odometer_descent_needs_two_classes :
    ∑ c : Unit, ((1 : ℝ) - (Pi.single () (1 : ℝ) : Unit → ℝ) c) *
      ((1 : ℝ) - (Pi.single () (1 : ℝ) : Unit → ℝ) c) = 0 := by
  simp

omit [DecidableEq Index] in
/-- [proved-derived; formal-checked] **At integer cells the chart is the face.** With every phase
class `k_c = 0` the odometer masses `2^(n_c)(1 + 0) / Σ_d 2^(n_d)(1 + 0)` equal the face's masses
`2^(n_c) / Σ_d 2^(n_d)`. -/
theorem odometer_eq_face_at_integer_cells (n : Index → ℤ) (L : ℕ) (c : Index) :
    odometerWeight (n c) 0 L / ∑ d, odometerWeight (n d) 0 L =
      (2 : ℝ) ^ ((n c : ℤ) : ℝ) / ∑ d, (2 : ℝ) ^ ((n d : ℤ) : ℝ) := by
  simp [odometerWeight, Real.rpow_intCast]

/-- [proved-derived; formal-checked] **The chart dominates the face's weight inside a carry.** For
`k ≤ L`, `2^(n + k/L) ≤ 2^n (1 + k/L)` (Bernoulli's inequality for an exponent in `[0, 1]`): the
odometer weight lies on the chord above the face's weight and meets it at both ends of the carry. -/
theorem face_weight_le_odometer (n : ℤ) {k L : ℕ} (hL : 0 < L) (hk : k ≤ L) :
    (2 : ℝ) ^ ((n : ℝ) + (k : ℝ) / L) ≤ odometerWeight n k L := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hx0 : (0 : ℝ) ≤ (k : ℝ) / L := by positivity
  have hx1 : (k : ℝ) / L ≤ 1 := by
    rw [div_le_one hLpos]; exact_mod_cast hk
  have hbern := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hx0 hx1
  rw [Real.rpow_add (by norm_num), Real.rpow_intCast, odometerWeight]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n
  norm_num at hbern
  exact mul_le_mul_of_nonneg_left hbern h2.le

end Odometer

section Audit

#print axioms receivingPhase_ratio
#print axioms produced_rechart_moves_the_ratio
#print axioms receivingPhase_pullback
#print axioms closing_period_is_load_bearing
#print axioms receivingPhase_magnitude_pullback
#print axioms receivingPhase_phase_pullback
#print axioms alignCost_turns
#print axioms turns_need_a_period
#print axioms face_constant_on_fibre
#print axioms grain_needs_positive_L
#print axioms codeLength_eq_face
#print axioms face_code_length_within_grain
#print axioms reading_beyond_the_grain_moves_the_code
#print axioms grain_of_tolerance
#print axioms odometer_covector_descends
#print axioms odometer_descent_needs_two_classes
#print axioms odometer_eq_face_at_integer_cells
#print axioms face_weight_le_odometer

end Audit

end Holonics.HNN.Ratio

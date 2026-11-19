import Holonics.HNN.Ratio
import Holonics.HNN.Ratio.Resolution
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# HNN.AnchorGradient: the receiver's comparison pulled back to the whole anchor space

[definition] The receiving ring's anchor `v` lies in a real inner product space `V`. A read is a
continuous linear map into the Euclidean chart of the logits, `R : V →L[ℝ] EuclideanSpace ℝ Index`,
where the adjoint lives, taken after the ring's clock `P^τ`, `P : V ≃ₗᵢ[ℝ] V` (`anchorRead`). The phase
cost on the anchor is the owner's alignment cost `½ Σ_c q_c Δ_c²` of the imaginary logits `Rim (P^τ v)`
(`anchorCost`); the magnitude part is the code-length excess of the real logits `Rre (P^τ v)`
(`anchorCode`), the real part of the owner's lifted excess.

Sources. #410's box "The phase pullback beyond the anchor line" carries no more text; the reading here
is `agent-inferred`. `Holonics/HNN/Ratio.lean` item 2 proves the pullback of the receiver's comparison
to the anchor only along the anchor line `v + x δ`, as directional derivatives at `x = 0`
(`receivingPhase_magnitude_pullback`, `receivingPhase_phase_pullback`), with the adjoint identity
`⟨g, R P^τ v⟩ = ⟨(P^τ)⁻¹ R† g, v⟩` and its closing-ring form `P^((d−1)τ)` (`receivingPhase_pullback`).
`Holonics/Objects/RatioPhase.lean`'s `[open]` paragraph reads: "Lifts over higher-dimensional parameter
domains (needing simple connectivity of the domain and returning the monodromy otherwise) … are not
proved here." Beyond the line is read as: the whole derivative on the anchor space, its gradient as the
adjoint pullback, every curve through the anchor, the cost's shape along a line with the descent it
gives, and the lift over the anchor space. CLAUDE.md's laws "Learning uses the covector of a declared
comparison" and "Loss is the logarithm of a ratio of Holons" name the covector; the record that lists
the owner (its row 5) is
`research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md`.
Atlas rows served (`rg -n -i 'pullback|alignCost|anchor' docs/atlas/`): `hnn.receiving-phase-pullback`
(its line clause becomes the whole derivative), `ratio.phase-alignment-descent`,
`receiver.station-score-curvature` (`Resolution.alignCost_quadratic`, consumed by item 6),
`ratio.excess-covector-faces`, `ratio.continuous-lift` (its interval clause becomes item c) and
`holon.certified-step` (the machine's own step, which item 6 does not replace).
`HolonicsResearch/HNN/LossPhase` and `HolonicsResearch/HNN/TargetFaceDescent` read the same covector in
other charts and are not restated.

[proved-standard; formal-checked] What is proved, classical.

a. **The chain rule along a curve** (`hasDerivAt_curve_of_hasGradientAt`, `hasDerivAt_line`): a
   function with gradient `g` at `γ t` moves along a curve with velocity `γ'` at the pairing `⟨g, γ'⟩`;
   the anchor line `x ↦ v + x δ` is the curve with velocity `δ`.
b. **Completing the square** (`quadratic_min`): for `b > 0`, `c − η a² + b η²` is least at
   `η = a²/(2b)`, where it is `c − a⁴/(4b)`.
c. **The lift over a convex anchor domain** (`exists_continuous_lift_convex`,
   `continuous_lift_unique_convex`, `continuous_lift_hasFDerivAt`, `continuous_lift_anchor_space`): a
   ratio `R : V → ℂ` continuous and nonvanishing on a nonempty convex `S` (contractible, so simply
   connected, and locally path-connected) has a continuous lift `L` with `exp ∘ L = R` on `S`, through
   Mathlib's `IsCoveringMapOn.existsUnique_continuousMap_lifts` on `Complex.isCoveringMapOn_exp`; two
   continuous lifts differ by one constant `2πin`; at an interior point where `R` has the derivative
   `DR`, a continuous lift has the derivative `R⁻¹ DR`, the logarithmic derivative, read in every
   direction at once (the owner's local-branch argument of `continuous_lift_hasDerivAt`, on `V`). On
   the whole anchor space the three hold together. This answers the first half of RatioPhase's
   `[open]` paragraph for convex domains.

[proved-derived; formal-checked] What is proved, the house's joins.

1. **The two forms of a read** (`ownerRead`, `ownerRead_apply`, `ownerRead_surjective`): the owner's
   reads `V →ₗ[ℝ] (Index → ℝ)` land in the sup-norm chart, which has no inner product, so no adjoint.
   `ownerRead` follows a Euclidean read by the coordinate equivalence `WithLp.linearEquiv`, giving the
   same logits channel by channel, and on a finite-dimensional anchor space every owner's read is one.
2. **A whole derivative pulls back through the read** (`anchorRead`, `hasFDerivAt_pullback`,
   `hasGradientAt_pullback`): a face `G` on the logits with gradient `w` at `R (P^τ v)` gives
   `u ↦ G (R (P^τ u))` the derivative `δ ↦ ⟨w, R P^τ δ⟩` and the gradient `(P^τ)⁻¹ R† w`, and on a
   closing ring (`P^d = 1`, `0 < d`) the gradient `P^((d−1)τ) R† w`: the owner's
   `receivingPhase_pullback` read in every direction at once.
3. **The phase cost** (`phaseCovector`, `phaseCovector_inner`, `hasGradientAt_alignCost_euclid`,
   `anchorCost`, `hasFDerivAt_anchorCost`, `anchorPhaseGradient`, `hasGradientAt_anchorCost`): the
   owner's alignment cost has gradient `w_c = −½ q_c Δ_c` in the Euclidean chart of the imaginary
   logits; on the anchor, `v ↦ alignCost q φT (Rim (P^τ v))` has at every `v` the derivative
   `δ ↦ Σ_c −½ q_c Δ_c(v) (Rim P^τ δ)_c` and the gradient `(P^τ)⁻¹ Rim† w(v)`, or
   `P^((d−1)τ) Rim† w(v)` on a closing ring.
4. **The magnitude part** (`codeExcess`, `codeExcess_eq_re`, `crossEntropy_face`, `magnitudeCovector`,
   `magnitudeCovector_inner`, `hasGradientAt_codeExcess_euclid`, `anchorCode`, `anchorCode_eq_re`,
   `hasFDerivAt_anchorCode`, `anchorMagnitudeGradient`, `hasGradientAt_anchorCode`): the real part of
   the owner's lifted excess is the code-length excess `(H(T, face s) − H(T, T))/ln 2`, whatever the
   phase reads; `H(T, face s) = log Z(s) − Σ_j T_j s_j`; its gradient in the Euclidean chart is
   `(p̂ − q)/ln 2`; on the anchor, through `Rre`, the derivative is
   `δ ↦ Σ_j (p̂_j − q_j)(Rre P^τ δ)_j / ln 2` and the gradient `(P^τ)⁻¹ Rre† (p̂ − q)/ln 2`, or the
   closing-ring power.
5. **Every curve through the anchor** (`anchorCost_along_curve`, `anchorCode_along_curve`,
   `phase_line_is_value`, `magnitude_line_is_value`): along a differentiable curve `γ` both costs move
   at `⟨∇(γ t), γ'⟩`. On the anchor line the owner's line theorems are this value at `δ`: every
   derivative of the owner's line function for the phase cost is `⟨∇, δ⟩`, which is the owner's sum;
   the real part of every derivative of the owner's lifted excess along the line is `⟨∇_mag, δ⟩`, and
   the owner's `receivingPhase_magnitude_pullback` supplies one.
6. **The phase cost is quadratic along every line, and a gradient step descends** (`lineCurvature`,
   `anchorCost_line`, `anchorDerivative_eq_inner`, `gradient_step`, `gradient_step_descends_iff`,
   `lineCurvature_le`, `gradient_step_descends`, `lineCurvature_pos`, `minimizing_step`):
   `cost(v + x δ) = cost(v) + C₁ x + C₂ x²` with `C₁ = ⟨∇, δ⟩` (item 3's derivative at `δ`) and
   `C₂ = (1/8) Σ_c q_c (Rim P^τ δ)_c²`, from `Resolution.alignCost_quadratic`. With `g = ∇`,
   `cost(v − η g) = cost(v) − η ‖g‖² + C₂(g) η²`; for `η > 0` the step lowers the cost if and only if
   `η C₂(g) < ‖g‖²`. If `q_c ≤ Q` for every channel and `0 ≤ Q`, then `C₂(g) ≤ (Q/8) ‖Rim‖² ‖g‖²`
   (`‖Rim‖` the operator norm), so for `g ≠ 0`, `0 < η` and `η (Q/8) ‖Rim‖² < 1` the step lowers the
   cost by at least `η (1 − η (Q/8) ‖Rim‖²) ‖g‖²`. With `q ≥ 0` and `g ≠ 0`, `C₂(g) > 0`, and the step
   `η* = ‖g‖²/(2 C₂(g))` is least along the gradient's line, at `cost(v) − ‖g‖⁴/(4 C₂(g))`.
7. **A witness** (`quarterTurn`, `quarterTurn_apply`, `quarterTurn_symm_apply`, `witnessWeight`,
   `witnessPhase`, `quarterTurn_witness`): on the Euclidean plane with the identity read, the
   quarter-turn `P` (`τ = 1`, `P⁴ = 1`), `q = (1/2, 1/2)`, `φT = (1, 0)` and `v = 0`, the gradient is
   `(0, 1/4)`, both as `P⁻¹ Rim† w` and as `P³ Rim† w`; the cost is `1/4`, `‖g‖² = 1/16`,
   `C₂(g) = 1/256`, `η* = 8`, and the one step `v − 8 g` lowers the cost by `1/4`, to `0`.

[open] What is not claimed.
* The moving-weight term's gradient (`RatioPhase.hasDerivAt_phaseMean_moving`): the phase cost here
  weighs by a fixed `q`.
* The grain-quantized score (constant on grain cells, `HNN/Ratio` item 6) and the odometer chart: the
  derivatives here are of the smooth faces on the logits.
* The piecewise-`C¹` integral formula `L(t) = L(a) + ∫ R′/R`, and the monodromy of a lift over a domain
  that is not simply connected (the cell holonomy of the ratio); domains that are simply connected but
  not convex are not stated either.
* Second-order terms of the excess: the code-length face is not quadratic, and its curvature bound is
  `Resolution.codeLength_quadratic_upper`, not restated.
* Reads that are linear but not continuous on an infinite-dimensional anchor space: the owner's line
  results hold for them, and the whole derivative here needs a continuous read.
* A deposition law using the step: `η*`, the bound on `η` and the descent are statements about the cost
  along the gradient's line. The machine's deposit reads the odometer covector and certifies its own
  dyadic step (`holon.certified-step`); no step here replaces it, and `8/(Q ‖Rim‖²)` is a sufficient
  range, not the largest one (the line's own range is `gradient_step_descends_iff`).
* The imaginary part of the lifted excess (the signed phase reading) is not a descent law, by the
  owner's ruling (`RatioPhase.signed_reading_is_not_alignment`); no gradient of it is stated.

The computational object is the helical pair interaction: the produced Holon and the target Holon are
a pair compared at the receiving face by their ratio, and the receiving ring's anchor is the state of
the helix whose clock `P^τ` carries the read. The covector of the pair's comparison, its phase part
`−½ q Δ` and its magnitude part `(p̂ − q)/ln 2`, is returned to the anchor by the adjoint of the read and
the inverse clock, which is a nonnegative power of the clock on a closing ring. Of the winding guide's
six general objects this touches the helix (the clock `P^τ`, the closing period `P^d = 1`, and the
lift's carry, the whole turns `2πin` by which two lifts differ), the pair (the target and produced
comparison) and faces and placement (the receiving read's phase and code-length faces, and the
gradient's placement on the anchor); cell holonomy (the monodromy left open above), the tube and the
tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.AnchorGradient

open Set Filter Topology InnerProductSpace
open Holonics
open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicInformationTheory.PositiveProbabilitySection
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.Physics.InformationDifference
open Holonics.Objects.RatioPhase
open Holonics.HNN.Ratio

/-! ## A whole derivative pulls back through the read -/

section Read

variable {V F : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- [definition] The anchor read `v ↦ R (P^τ v)` as one continuous linear map. -/
def anchorRead (R : V →L[ℝ] F) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) : V →L[ℝ] F :=
  R.comp ((P ^ τ).toContinuousLinearEquiv : V →L[ℝ] V)

/-- [definition] The anchor read applied to `v` is `R (P^τ v)`. -/
@[simp] theorem anchorRead_apply (R : V →L[ℝ] F) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) :
    anchorRead R P τ v = R ((P ^ τ) v) := rfl

/-- [proved-derived; formal-checked] A face with gradient `w` on the logits has, on the anchor, the
whole derivative `δ ↦ ⟨w, R P^τ δ⟩`. -/
theorem hasFDerivAt_pullback [CompleteSpace F] {G : F → ℝ} {w : F} (R : V →L[ℝ] F)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) (hG : HasGradientAt G w (R ((P ^ τ) v))) :
    HasFDerivAt (fun u => G (R ((P ^ τ) u))) ((toDual ℝ F w).comp (anchorRead R P τ)) v ∧
      ∀ δ, (toDual ℝ F w).comp (anchorRead R P τ) δ = inner ℝ w (R ((P ^ τ) δ)) :=
  ⟨hG.hasFDerivAt.comp v (anchorRead R P τ).hasFDerivAt, fun _ => rfl⟩

/-- [proved-derived; formal-checked] Its gradient on the anchor is `(P^τ)⁻¹ R† w`, and `P^((d−1)τ) R† w`
on a closing ring `P^d = 1`. -/
theorem hasGradientAt_pullback [CompleteSpace V] [CompleteSpace F] {G : F → ℝ} {w : F}
    (R : V →L[ℝ] F) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) (hG : HasGradientAt G w (R ((P ^ τ) v))) :
    HasGradientAt (fun u => G (R ((P ^ τ) u))) ((P ^ τ).symm (R.adjoint w)) v ∧
      ∀ d : ℕ, 0 < d → P ^ d = 1 →
        HasGradientAt (fun u => G (R ((P ^ τ) u))) ((P ^ ((d - 1) * τ)) (R.adjoint w)) v := by
  have hF := (hasFDerivAt_pullback R P τ v hG).1
  refine ⟨?_, fun d hd hP => ?_⟩
  · refine hF.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
    rw [toDual_apply_apply]
    exact (receivingPhase_pullback R P τ w δ).1
  · refine hF.congr_fderiv (ContinuousLinearMap.ext fun δ => ?_)
    rw [toDual_apply_apply]
    exact (receivingPhase_pullback R P τ w δ).2 d hd hP

end Read

/-! ## The phase cost in the Euclidean chart of the logits -/

section Phase

variable {Index : Type*} [Fintype Index]

/-- [definition] The phase covector `w_c = −½ q_c Δ_c(y)` at the imaginary logits `y`, in the Euclidean
chart. -/
def phaseCovector (q φT y : Index → ℝ) : EuclideanSpace ℝ Index :=
  WithLp.toLp 2 (fun c => -(1 / 2) * q c * phaseGap φT y c)

/-- [proved-derived; formal-checked] Pairing the phase covector with `h` is `Σ_c −½ q_c Δ_c h_c`. -/
theorem phaseCovector_inner (q φT y : Index → ℝ) (h : EuclideanSpace ℝ Index) :
    inner ℝ (phaseCovector q φT y) h = ∑ c, -(1 / 2) * q c * phaseGap φT y c * h c := by
  simp only [PiLp.inner_apply, phaseCovector, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- [proved-derived; formal-checked] The alignment cost has gradient `phaseCovector` at every point of
the Euclidean chart. -/
theorem hasGradientAt_alignCost_euclid (q φT : Index → ℝ) (y : EuclideanSpace ℝ Index) :
    HasGradientAt (fun z : EuclideanSpace ℝ Index => alignCost q φT z.ofLp)
      (phaseCovector q φT y.ofLp) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hterm : ∀ c ∈ (Finset.univ : Finset Index),
      HasFDerivAt (fun z : EuclideanSpace ℝ Index => q c * phaseGap φT z.ofLp c ^ 2)
        (q c • (((2 : ℕ) • phaseGap φT y.ofLp c ^ (2 - 1)) •
          (-((1 / 2 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) c)))) y := by
    intro c _
    have hc : HasFDerivAt (fun z : EuclideanSpace ℝ Index => z c)
        (EuclideanSpace.proj (𝕜 := ℝ) c) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) c).hasFDerivAt
    have hfun : (fun z : EuclideanSpace ℝ Index => phaseGap φT z.ofLp c) =
        fun z => φT c - 1 / 2 * z c := by
      funext z; simp only [phaseGap]; ring
    have hgap : HasFDerivAt (fun z : EuclideanSpace ℝ Index => phaseGap φT z.ofLp c)
        (-((1 / 2 : ℝ) • EuclideanSpace.proj (𝕜 := ℝ) c)) y := by
      rw [hfun]
      exact (hc.const_mul (1 / 2 : ℝ)).const_sub (φT c)
    exact (hgap.pow 2).const_mul (q c)
  have hsum := (HasFDerivAt.fun_sum hterm).const_mul (1 / 2 : ℝ)
  have hfun : (fun z : EuclideanSpace ℝ Index => alignCost q φT z.ofLp) =
      fun z => 1 / 2 * ∑ c, q c * phaseGap φT z.ofLp c ^ 2 := by
    funext z; rfl
  rw [hfun]
  refine hsum.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [toDual_apply_apply, phaseCovector_inner]
  simp [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Phase

/-! ## The magnitude part: the code-length excess in the Euclidean chart -/

section Magnitude

variable {Index : Type*} [Fintype Index] [Nonempty Index]

/-- [definition] The code-length excess at the logits `s`, in bits: `(H(T, face s) − H(T, T))/ln 2`. -/
def codeExcess (target : PositiveProbabilitySection Index) (s : Index → ℝ) : ℝ :=
  (crossEntropy target (face s) - crossEntropy target target) / Real.log 2

/-- [proved-derived; formal-checked] The code-length excess is the real part of the owner's lifted
excess, whatever the phase reads. -/
theorem codeExcess_eq_re (target : PositiveProbabilitySection Index) (s φ θ : Index → ℝ) :
    codeExcess target s =
      (liftedCrossEntropy target (face s) φ - liftedCrossEntropy target target θ).re := by
  rw [Complex.sub_re, liftedCrossEntropy_real, liftedCrossEntropy_real, codeExcess, sub_div]

/-- [proved-derived; formal-checked] `H(T, face s) = log Z(s) − Σ_j T_j s_j` (`log_face_mass`). -/
theorem crossEntropy_face (target : PositiveProbabilitySection Index) (s : Index → ℝ) :
    crossEntropy target (face s) = Real.log (partition s) - ∑ j, target.mass j * s j := by
  simp only [crossEntropy, log_face_mass, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    target.normalized, one_mul]
  ring

/-- [definition] The magnitude covector `(p̂ − q)/ln 2` at the logits `s`, in the Euclidean chart. -/
def magnitudeCovector (target : PositiveProbabilitySection Index) (s : Index → ℝ) :
    EuclideanSpace ℝ Index :=
  WithLp.toLp 2 (fun j => ((face s).mass j - target.mass j) / Real.log 2)

/-- [proved-derived; formal-checked] Pairing the magnitude covector with `h` is
`Σ_j (p̂_j − q_j) h_j / ln 2`. -/
theorem magnitudeCovector_inner (target : PositiveProbabilitySection Index) (s : Index → ℝ)
    (h : EuclideanSpace ℝ Index) :
    inner ℝ (magnitudeCovector target s) h =
      (∑ j, ((face s).mass j - target.mass j) * h j) / Real.log 2 := by
  simp only [PiLp.inner_apply, magnitudeCovector, RCLike.inner_apply, conj_trivial, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] The code-length excess has gradient `magnitudeCovector` at every
point of the Euclidean chart. -/
theorem hasGradientAt_codeExcess_euclid (target : PositiveProbabilitySection Index)
    (s : EuclideanSpace ℝ Index) :
    HasGradientAt (fun z : EuclideanSpace ℝ Index => codeExcess target z.ofLp)
      (magnitudeCovector target s.ofLp) s := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hZ : HasFDerivAt (fun z : EuclideanSpace ℝ Index => partition z.ofLp)
      (∑ j, Real.exp (s j) • EuclideanSpace.proj (𝕜 := ℝ) j) s :=
    HasFDerivAt.fun_sum fun j _ => (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.exp
  have hlin : HasFDerivAt (fun z : EuclideanSpace ℝ Index => ∑ j, target.mass j * z j)
      (∑ j, target.mass j • EuclideanSpace.proj (𝕜 := ℝ) j) s :=
    HasFDerivAt.fun_sum fun j _ => (EuclideanSpace.proj (𝕜 := ℝ) j).hasFDerivAt.const_mul _
  have hall := (((hZ.log (partition_ne_zero _)).sub hlin).sub_const
    (crossEntropy target target)).const_mul (Real.log 2)⁻¹
  have hfun : (fun z : EuclideanSpace ℝ Index => codeExcess target z.ofLp) = fun z =>
      (Real.log 2)⁻¹ * (Real.log (partition z.ofLp) - ∑ j, target.mass j * z j -
        crossEntropy target target) := by
    funext z; rw [codeExcess, crossEntropy_face, div_eq_inv_mul]
  rw [hfun]
  refine hall.congr_fderiv (ContinuousLinearMap.ext fun h => ?_)
  rw [toDual_apply_apply, magnitudeCovector_inner, div_eq_inv_mul]
  simp [face, Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, div_eq_inv_mul]
  exact Or.inl (Finset.sum_congr rfl fun i _ => by ring)

end Magnitude

/-! ## The two forms of a read, and the phase cost on the anchor space -/

section Anchor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Index : Type*} [Fintype Index]

/-- [definition] The owner's form of a Euclidean read: the read followed by the coordinate
equivalence. -/
def ownerRead (R : V →L[ℝ] EuclideanSpace ℝ Index) : V →ₗ[ℝ] (Index → ℝ) :=
  (WithLp.linearEquiv 2 ℝ (Index → ℝ)).toLinearMap ∘ₗ (R : V →ₗ[ℝ] EuclideanSpace ℝ Index)

omit [Fintype Index] in
/-- [definition] The owner's form gives the same logits channel by channel. -/
@[simp] theorem ownerRead_apply (R : V →L[ℝ] EuclideanSpace ℝ Index) (v : V) :
    ownerRead R v = (R v).ofLp := rfl

/-- [proved-derived; formal-checked] On a finite-dimensional anchor space every owner's read is the
owner's form of a Euclidean read. -/
theorem ownerRead_surjective [FiniteDimensional ℝ V] (A : V →ₗ[ℝ] (Index → ℝ)) :
    ∃ R : V →L[ℝ] EuclideanSpace ℝ Index, ownerRead R = A :=
  ⟨LinearMap.toContinuousLinearMap ((WithLp.linearEquiv 2 ℝ (Index → ℝ)).symm.toLinearMap ∘ₗ A),
    by ext v c; rfl⟩

/-- [definition] The phase cost on the anchor space: `v ↦ ½ Σ_c q_c Δ_c(Rim (P^τ v))²`. -/
def anchorCost (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V)
    (τ : ℕ) (v : V) : ℝ :=
  alignCost q φT (Rim ((P ^ τ) v)).ofLp

/-- [proved-derived; formal-checked] **The whole derivative at the anchor.** At every `v` the phase
cost has the derivative `δ ↦ Σ_c −½ q_c Δ_c(v) (Rim P^τ δ)_c`. -/
theorem hasFDerivAt_anchorCost (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) :
    HasFDerivAt (anchorCost q φT Rim P τ)
        ((toDual ℝ (EuclideanSpace ℝ Index) (phaseCovector q φT (Rim ((P ^ τ) v)).ofLp)).comp
          (anchorRead Rim P τ)) v ∧
      ∀ δ, (toDual ℝ (EuclideanSpace ℝ Index) (phaseCovector q φT (Rim ((P ^ τ) v)).ofLp)).comp
          (anchorRead Rim P τ) δ =
        ∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c * Rim ((P ^ τ) δ) c := by
  have h := hasFDerivAt_pullback Rim P τ v (hasGradientAt_alignCost_euclid q φT _)
  exact ⟨h.1, fun δ => (h.2 δ).trans (phaseCovector_inner _ _ _ _)⟩

/-- [definition] The phase cost's curvature along a direction whose logits are `h`:
`C₂ = (1/8) Σ_c q_c h_c²`. -/
def lineCurvature (q h : Index → ℝ) : ℝ := (1 / 8) * ∑ c, q c * h c ^ 2

/-- [proved-derived; formal-checked] **The phase cost is a quadratic along every line**:
`cost(v + x δ) = cost(v) + C₁ x + C₂ x²` (`Resolution.alignCost_quadratic`). -/
theorem anchorCost_line (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v δ : V) (x : ℝ) :
    anchorCost q φT Rim P τ (v + x • δ) = anchorCost q φT Rim P τ v +
      (∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c * Rim ((P ^ τ) δ) c) * x +
        lineCurvature q (Rim ((P ^ τ) δ)).ofLp * x ^ 2 := by
  have hy : (Rim ((P ^ τ) (v + x • δ))).ofLp =
      fun c => (Rim ((P ^ τ) v)).ofLp c + x * (Rim ((P ^ τ) δ)).ofLp c := by
    funext c; simp [map_add, map_smul]
  have hq := Resolution.alignCost_quadratic q φT (Rim ((P ^ τ) v)).ofLp
    (fun c => x * (Rim ((P ^ τ) δ)).ofLp c)
  have h1 : ∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c *
      (x * (Rim ((P ^ τ) δ)).ofLp c) =
      (∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c * Rim ((P ^ τ) δ) c) * x := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : 1 / 2 * ∑ c, q c / 4 * (x * (Rim ((P ^ τ) δ)).ofLp c) ^ 2 =
      lineCurvature q (Rim ((P ^ τ) δ)).ofLp * x ^ 2 := by
    rw [lineCurvature, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  unfold anchorCost
  rw [hy, hq, h1, h2]

end Anchor

/-! ## The magnitude part on the anchor space -/

section AnchorCode

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {Index : Type*} [Fintype Index] [Nonempty Index]

/-- [definition] The code-length excess on the anchor space, read through `Rre`. -/
def anchorCode (target : PositiveProbabilitySection Index) (Rre : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) : ℝ :=
  codeExcess target (Rre ((P ^ τ) v)).ofLp

/-- [proved-derived; formal-checked] It is the real part of the owner's lifted excess along the read,
for every imaginary read `Rim`. -/
theorem anchorCode_eq_re (target : PositiveProbabilitySection Index)
    (Rre Rim : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ)
    (targetPhase : Index → ℝ) (v : V) :
    anchorCode target Rre P τ v =
      (liftedCrossEntropy target (face (ownerRead Rre ((P ^ τ) v)))
          (fun i => ownerRead Rim ((P ^ τ) v) i / 2) -
        liftedCrossEntropy target target targetPhase).re :=
  codeExcess_eq_re _ _ _ _

/-- [proved-derived; formal-checked] **The magnitude part's whole derivative.** At every `v` it is
`δ ↦ Σ_j (p̂_j − q_j)(Rre P^τ δ)_j / ln 2`. -/
theorem hasFDerivAt_anchorCode (target : PositiveProbabilitySection Index)
    (Rre : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) :
    HasFDerivAt (anchorCode target Rre P τ)
        ((toDual ℝ (EuclideanSpace ℝ Index) (magnitudeCovector target (Rre ((P ^ τ) v)).ofLp)).comp
          (anchorRead Rre P τ)) v ∧
      ∀ δ, (toDual ℝ (EuclideanSpace ℝ Index)
          (magnitudeCovector target (Rre ((P ^ τ) v)).ofLp)).comp (anchorRead Rre P τ) δ =
        (∑ j, ((face (Rre ((P ^ τ) v)).ofLp).mass j - target.mass j) * Rre ((P ^ τ) δ) j) /
          Real.log 2 := by
  have h := hasFDerivAt_pullback Rre P τ v (hasGradientAt_codeExcess_euclid target _)
  exact ⟨h.1, fun δ => (h.2 δ).trans (magnitudeCovector_inner _ _ _)⟩

variable [CompleteSpace V]

/-- [definition] The magnitude gradient on the anchor, `(P^τ)⁻¹ Rre† (p̂ − q)/ln 2`. -/
def anchorMagnitudeGradient (target : PositiveProbabilitySection Index)
    (Rre : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) : V :=
  (P ^ τ).symm (Rre.adjoint (magnitudeCovector target (Rre ((P ^ τ) v)).ofLp))

/-- [proved-derived; formal-checked] **The magnitude gradient.** It is `(P^τ)⁻¹ Rre† (p̂ − q)/ln 2`, and
the closing-ring power on `P^d = 1`. -/
theorem hasGradientAt_anchorCode (target : PositiveProbabilitySection Index)
    (Rre : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) :
    HasGradientAt (anchorCode target Rre P τ) (anchorMagnitudeGradient target Rre P τ v) v ∧
      ∀ d : ℕ, 0 < d → P ^ d = 1 → HasGradientAt (anchorCode target Rre P τ)
        ((P ^ ((d - 1) * τ)) (Rre.adjoint (magnitudeCovector target (Rre ((P ^ τ) v)).ofLp))) v :=
  hasGradientAt_pullback Rre P τ v (hasGradientAt_codeExcess_euclid target _)

end AnchorCode

/-! ## The phase gradient, and the step it gives -/

section Square

/-- [proved-standard; formal-checked] Completing the square: for `b > 0`, `c − η a² + b η²` is least at
`η = a²/(2b)`, where it is `c − a⁴/(4b)`. -/
theorem quadratic_min {a b c : ℝ} (hb : 0 < b) :
    c - a ^ 2 / (2 * b) * a ^ 2 + b * (a ^ 2 / (2 * b)) ^ 2 = c - a ^ 4 / (4 * b) ∧
      ∀ η : ℝ, c - a ^ 2 / (2 * b) * a ^ 2 + b * (a ^ 2 / (2 * b)) ^ 2 ≤
        c - η * a ^ 2 + b * η ^ 2 := by
  have h1 : c - a ^ 2 / (2 * b) * a ^ 2 + b * (a ^ 2 / (2 * b)) ^ 2 = c - a ^ 4 / (4 * b) := by
    field_simp; ring
  refine ⟨h1, fun η => ?_⟩
  have key : c - η * a ^ 2 + b * η ^ 2 = c - a ^ 4 / (4 * b) + b * (η - a ^ 2 / (2 * b)) ^ 2 := by
    field_simp; ring
  rw [h1, key]
  nlinarith [mul_nonneg hb.le (sq_nonneg (η - a ^ 2 / (2 * b)))]

end Square

section Gradient

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
variable {Index : Type*} [Fintype Index]

/-- [definition] The phase gradient on the anchor, `(P^τ)⁻¹ Rim† w(v)`, `w_c = −½ q_c Δ_c(v)`. -/
def anchorPhaseGradient (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) : V :=
  (P ^ τ).symm (Rim.adjoint (phaseCovector q φT (Rim ((P ^ τ) v)).ofLp))

/-- [proved-derived; formal-checked] **The phase gradient.** The phase cost has gradient
`(P^τ)⁻¹ Rim† w(v)`, and `P^((d−1)τ) Rim† w(v)` on a closing ring `P^d = 1`. -/
theorem hasGradientAt_anchorCost (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) :
    HasGradientAt (anchorCost q φT Rim P τ) (anchorPhaseGradient q φT Rim P τ v) v ∧
      ∀ d : ℕ, 0 < d → P ^ d = 1 → HasGradientAt (anchorCost q φT Rim P τ)
        ((P ^ ((d - 1) * τ)) (Rim.adjoint (phaseCovector q φT (Rim ((P ^ τ) v)).ofLp))) v :=
  hasGradientAt_pullback Rim P τ v (hasGradientAt_alignCost_euclid q φT _)

/-- [proved-derived; formal-checked] The line coefficient `C₁` at `δ` is the pairing `⟨∇, δ⟩`. -/
theorem anchorDerivative_eq_inner (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v δ : V) :
    ∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c * Rim ((P ^ τ) δ) c =
      inner ℝ (anchorPhaseGradient q φT Rim P τ v) δ := by
  rw [← phaseCovector_inner]
  exact (receivingPhase_pullback Rim P τ _ δ).1

/-- [proved-derived; formal-checked] **A gradient step:** `cost(v − η g) = cost(v) − η ‖g‖² + C₂(g) η²`. -/
theorem gradient_step (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) (η : ℝ) :
    anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) =
      anchorCost q φT Rim P τ v - η * ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 +
        lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp * η ^ 2 := by
  have h := anchorCost_line q φT Rim P τ v (anchorPhaseGradient q φT Rim P τ v) (-η)
  rw [anchorDerivative_eq_inner, real_inner_self_eq_norm_sq, neg_smul, ← sub_eq_add_neg] at h
  rw [h]; ring

/-- [proved-derived; formal-checked] For `η > 0` the step lowers the cost if and only if
`η C₂(g) < ‖g‖²`. -/
theorem gradient_step_descends_iff (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) {η : ℝ} (hη : 0 < η) :
    anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) <
        anchorCost q φT Rim P τ v ↔
      η * lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp <
        ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 := by
  rw [gradient_step]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

omit [CompleteSpace V] in
/-- [proved-derived; formal-checked] With `q_c ≤ Q` and `0 ≤ Q`, the curvature along any `g` is at most
`(Q/8) ‖Rim‖² ‖g‖²`. -/
theorem lineCurvature_le (q : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (g : V) {Q : ℝ} (hQ : 0 ≤ Q) (hq : ∀ c, q c ≤ Q) :
    lineCurvature q (Rim ((P ^ τ) g)).ofLp ≤ Q / 8 * ‖Rim‖ ^ 2 * ‖g‖ ^ 2 := by
  have hsum : ∑ c, q c * (Rim ((P ^ τ) g)).ofLp c ^ 2 ≤ Q * ‖Rim ((P ^ τ) g)‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right (hq c) (sq_nonneg _)
  have hnorm : ‖Rim ((P ^ τ) g)‖ ≤ ‖Rim‖ * ‖g‖ := by
    have := Rim.le_opNorm ((P ^ τ) g)
    rwa [LinearIsometryEquiv.norm_map] at this
  have hsq : ‖Rim ((P ^ τ) g)‖ ^ 2 ≤ (‖Rim‖ * ‖g‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  unfold lineCurvature
  nlinarith [mul_le_mul_of_nonneg_left hsq hQ]

/-- [proved-derived; formal-checked] **A gradient step descends**: for `g ≠ 0`, `0 < η` and
`η (Q/8) ‖Rim‖² < 1` the cost falls by at least `η (1 − η (Q/8) ‖Rim‖²) ‖g‖² > 0`. -/
theorem gradient_step_descends (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) {Q η : ℝ} (hQ : 0 ≤ Q) (hq : ∀ c, q c ≤ Q) (hη : 0 < η)
    (hηQ : η * (Q / 8 * ‖Rim‖ ^ 2) < 1) (hg : anchorPhaseGradient q φT Rim P τ v ≠ 0) :
    anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) ≤
        anchorCost q φT Rim P τ v -
          η * (1 - η * (Q / 8 * ‖Rim‖ ^ 2)) * ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 ∧
      anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) <
        anchorCost q φT Rim P τ v := by
  have hC := lineCurvature_le q Rim P τ (anchorPhaseGradient q φT Rim P τ v) hQ hq
  have hg2 : 0 < ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 := by positivity
  have hle : anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) ≤
      anchorCost q φT Rim P τ v -
        η * (1 - η * (Q / 8 * ‖Rim‖ ^ 2)) * ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 := by
    rw [gradient_step]
    have := mul_le_mul_of_nonneg_left hC (sq_nonneg η)
    nlinarith
  refine ⟨hle, lt_of_le_of_lt hle ?_⟩
  have : 0 < η * (1 - η * (Q / 8 * ‖Rim‖ ^ 2)) * ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 := by
    have : 0 < 1 - η * (Q / 8 * ‖Rim‖ ^ 2) := by linarith
    positivity
  linarith

/-- [proved-derived; formal-checked] With `q ≥ 0` and a nonzero gradient, the curvature along the
gradient is positive. -/
theorem lineCurvature_pos (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V) (hq : ∀ c, 0 ≤ q c)
    (hg : anchorPhaseGradient q φT Rim P τ v ≠ 0) :
    0 < lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp := by
  have hterm : ∀ c ∈ (Finset.univ : Finset Index),
      0 ≤ q c * (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp c ^ 2 :=
    fun c _ => mul_nonneg (hq c) (sq_nonneg _)
  by_contra hne
  have hzero : ∑ c, q c * (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp c ^ 2 = 0 := by
    have h0 := Finset.sum_nonneg hterm
    unfold lineCurvature at hne
    linarith
  have hc : ∀ c, q c * (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp c = 0 := by
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero c (Finset.mem_univ c)
    rcases mul_eq_zero.mp this with h1 | h1
    · rw [h1, zero_mul]
    · rw [pow_eq_zero_iff two_ne_zero] at h1; rw [h1, mul_zero]
  have hinner := anchorDerivative_eq_inner q φT Rim P τ v (anchorPhaseGradient q φT Rim P τ v)
  rw [real_inner_self_eq_norm_sq] at hinner
  have hsum : ∑ c, -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c *
      Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v)) c = 0 := by
    refine Finset.sum_eq_zero fun c _ => ?_
    calc -(1 / 2) * q c * phaseGap φT (Rim ((P ^ τ) v)).ofLp c *
          Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v)) c
        = -(1 / 2) * phaseGap φT (Rim ((P ^ τ) v)).ofLp c *
          (q c * Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v)) c) := by ring
      _ = 0 := by rw [hc c, mul_zero]
  rw [hsum] at hinner
  exact hg (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hinner.symm))

/-- [proved-derived; formal-checked] **The minimizing step** `η* = ‖g‖²/(2 C₂(g))` gives
`cost(v) − ‖g‖⁴/(4 C₂(g))`, the least cost along the gradient's line. -/
theorem minimizing_step (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v : V)
    (hC : 0 < lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp) :
    anchorCost q φT Rim P τ (v - (‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 /
        (2 * lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp)) •
          anchorPhaseGradient q φT Rim P τ v) =
        anchorCost q φT Rim P τ v - ‖anchorPhaseGradient q φT Rim P τ v‖ ^ 4 /
          (4 * lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp) ∧
      ∀ η : ℝ, anchorCost q φT Rim P τ (v - (‖anchorPhaseGradient q φT Rim P τ v‖ ^ 2 /
          (2 * lineCurvature q (Rim ((P ^ τ) (anchorPhaseGradient q φT Rim P τ v))).ofLp)) •
            anchorPhaseGradient q φT Rim P τ v) ≤
        anchorCost q φT Rim P τ (v - η • anchorPhaseGradient q φT Rim P τ v) := by
  rw [gradient_step]
  refine ⟨(quadratic_min hC).1, fun η => ?_⟩
  rw [gradient_step]
  exact (quadratic_min hC).2 η

end Gradient

/-! ## Every curve through the anchor, and the owner's line as a value -/

section Curves

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- [proved-standard; formal-checked] A function with gradient `g` at `γ t` moves along `γ` at
`⟨g, γ'⟩`. -/
theorem hasDerivAt_curve_of_hasGradientAt {G : V → ℝ} {g : V} {γ : ℝ → V} {γ' : V} {t : ℝ}
    (hG : HasGradientAt G g (γ t)) (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun x => G (γ x)) (inner ℝ g γ') t :=
  (hG.hasFDerivAt.comp_hasDerivAt t hγ).congr_deriv toDual_apply_apply

omit [CompleteSpace V] in
/-- [proved-standard; formal-checked] The anchor line `x ↦ v + x δ` has velocity `δ` at `0`. -/
theorem hasDerivAt_line (v δ : V) : HasDerivAt (fun x : ℝ => v + x • δ) δ 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add v

variable {Index : Type*} [Fintype Index]

/-- [proved-derived; formal-checked] **Every curve through the anchor**: the phase cost moves along `γ`
at `⟨∇(γ t), γ'⟩`. -/
theorem anchorCost_along_curve (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) {γ : ℝ → V} {γ' : V} {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun x => anchorCost q φT Rim P τ (γ x))
      (inner ℝ (anchorPhaseGradient q φT Rim P τ (γ t)) γ') t :=
  hasDerivAt_curve_of_hasGradientAt (hasGradientAt_anchorCost q φT Rim P τ (γ t)).1 hγ

/-- [proved-derived; formal-checked] The magnitude part moves along `γ` at `⟨∇_mag(γ t), γ'⟩`. -/
theorem anchorCode_along_curve [Nonempty Index] (target : PositiveProbabilitySection Index)
    (Rre : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) {γ : ℝ → V} {γ' : V}
    {t : ℝ} (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun x => anchorCode target Rre P τ (γ x))
      (inner ℝ (anchorMagnitudeGradient target Rre P τ (γ t)) γ') t :=
  hasDerivAt_curve_of_hasGradientAt (hasGradientAt_anchorCode target Rre P τ (γ t)).1 hγ

/-- [proved-derived; formal-checked] The owner's `receivingPhase_phase_pullback` is the whole
derivative's value at `δ`: every derivative of its line function is `⟨∇, δ⟩`, the owner's sum. -/
theorem phase_line_is_value (q φT : Index → ℝ) (Rim : V →L[ℝ] EuclideanSpace ℝ Index)
    (P : V ≃ₗᵢ[ℝ] V) (τ : ℕ) (v δ : V) :
    HasDerivAt (fun x : ℝ => alignCost q φT (ownerRead Rim ((P ^ τ) (v + x • δ))))
        (inner ℝ (anchorPhaseGradient q φT Rim P τ v) δ) 0 ∧
      ∑ c, -(1 / 2) * q c * phaseGap φT (ownerRead Rim ((P ^ τ) v)) c *
          ownerRead Rim ((P ^ τ) δ) c =
        inner ℝ (anchorPhaseGradient q φT Rim P τ v) δ ∧
      ∀ D : ℝ, HasDerivAt (fun x : ℝ => alignCost q φT (ownerRead Rim ((P ^ τ) (v + x • δ)))) D 0 →
        D = inner ℝ (anchorPhaseGradient q φT Rim P τ v) δ := by
  have h := anchorCost_along_curve q φT Rim P τ (hasDerivAt_line v δ)
  simp only [zero_smul, add_zero] at h
  exact ⟨h, anchorDerivative_eq_inner q φT Rim P τ v δ, fun D hD => hD.unique h⟩

/-- [proved-derived; formal-checked] The real part of every line derivative of the owner's lifted
excess is `⟨∇_mag, δ⟩`, and `receivingPhase_magnitude_pullback` supplies one. -/
theorem magnitude_line_is_value [Nonempty Index] (target : PositiveProbabilitySection Index)
    (targetPhase : Index → ℝ) (Rre Rim : V →L[ℝ] EuclideanSpace ℝ Index) (P : V ≃ₗᵢ[ℝ] V)
    (τ : ℕ) (v δ : V) :
    (∀ D : ℂ, HasDerivAt (fun x : ℝ => liftedCrossEntropy target
        (face (ownerRead Rre ((P ^ τ) (v + x • δ))))
          (fun i => ownerRead Rim ((P ^ τ) (v + x • δ)) i / 2) -
        liftedCrossEntropy target target targetPhase) D 0 →
      D.re = inner ℝ (anchorMagnitudeGradient target Rre P τ v) δ) ∧
    ∃ D : ℂ, HasDerivAt (fun x : ℝ => liftedCrossEntropy target
        (face (ownerRead Rre ((P ^ τ) (v + x • δ))))
          (fun i => ownerRead Rim ((P ^ τ) (v + x • δ)) i / 2) -
        liftedCrossEntropy target target targetPhase) D 0 ∧
      D.re = inner ℝ (anchorMagnitudeGradient target Rre P τ v) δ := by
  have hall : ∀ D : ℂ, HasDerivAt (fun x : ℝ => liftedCrossEntropy target
      (face (ownerRead Rre ((P ^ τ) (v + x • δ))))
        (fun i => ownerRead Rim ((P ^ τ) (v + x • δ)) i / 2) -
      liftedCrossEntropy target target targetPhase) D 0 →
      D.re = inner ℝ (anchorMagnitudeGradient target Rre P τ v) δ := by
    intro D hD
    have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD
    have h := anchorCode_along_curve target Rre P τ (hasDerivAt_line v δ)
    simp only [zero_smul, add_zero] at h
    have hfun : (fun x : ℝ => anchorCode target Rre P τ (v + x • δ)) =
        Complex.reCLM ∘ (fun x : ℝ => liftedCrossEntropy target
          (face (ownerRead Rre ((P ^ τ) (v + x • δ))))
            (fun i => ownerRead Rim ((P ^ τ) (v + x • δ)) i / 2) -
          liftedCrossEntropy target target targetPhase) := by
      funext x
      exact anchorCode_eq_re target Rre Rim P τ targetPhase (v + x • δ)
    rw [hfun] at h
    simpa using hre.unique h
  obtain ⟨D, hD, -⟩ := receivingPhase_magnitude_pullback target targetPhase (ownerRead Rre)
    (ownerRead Rim) P τ v δ
  exact ⟨hall, D, hD, hall D hD⟩

end Curves

/-! ## A witness: the quarter-turn ring -/

section Witness

/-- [definition] The quarter-turn `(a, b) ↦ (−b, a)` of the Euclidean plane, a ring of period four. -/
def quarterTurn : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun x := !₂[-x 1, x 0]
  invFun x := !₂[x 1, -x 0]
  map_add' x y := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' c x := by ext i; fin_cases i <;> simp
  left_inv x := by ext i; fin_cases i <;> simp
  right_inv x := by ext i; fin_cases i <;> simp
  norm_map' x := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [Fin.sum_univ_two, add_comm]

/-- [definition] The quarter-turn applied: `(a, b) ↦ (−b, a)`. -/
theorem quarterTurn_apply (x : EuclideanSpace ℝ (Fin 2)) : quarterTurn x = !₂[-x 1, x 0] := rfl

/-- [definition] Its inverse applied: `(a, b) ↦ (b, −a)`. -/
theorem quarterTurn_symm_apply (x : EuclideanSpace ℝ (Fin 2)) :
    quarterTurn.symm x = !₂[x 1, -x 0] := rfl

/-- [definition] The witness's target weights `q = (1/2, 1/2)`. -/
def witnessWeight : Fin 2 → ℝ := fun _ => 1 / 2

/-- [definition] The witness's target phases `φT = (1, 0)`. -/
def witnessPhase : Fin 2 → ℝ := ![1, 0]

/-- [proved-derived; formal-checked] **Witness.** On the quarter-turn ring (`P⁴ = 1`) at `v = 0` the
gradient is `(0, 1/4)` in both forms, `η* = 8`, and one step lowers the cost from `1/4` to `0`. -/
theorem quarterTurn_witness :
    quarterTurn ^ 4 = 1 ∧
    anchorPhaseGradient witnessWeight witnessPhase (ContinuousLinearMap.id ℝ _) quarterTurn 1 0 =
      !₂[0, 1 / 4] ∧
    (quarterTurn ^ ((4 - 1) * 1)) ((ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))).adjoint
      (phaseCovector witnessWeight witnessPhase
        ((ContinuousLinearMap.id ℝ _) ((quarterTurn ^ 1) 0)).ofLp)) = !₂[0, 1 / 4] ∧
    HasGradientAt (anchorCost witnessWeight witnessPhase (ContinuousLinearMap.id ℝ _) quarterTurn 1)
      !₂[0, 1 / 4] 0 ∧
    anchorCost witnessWeight witnessPhase (ContinuousLinearMap.id ℝ _) quarterTurn 1 0 = 1 / 4 ∧
    ‖(!₂[0, 1 / 4] : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 / 16 ∧
    lineCurvature witnessWeight
      ((ContinuousLinearMap.id ℝ _) ((quarterTurn ^ 1) !₂[0, 1 / 4])).ofLp = 1 / 256 ∧
    (1 / 16 : ℝ) / (2 * (1 / 256)) = 8 ∧
    anchorCost witnessWeight witnessPhase (ContinuousLinearMap.id ℝ _) quarterTurn 1
      (0 - (8 : ℝ) • !₂[0, 1 / 4]) = 0 := by
  have hP : quarterTurn ^ 4 = 1 := by
    ext x i
    fin_cases i <;> simp [pow_succ, LinearIsometryEquiv.coe_mul, quarterTurn_apply]
  have hg : anchorPhaseGradient witnessWeight witnessPhase (ContinuousLinearMap.id ℝ _)
      quarterTurn 1 0 = !₂[0, 1 / 4] := by
    ext i
    fin_cases i <;> norm_num [anchorPhaseGradient, quarterTurn_symm_apply, phaseCovector, phaseGap,
      witnessWeight, witnessPhase, ContinuousLinearMap.adjoint_id]
  refine ⟨hP, hg, ?_, ?_, ?_, ?_, ?_, by norm_num, ?_⟩
  · ext i
    fin_cases i <;> norm_num [pow_succ, LinearIsometryEquiv.coe_mul, quarterTurn_apply,
      phaseCovector, phaseGap, witnessWeight, witnessPhase, ContinuousLinearMap.adjoint_id]
  · rw [← hg]; exact (hasGradientAt_anchorCost _ _ _ _ _ _).1
  · norm_num [anchorCost, alignCost, phaseGap, witnessWeight, witnessPhase, Fin.sum_univ_two]
  · rw [EuclideanSpace.real_norm_sq_eq]; norm_num [Fin.sum_univ_two]
  · norm_num [lineCurvature, witnessWeight, quarterTurn_apply, Fin.sum_univ_two]
  · norm_num [anchorCost, alignCost, phaseGap, witnessWeight, witnessPhase, Fin.sum_univ_two,
      quarterTurn_apply]

end Witness

/-! ## The lift over a convex anchor domain -/

section Lift

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- [proved-standard; formal-checked] **Continuous lifts exist on a convex domain**: `exp ∘ L = R` on
`S`. -/
theorem exists_continuous_lift_convex {R : V → ℂ} {S : Set V} (hS : Convex ℝ S)
    (hne : S.Nonempty) (hR : ContinuousOn R S) (h0 : ∀ v ∈ S, R v ≠ 0) :
    ∃ L : V → ℂ, ContinuousOn L S ∧ ∀ v ∈ S, Complex.exp (L v) = R v := by
  obtain ⟨v₀, hv₀⟩ := hne
  have : Nonempty S := ⟨⟨v₀, hv₀⟩⟩
  have := hS.contractibleSpace ⟨v₀, hv₀⟩
  have := hS.locallyPathConnectedSpace
  let f : C(S, ℂ) := ⟨fun v => R v, hR.domRestrict⟩
  let a₀ : S := ⟨v₀, hv₀⟩
  have he : Complex.exp (Complex.log (R v₀)) = f a₀ := Complex.exp_log (h0 v₀ hv₀)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he
    (fun v => h0 v v.2)
  classical
  refine ⟨fun v => if h : v ∈ S then F ⟨v, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have hres : S.domRestrict (fun v => if h : v ∈ S then F ⟨v, h⟩ else 0) = F := by
      funext x; simp [Set.domRestrict, x.2]
    rw [hres]; exact F.continuous
  · intro v hv
    have := congrFun hF ⟨v, hv⟩
    simp only [Function.comp_apply] at this
    simp only [hv, dif_pos]
    exact this

/-- [proved-standard; formal-checked] **Two continuous lifts on a convex domain differ by one whole-turn
constant** `2πin`. -/
theorem continuous_lift_unique_convex {R L L' : V → ℂ} {S : Set V} (hS : Convex ℝ S)
    {v₀ : V} (hv₀ : v₀ ∈ S) (hL : ContinuousOn L S) (hL' : ContinuousOn L' S)
    (hlift : ∀ v ∈ S, Complex.exp (L v) = R v) (hlift' : ∀ v ∈ S, Complex.exp (L' v) = R v) :
    ∃ n : ℤ, ∀ v ∈ S, L' v = L v + n * (2 * Real.pi * Complex.I) := by
  have : Nonempty S := ⟨⟨v₀, hv₀⟩⟩
  have := hS.contractibleSpace ⟨v₀, hv₀⟩
  have := hS.locallyPathConnectedSpace
  obtain ⟨n, hn⟩ : ∃ n : ℤ, L' v₀ = L v₀ + n * (2 * Real.pi * Complex.I) :=
    Complex.exp_eq_exp_iff_exists_int.mp ((hlift' v₀ hv₀).trans (hlift v₀ hv₀).symm)
  refine ⟨n, ?_⟩
  have hRc : ContinuousOn R S := by
    refine (Complex.continuous_exp.comp_continuousOn hL).congr ?_
    intro v hv; exact (hlift v hv).symm
  let f : C(S, ℂ) := ⟨fun v => R v, hRc.domRestrict⟩
  let a₀ : S := ⟨v₀, hv₀⟩
  let G : C(S, ℂ) := ⟨fun v => L' v, hL'.domRestrict⟩
  let H : C(S, ℂ) :=
    ⟨fun v => L v + n * (2 * Real.pi * Complex.I), hL.domRestrict.add continuous_const⟩
  have hG : Complex.exp ∘ G = f := by funext v; exact hlift' v v.2
  have hH : Complex.exp ∘ H = f := by
    funext v
    change Complex.exp (L v + n * (2 * Real.pi * Complex.I)) = R v
    rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    exact hlift v v.2
  have he : Complex.exp (G a₀) = f a₀ := congrFun hG a₀
  have hne : ∀ v : S, f v ∈ ({0}ᶜ : Set ℂ) := by
    intro v
    change R v ≠ 0
    rw [← hlift v v.2]; exact Complex.exp_ne_zero _
  obtain ⟨F, -, huniq⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hne
  have hGF : G = F := huniq G ⟨rfl, hG⟩
  have hHF : H = F := huniq H ⟨by change L v₀ + _ = L' v₀; rw [hn], hH⟩
  intro v hv
  exact congrArg (fun F : C(S, ℂ) => F ⟨v, hv⟩) (hGF.trans hHF.symm)

/-- [proved-standard; formal-checked] **A continuous lift has the derivative `R⁻¹ DR`** at an interior
point where `R` has the derivative `DR`, in every direction at once. -/
theorem continuous_lift_hasFDerivAt {R L : V → ℂ} {S : Set V} {v : V} {R' : V →L[ℝ] ℂ}
    (hL : ContinuousOn L S) (hlift : ∀ s ∈ S, Complex.exp (L s) = R s) (hv : S ∈ 𝓝 v)
    (hR : HasFDerivAt R R' v) :
    HasFDerivAt L ((R v)⁻¹ • R') v := by
  have hLt : ContinuousAt L v := hL.continuousAt hv
  have hvS : v ∈ S := mem_of_mem_nhds hv
  have hRv : R v ≠ 0 := by rw [← hlift v hvS]; exact Complex.exp_ne_zero _
  have hw : HasFDerivAt (fun s => R s * (R v)⁻¹) ((R v)⁻¹ • R') v := hR.mul_const (R v)⁻¹
  have hw1 : R v * (R v)⁻¹ = 1 := mul_inv_cancel₀ hRv
  have hslit : R v * (R v)⁻¹ ∈ Complex.slitPlane := by rw [hw1]; exact Complex.one_mem_slitPlane
  have hlog : HasFDerivAt (Complex.log ∘ fun s => R s * (R v)⁻¹)
      ((R v * (R v)⁻¹)⁻¹ • ((R v)⁻¹ • R')) v :=
    (Complex.hasStrictDerivAt_log hslit).hasDerivAt.comp_hasFDerivAt v hw
  have hg : ContinuousAt (fun s => L s - L v - Complex.log (R s * (R v)⁻¹)) v :=
    (hLt.sub continuousAt_const).sub hlog.continuousAt
  have hgv : L v - L v - Complex.log (R v * (R v)⁻¹) = 0 := by rw [hw1]; simp
  have hgint : ∀ s ∈ S, ∃ n : ℤ,
      L s - L v - Complex.log (R s * (R v)⁻¹) = n * (2 * Real.pi * Complex.I) := by
    intro s hs
    have hRs : R s ≠ 0 := by rw [← hlift s hs]; exact Complex.exp_ne_zero _
    have hws : R s * (R v)⁻¹ ≠ 0 := mul_ne_zero hRs (inv_ne_zero hRv)
    have : Complex.exp (L s - L v - Complex.log (R s * (R v)⁻¹)) = 1 := by
      rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_log hws, hlift s hs, hlift v hvS]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp this
    exact ⟨n, by rw [hn]⟩
  have hsmall : ∀ᶠ s in 𝓝 v, ‖L s - L v - Complex.log (R s * (R v)⁻¹)‖ < 2 * Real.pi := by
    have h2 : Tendsto (fun s => ‖L s - L v - Complex.log (R s * (R v)⁻¹)‖) (𝓝 v) (𝓝 0) := by
      have := hg.norm
      rw [ContinuousAt, hgv, norm_zero] at this
      exact this
    exact h2.eventually (gt_mem_nhds (by positivity))
  have hzero : ∀ᶠ s in 𝓝 v, L s - L v - Complex.log (R s * (R v)⁻¹) = 0 := by
    filter_upwards [hsmall, hv] with s hs hsS
    obtain ⟨n, hn⟩ := hgint s hsS
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
  have heq : (fun s => L v + Complex.log (R s * (R v)⁻¹)) =ᶠ[𝓝 v] L := by
    filter_upwards [hzero] with s hs
    linear_combination -hs
  have hd : HasFDerivAt (fun s => L v + Complex.log (R s * (R v)⁻¹)) ((R v)⁻¹ • R') v := by
    refine (hlog.const_add (L v)).congr_fderiv ?_
    rw [hw1, inv_one, one_smul]
  exact hd.congr_of_eventuallyEq heq.symm

/-- [proved-standard; formal-checked] **The lift over the anchor space**: a continuous nonvanishing
ratio has a continuous lift, unique up to one `2πin`, with derivative `R⁻¹ DR` wherever `R` has one. -/
theorem continuous_lift_anchor_space {R : V → ℂ} (hR : Continuous R) (h0 : ∀ v, R v ≠ 0) :
    ∃ L : V → ℂ, Continuous L ∧ (∀ v, Complex.exp (L v) = R v) ∧
      (∀ L' : V → ℂ, Continuous L' → (∀ v, Complex.exp (L' v) = R v) →
        ∃ n : ℤ, ∀ v, L' v = L v + n * (2 * Real.pi * Complex.I)) ∧
      ∀ (v : V) (R' : V →L[ℝ] ℂ), HasFDerivAt R R' v → HasFDerivAt L ((R v)⁻¹ • R') v := by
  obtain ⟨L, hL, hlift⟩ := exists_continuous_lift_convex convex_univ univ_nonempty
    hR.continuousOn (fun v _ => h0 v)
  have hLc : Continuous L := continuousOn_univ.mp hL
  refine ⟨L, hLc, fun v => hlift v (mem_univ v), fun L' hL' hlift' => ?_, fun v R' hd => ?_⟩
  · obtain ⟨n, hn⟩ := continuous_lift_unique_convex convex_univ (mem_univ (0 : V)) hL
      hL'.continuousOn (fun v _ => hlift v (mem_univ v)) (fun v _ => hlift' v)
    exact ⟨n, fun v => hn v (mem_univ v)⟩
  · exact continuous_lift_hasFDerivAt hL hlift univ_mem hd

end Lift

end Holonics.HNN.AnchorGradient

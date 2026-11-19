import Holonics.Transport.SerialScrewChain
import Holonics.Geometry.Motion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# The serial chain's Jacobian: proper recharting, the axis, the Cayley rate and `Ad` of the prefix

The #410 boxes read: "Pair/frame and port realization (#408): proper-rotation recharting and axis
extraction; configuration, rate, storage and current chart maps at the HNN consumer; the pair-rate
form `C*J*DJC`", and "The serial-chain Jacobian (#408): Lean statement of Rust `SerialChain`'s
chain derivative (angular rate `2/(1+t²)`, `spatial_jacobian` columns as `Ad`) and its
differential/finite-flow correspondence; `Transport/SerialScrewChain` has the finite product only".
The owner `Holonics/Transport/SerialScrewChain.lean` closes its docstring with "General
proper-rotation cross-product covariance and continuous chain derivatives remain the concrete
remainder for #62", and states that "no Jacobian theorem is claimed without a supplied parameter
differential". This module states that remainder on the owner's objects (`AffineMap3`, its
`compose` and `serialPrefixes`, `cayleyZChart`) and on `Geometry/ScrewGeometry`'s `Screw` and
`velocity`.

Sources: the two boxes and the owner's closing paragraph; `docs/FORMAL_FRAMEWORK.md` ("#62 owns
the actual remaining joins: proper-rotation recharting/axis extraction; serial finite motions
compatible with their generators and Jacobian"); the record of September 21,
`2026-09-21_THE_HELICAL_PAIR_INTERACTION_IS_THE_HNN_SITE_AND_PHASE_CARRIES_CONTEXT.md`, obligations
1 ("Proper-rotation recharting and axis extraction of a screw … Lean has translation covariance
only") and 2 ("Jacobian column as the recharted generator, and the revolute/prismatic rows"); the
record of November 10, `2026-11-10_A_CHAIN_OF_JOINTS_IS_THE_CHART_OF_FRICTION_…` (atlas
`chain.wrench-pullback`, `J_i = Ad_(g_1⋯g_(i−1)) ξ_i`); the retired Rust owner
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs)):
`JointMotion::parameter_generator` (angular `axis · 2/(1 + t²)`, advance `−(angular × pivot)`),
`SerialChain::spatial_jacobian` (each column the site's generator recharted through the preceding
finite product, the prefix advanced by `joint.finite_map().followed_by(prefix)`) and
`ScrewGenerator::rechart` (`ω' = Rω`, `v' = Rv + t × ω'`, refused unless `RᵀR = 1`, `det R = 1`).
Atlas rows served: `screw.adjoint-rechart` (`Ad_(R,p)(ω, v) = (Rω, Rv + p × Rω)`,
`V_(Adξ)(Rx + p) = R V_ξ(x)`, with its improper-frame caveat), `chain.jacobian-columns` (whose
"continuous Jacobian owed (#27, #28, #62)" this module answers), `chain.wrench-pullback`,
`chain.cayley-z-chart`, `frame.cayley-rotations`, `phase.rational-phase-winding` (the Cayley
parameter is not a turn rate), `holon.cayley-isometry` (the Cayley form `(1 − tK)⁻¹(1 + tK)`),
`chain.serial-configuration` and `chain.prefix-accumulation` (consumed), `motion.chasles-screw`
(consumed: `Geometry/Motion.proper_mulVec_cross`, `proper_has_axis`, `proper_fixed_parallel`).

[proved-standard; formal-checked] What is proved, classical (the hat map `[u]×` is `crossMat u`,
its inverse reading `vee`, the axis quadrance `n = u·u`, the chart denominator `1 + n t²`).

1. **Proper-rotation recharting.** `crossMat u *ᵥ v = u × v` (`crossMat_mulVec`); for every
   orthogonal `R`, `adj R = det R · Rᵀ` (`orthogonal_adjugate`) and
   `(R u) × (R v) = det R · R (u × v)` (`orthogonal_mulVec_cross`, through
   `Motion.mulVec_cross_mulVec`); for proper `R` the hat map is covariant,
   `R [u]× Rᵀ = [R u]×` (`proper_conj_crossMat`, from `Motion.proper_mulVec_cross`) and
   `[R u]× R = R [u]×` (`proper_crossMat_mul`). A reflection reverses the cross product:
   `diag(1, 1, −1)` is orthogonal with determinant `−1` and `(R e₁) × (R e₂) = −R(e₁ × e₂) ≠
   R(e₁ × e₂)` (`reflectionZ_reverses`).
2. **Axis extraction.** A proper rotation of an ordered field's three-space has `det(R − 1) = 0`
   (`proper_det_sub_one`, from `Motion.proper_has_axis`). Its skew part reads the axis:
   `[vee(R − Rᵀ)]× = R − Rᵀ` (`crossMat_vee_sub_transpose`), and
   `R vee(R − Rᵀ) = vee(R − Rᵀ)` (`proper_skew_axis`, over any field), with
   `vee(R − Rᵀ) = (R₂₁ − R₁₂, R₀₂ − R₂₀, R₁₀ − R₀₁)`; for `R ≠ 1` it is parallel to every fixed
   vector (`proper_skew_axis_parallel`, through `Motion.proper_fixed_parallel`). It can vanish
   away from the identity: the half-turn `diag(1, −1, −1)` is proper, fixes `e₁` and has zero
   skew part (`halfTurnX_skew_zero`), so the fixed vector of `proper_has_axis` is the general axis.
3. **The Cayley chart of an axis.** With `K = [u]×`, `K³ = −n K` (`crossMat_cube`). The Rodrigues
   words `rodrigues u a b = 1 + a K + b K²` multiply in closed form (`rodrigues_mul`), commute with
   `K` (`rodrigues_mul_crossMat`), transpose to `rodrigues u (−a) b` (`rodrigues_transpose`), fix
   `u` (`rodrigues_mulVec_self`) and read `tr = 3 − 2 n b` (`rodrigues_trace`) and
   `vee(W − Wᵀ) = 2a u` (`rodrigues_skew`). The Cayley rotation
   `cayleyRot u t = 1 + (2t/(1 + nt²)) K + (2t²/(1 + nt²)) K²` is the Cayley transform of `tK`:
   `(1 − tK) C(t) = 1 + tK` (`cayleyRot_cayley`), with `det(1 ± tK) = 1 + n t²`
   (`det_one_add_smul_crossMat`, `det_one_sub_smul_crossMat`); over an ordered field it is
   orthogonal (`cayleyRot_orthogonal`) with determinant one (`cayleyRot_det`, `cayleyRot_proper`),
   fixes its axis (`cayleyRot_mulVec_axis`), reads `tr C = 1 + 2(1 − nt²)/(1 + nt²)`
   (`cayleyRot_trace`) and `vee(C − Cᵀ) = (4t/(1 + nt²)) u` (`cayleyRot_skew`). No square root
   enters: the axis need not be a unit vector.
4. **The angle reading** (over `ℝ`, unit axis). `θ(t) = 2 arctan t` has
   `cos θ = (1 − t²)/(1 + t²)`, `sin θ = 2t/(1 + t²)` (`cos_two_arctan`, `sin_two_arctan`),
   `dθ/dt = 2/(1 + t²)` (`hasDerivAt_two_arctan`), `C(t) = 1 + sin θ K + (1 − cos θ) K²`
   (`cayleyRot_angle`) and `tr C = 1 + 2 cos θ` (`cayleyRot_trace_angle`).
5. **The angular rate** (over `ℝ`, entrywise). `σ(t) = 2t/(1 + nt²)` and `γ(t) = 2t²/(1 + nt²)`
   have `σ' = ω(1 − nγ)` and `γ' = ωσ` with `ω(t) = 2/(1 + nt²)` (`hasDerivAt_chartSine`,
   `hasDerivAt_chartVersine`), so `C'(t) = ω(t) K C(t)` (`hasDerivAt_cayleyRot`); the body rate
   `C⁻¹C' = ωK` (`cayleyRot_body_rate`, with `C⁻¹ = Cᵀ`, `cayleyRot_inv`) and the spatial rate
   `C'C⁻¹ = ωK` (`cayleyRot_spatial_rate`) agree. A revolute joint about the pivot `p` moves a
   point at the velocity of the Rust parameter generator, angular `ωu` and advance `p × ωu`
   (`revolute_point_rate`).
6. **The spatial Jacobian's columns are `Ad` of the prefix.** In any normed `ℝ`-algebra, with
   `adjoint P ξ = P ξ P⁻¹`: a factor in context differentiates as `P C' S`
   (`hasDerivAt_factor`); a factor with `C' = ξ C` gives the spatial rate `Ad_P ξ` times the
   configuration (`spatial_column`), one with `C' = C ξ` the body rate `S⁻¹ ξ S`
   (`body_column`); for a list product `(pre ++ C s :: post).prod` the column is
   `Ad_(pre.prod) ξ` (`chain_spatial_column`), and `Ad_(PQ) = Ad_P ∘ Ad_Q` for units
   (`adjoint_mul`). Entrywise for real matrices (`hasDerivAt_entry_factor`): a Cayley joint behind
   a proper prefix `P` has the column `[P(ωu)]×` (`cayley_chain_column`), for a list prefix of
   proper factors too (`cayley_chain_column_list`, `proper_prod`); and behind a proper affine
   prefix `x ↦ P x + b` the joint moves a point at the velocity of the generator with angular
   `P(ωu)` through the moved pivot `P p + b` (`revolute_chain_point_rate`).

[proved-derived; formal-checked] What is proved on the owner's objects and as the house's join.

7. **The rechart is `Ad` on the owner's screws.** `rechart f ξ = (Rω, Rv + t × Rω)` for
   `f = (R, t)`; a proper chart carries velocities, `V_(rechart f ξ)(f x) = R V_ξ(x)`
   (`rechart_velocity`, from `proper_rechart_velocity` over any field); it recharts through the
   owner's ordered composition as `rechart (f.compose g) = rechart g ∘ rechart f` for proper `g`
   (`rechart_compose`, `isProper_compose`); the identity chart is neutral (`rechart_identity`) and a
   translation chart is `ScrewGeometry.translationRechart` (`rechart_translationChart`). A
   revolute generator `(ω, p × ω)` recharts to the generator of the moved axis through the moved
   pivot (`rechart_revolute`). The Rust loop's columns are the owner's serial prefixes applied to
   the joints' generators: `spatialColumns base js = zipWith rechart (serialPrefixes base fs) ξs`
   (`spatialColumns_eq_zipWith`).
8. **The owner's chart.** Over `ℚ` the Cayley rotation about `e₃` is the linear part of
   `cayleyZChart` (`cayleyRot_z`), and `σ`, `1 − γ` at `n = 1` are the owner's `cayleySin`,
   `cayleyCos` (`chartSine_one`, `one_sub_chartVersine_one`).
9. **The differential/finite-flow correspondence** (the reading is `agent-inferred`). The finite
   chart composes by tangent half-angle addition, `C(s) C(t) = C((s + t)/(1 − nst))` when
   `nst ≠ 1` (`cayleyRot_mul`, from `chart_add_sine`, `chart_add_versine`,
   `chart_den_halfAngleAdd`), `C(0) = 1` (`cayleyRot_zero`) and `C'(0) = 2K`
   (`hasDerivAt_cayleyRot_zero`). Left translation moves the parameter at the chart speed
   `∂_s (s ⊕ t)|₀ = 1 + nt²` (`hasDerivAt_halfAngleAdd`), and `ω(t)(1 + nt²) = 2`
   (`angularRate_mul_den`). Differentiating the group law at the identity fixes the rate:
   any entrywise derivative `D` of `C` at `t` equals `ω(t) K C(t)` (`cayley_rate_of_group_law`).
   The angular rate `2/(1 + nt²)` is the generator at the identity divided by the chart speed:
   the finite chart of the owner and the rate of item 5 are one flow read in two charts.

What is not claimed. No exponential of a twist is identified with a finite chart. The product
`C(s) C(t)` at `nst = 1`, where the half-angle sum leaves the finite chart, is not stated, and the
lifted winding (the Rust `RationalPhase`'s `extra_turns`) is carried on the plane of one turn in
`Geometry/CayleyTurnClock`, not here. The prismatic and general
screw joints' rows are not stated beyond the general `spatial_column`. The box's "configuration,
rate, storage and current chart maps at the HNN consumer" are not found in the tree and stay
owed; the pair-rate congruence `faceForm (J C) = Cᵀ faceForm J C` is already
`Transport/HelicalPairInteraction.faceForm_pairRatePort_congruence` (atlas
`pair.rate-port-congruence`), and its consuming decoder `C(q)` at a native contact is not built
here. The contact rows and the wrench pullback `τ = Jᵀ W` of the Rust chain are not restated.
The trace's angle is read only through `2 arctan t` for a unit axis.

The computational object is the helical pair interaction read on a serial chain: each joint is a
helix (a screw navigator whose clock is the Cayley half-angle parameter, so a constant parameter
rate is not a constant turn rate), and the chain's columns are the joints' generators carried
through the preceding finite product into the shared frame where a pair contact reads its slip
`J = [V_a | −V_b]`. Of the winding guide's six general objects it touches the helix (the circle
chart and its half-angle addition; the carry at the half-turn stays attached), the pair (the
recharted generators that a contact row consumes) and the tube (the ordered chain of joints and
its prefix accumulation); faces and placement, cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix

namespace Holonics.Transport.SerialChainJacobian

/-! ## 1. The hat map -/

section Hat
variable {K : Type*} [CommRing K]

/-- [definition] The hat map: `crossMat u` is the skew matrix `[u]×` with `[u]× v = u × v`. -/
def crossMat (u : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, -u 2, u 1; u 2, 0, -u 0; -u 1, u 0, 0]

/-- [proved-standard; formal-checked] The hat map acts as the cross product. -/
theorem crossMat_mulVec (u v : Fin 3 → K) : crossMat u *ᵥ v = u ⨯₃ v := by
  ext i
  fin_cases i <;> simp [crossMat, cross_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- [proved-standard; formal-checked] The hat matrix is skew. -/
theorem crossMat_transpose (u : Fin 3 → K) : (crossMat u)ᵀ = -crossMat u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMat]

/-- [proved-standard; formal-checked] The hat map is linear in its scalar. -/
theorem crossMat_smul (c : K) (u : Fin 3 → K) : crossMat (c • u) = c • crossMat u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMat]

/-- [definition] The vee reading of a `3 × 3` matrix: `(A₂₁, A₀₂, A₁₀)`. -/
def vee (A : Matrix (Fin 3) (Fin 3) K) : Fin 3 → K := ![A 2 1, A 0 2, A 1 0]

/-- [proved-standard; formal-checked] Vee inverts the hat map. -/
theorem vee_crossMat (u : Fin 3 → K) : vee (crossMat u) = u := by
  ext i
  fin_cases i <;> simp [vee, crossMat]

/-- [proved-standard; formal-checked] The hat map is injective. -/
theorem crossMat_injective : Function.Injective (crossMat : (Fin 3 → K) → _) := fun u v h => by
  rw [← vee_crossMat u, ← vee_crossMat v, h]

/-- [proved-standard; formal-checked] Twice the skew part is the hat of its vee reading. -/
theorem crossMat_vee_sub_transpose (A : Matrix (Fin 3) (Fin 3) K) :
    crossMat (vee (A - Aᵀ)) = A - Aᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [crossMat, vee]

/-- [proved-standard; formal-checked] The hat of `u` annihilates `u`. -/
theorem crossMat_mulVec_self (u : Fin 3 → K) : crossMat u *ᵥ u = 0 := by
  rw [crossMat_mulVec, cross_self]

/-- [proved-standard; formal-checked] `[u]×³ = −(u·u)[u]×`. -/
theorem crossMat_cube (u : Fin 3 → K) :
    crossMat u * crossMat u * crossMat u = -(u ⬝ᵥ u) • crossMat u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossMat, Matrix.mul_apply, Fin.sum_univ_three, dotProduct] <;> ring

/-- [proved-standard; formal-checked] `[u]×²` is symmetric. -/
theorem crossMat_sq_transpose (u : Fin 3 → K) :
    (crossMat u * crossMat u)ᵀ = crossMat u * crossMat u := by
  rw [Matrix.transpose_mul, crossMat_transpose, neg_mul_neg]

/-- [proved-standard; formal-checked] The hat matrix is traceless. -/
theorem trace_crossMat (u : Fin 3 → K) : (crossMat u).trace = 0 := by
  simp [crossMat, Matrix.trace_fin_three]

/-- [proved-standard; formal-checked] `tr [u]×² = −2 (u·u)`. -/
theorem trace_crossMat_sq (u : Fin 3 → K) : (crossMat u * crossMat u).trace = -2 * (u ⬝ᵥ u) := by
  simp [crossMat, Matrix.trace_fin_three, Fin.sum_univ_three, dotProduct]
  ring

/-- [proved-standard; formal-checked] `det(1 + t[u]×) = 1 + (u·u) t²`. -/
theorem det_one_add_smul_crossMat (t : K) (u : Fin 3 → K) :
    (1 + t • crossMat u).det = 1 + (u ⬝ᵥ u) * t ^ 2 := by
  simp [crossMat, Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-standard; formal-checked] `det(1 − t[u]×) = 1 + (u·u) t²`. -/
theorem det_one_sub_smul_crossMat (t : K) (u : Fin 3 → K) :
    (1 - t • crossMat u).det = 1 + (u ⬝ᵥ u) * t ^ 2 := by
  simp [crossMat, Matrix.det_fin_three, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-standard; formal-checked] The pivot form of a generator's velocity:
`a × (v + p) + p × a = a × v`. -/
theorem cross_pivot (a v p : Fin 3 → K) : a ⨯₃ (v + p) + p ⨯₃ a = a ⨯₃ v := by
  ext i
  fin_cases i <;> simp [cross_apply] <;> ring

end Hat

/-! ## 2. Proper-rotation recharting and the axis -/

section Proper
variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] An orthogonal matrix has `adj R = det R · Rᵀ`. -/
theorem orthogonal_adjugate {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1) :
    adjugate R = R.det • Rᵀ := by
  calc adjugate R = (Rᵀ * R) * adjugate R := by rw [hR, Matrix.one_mul]
    _ = R.det • Rᵀ := by rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]

/-- [proved-standard; formal-checked] An orthogonal matrix carries cross products up to its
determinant: `(R u) × (R v) = det R · R (u × v)`. -/
theorem orthogonal_mulVec_cross {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (u v : Fin 3 → K) : (R *ᵥ u) ⨯₃ (R *ᵥ v) = R.det • (R *ᵥ (u ⨯₃ v)) := by
  rw [Holonics.Geometry.Motion.mulVec_cross_mulVec, orthogonal_adjugate hR, Matrix.transpose_smul,
    Matrix.transpose_transpose, Matrix.smul_mulVec]

/-- [proved-standard; formal-checked] **The hat map is covariant under a proper rotation:**
`R [u]× Rᵀ = [R u]×`. -/
theorem proper_conj_crossMat {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (u : Fin 3 → K) : R * crossMat u * Rᵀ = crossMat (R *ᵥ u) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, crossMat_mulVec, crossMat_mulVec,
    ← Holonics.Geometry.Motion.proper_mulVec_cross hR hdet, Matrix.mulVec_mulVec, hR',
    Matrix.one_mulVec]

/-- [proved-standard; formal-checked] The intertwining form of covariance: `[R u]× R = R [u]×`. -/
theorem proper_crossMat_mul {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1) (hdet : R.det = 1)
    (u : Fin 3 → K) : crossMat (R *ᵥ u) * R = R * crossMat u := by
  rw [← proper_conj_crossMat hR hdet, Matrix.mul_assoc, hR, Matrix.mul_one]

/-- [definition] The reflection in the plane `z = 0`. -/
def reflectionZ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 1, 0; 0, 0, -1]

/-- [proved-standard; formal-checked] **A reflection reverses the cross product:** `diag(1, 1, −1)`
is orthogonal with determinant `−1`, and `(R e₁) × (R e₂) = −R(e₁ × e₂) ≠ R(e₁ × e₂)`. -/
theorem reflectionZ_reverses :
    reflectionZᵀ * reflectionZ = 1 ∧ reflectionZ.det = -1 ∧
      (reflectionZ *ᵥ ![1, 0, 0]) ⨯₃ (reflectionZ *ᵥ ![0, 1, 0]) =
        -(reflectionZ *ᵥ (![1, 0, 0] ⨯₃ ![0, 1, 0])) ∧
      (reflectionZ *ᵥ ![1, 0, 0]) ⨯₃ (reflectionZ *ᵥ ![0, 1, 0]) ≠
        reflectionZ *ᵥ (![1, 0, 0] ⨯₃ ![0, 1, 0]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [reflectionZ, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [reflectionZ, Matrix.det_fin_three]
  · ext i
    fin_cases i <;> simp [reflectionZ, cross_apply]
  · intro h
    have := congrFun h 2
    simp [reflectionZ, cross_apply] at this
    norm_num at this

/-- [proved-standard; formal-checked] **The skew part reads the axis:** a proper rotation fixes
`vee(R − Rᵀ) = (R₂₁ − R₁₂, R₀₂ − R₂₀, R₁₀ − R₀₁)`. -/
theorem proper_skew_axis {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    R *ᵥ vee (R - Rᵀ) = vee (R - Rᵀ) := by
  have hR' : R * Rᵀ = 1 := mul_eq_one_comm.1 hR
  apply crossMat_injective
  rw [← proper_conj_crossMat hR hdet, crossMat_vee_sub_transpose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, hR', Matrix.mul_one, Matrix.one_mul]

/-- [definition] The half-turn about the first axis. -/
def halfTurnX : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]

/-- [proved-standard; formal-checked] **The skew reading can vanish away from the identity:** the
half-turn `diag(1, −1, −1)` is proper, is not the identity, fixes `e₁` and has zero skew part. -/
theorem halfTurnX_skew_zero :
    halfTurnXᵀ * halfTurnX = 1 ∧ halfTurnX.det = 1 ∧ halfTurnX ≠ 1 ∧
      vee (halfTurnX - halfTurnXᵀ) = 0 ∧ halfTurnX *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [halfTurnX, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [halfTurnX, Matrix.det_fin_three]
  · intro h
    have := congrFun (congrFun h 1) 1
    simp [halfTurnX] at this
    norm_num at this
  · ext i
    fin_cases i <;> simp [halfTurnX, vee]
  · ext i
    fin_cases i <;> simp [halfTurnX]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] A proper rotation of an ordered field's three-space has
`det(R − 1) = 0`. -/
theorem proper_det_sub_one {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    (R - 1).det = 0 := by
  obtain ⟨a, ha, hRa⟩ := Holonics.Geometry.Motion.proper_has_axis hR hdet
  exact Matrix.exists_mulVec_eq_zero_iff.1
    ⟨a, ha, by rw [Matrix.sub_mulVec, Matrix.one_mulVec, hRa, sub_self]⟩

/-- [proved-standard; formal-checked] Away from the identity the skew reading is parallel to every
fixed vector: `vee(R − Rᵀ) × a = 0` when `R a = a`. -/
theorem proper_skew_axis_parallel {R : Matrix (Fin 3) (Fin 3) K} (hR : Rᵀ * R = 1)
    (hdet : R.det = 1) (hne : R ≠ 1) {a : Fin 3 → K} (ha : R *ᵥ a = a) :
    vee (R - Rᵀ) ⨯₃ a = 0 :=
  Holonics.Geometry.Motion.proper_fixed_parallel hR hdet hne (proper_skew_axis hR hdet) ha

end Proper

/-! ## 3. Rodrigues words and the Cayley chart -/

section Rodrigues
variable {K : Type*} [CommRing K]

/-- [definition] The Rodrigues word `1 + a [u]× + b [u]×²`. -/
def rodrigues (u : Fin 3 → K) (a b : K) : Matrix (Fin 3) (Fin 3) K :=
  1 + a • crossMat u + b • (crossMat u * crossMat u)

/-- [proved-standard; formal-checked] Rodrigues words about one axis multiply in closed form. -/
theorem rodrigues_mul (u : Fin 3 → K) (a b c d : K) :
    rodrigues u a b * rodrigues u c d =
      rodrigues u (a + c - (u ⬝ᵥ u) * (a * d + b * c)) (b + d + a * c - (u ⬝ᵥ u) * (b * d)) := by
  have h3 := crossMat_cube u
  have h3' : crossMat u * (crossMat u * crossMat u) = -(u ⬝ᵥ u) • crossMat u := by
    rw [← Matrix.mul_assoc, h3]
  have h4 : crossMat u * crossMat u * (crossMat u * crossMat u) =
      -(u ⬝ᵥ u) • (crossMat u * crossMat u) := by
    rw [← Matrix.mul_assoc, h3, Matrix.smul_mul]
  simp only [rodrigues, add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, h3, h3', h4]
  module

/-- [proved-standard; formal-checked] `[u]× (1 + a K + b K²) = (1 − (u·u) b) K + a K²`. -/
theorem crossMat_mul_rodrigues (u : Fin 3 → K) (a b : K) :
    crossMat u * rodrigues u a b =
      (1 - (u ⬝ᵥ u) * b) • crossMat u + a • (crossMat u * crossMat u) := by
  have h3' : crossMat u * (crossMat u * crossMat u) = -(u ⬝ᵥ u) • crossMat u := by
    rw [← Matrix.mul_assoc, crossMat_cube]
  simp only [rodrigues, mul_add, Matrix.mul_one, mul_smul_comm, h3', smul_smul]
  module

/-- [proved-standard; formal-checked] A Rodrigues word commutes with its axis's hat. -/
theorem rodrigues_mul_crossMat (u : Fin 3 → K) (a b : K) :
    rodrigues u a b * crossMat u = crossMat u * rodrigues u a b := by
  simp only [rodrigues, mul_add, add_mul, Matrix.mul_one, Matrix.one_mul, mul_smul_comm,
    smul_mul_assoc, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The transpose of a Rodrigues word reverses its sine part. -/
theorem rodrigues_transpose (u : Fin 3 → K) (a b : K) :
    (rodrigues u a b)ᵀ = rodrigues u (-a) b := by
  simp only [rodrigues, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul,
    crossMat_transpose, crossMat_sq_transpose, smul_neg, neg_smul]

/-- [proved-standard; formal-checked] The empty Rodrigues word is the identity. -/
theorem rodrigues_zero_zero (u : Fin 3 → K) : rodrigues u 0 0 = 1 := by
  simp [rodrigues]

/-- [proved-standard; formal-checked] A Rodrigues word fixes its axis. -/
theorem rodrigues_mulVec_self (u : Fin 3 → K) (a b : K) : rodrigues u a b *ᵥ u = u := by
  simp only [rodrigues, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, crossMat_mulVec_self, Matrix.mulVec_zero, smul_zero, add_zero]

/-- [proved-standard; formal-checked] The trace reading of a Rodrigues word: `3 − 2 (u·u) b`. -/
theorem rodrigues_trace (u : Fin 3 → K) (a b : K) :
    (rodrigues u a b).trace = 3 - 2 * (u ⬝ᵥ u) * b := by
  simp only [rodrigues, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, trace_crossMat,
    trace_crossMat_sq, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- [proved-standard; formal-checked] The skew reading of a Rodrigues word: `vee(W − Wᵀ) = 2a u`. -/
theorem rodrigues_skew (u : Fin 3 → K) (a b : K) :
    vee (rodrigues u a b - (rodrigues u a b)ᵀ) = (2 * a) • u := by
  apply crossMat_injective
  rw [crossMat_vee_sub_transpose, rodrigues_transpose, crossMat_smul]
  simp only [rodrigues]
  module

end Rodrigues

section Chart
variable {K : Type*} [Field K]

/-- [definition] The chart's sine coefficient `σ(t) = 2t/(1 + n t²)`, `n` the axis quadrance. -/
def chartSine (n t : K) : K := 2 * t / (1 + n * t ^ 2)

/-- [definition] The chart's versine coefficient `γ(t) = 2t²/(1 + n t²)`. -/
def chartVersine (n t : K) : K := 2 * t ^ 2 / (1 + n * t ^ 2)

/-- [definition] The angular rate of the half-angle chart, `ω(t) = 2/(1 + n t²)`. -/
def angularRate (n t : K) : K := 2 / (1 + n * t ^ 2)

/-- [definition] Tangent half-angle addition in the chart: `s ⊕ t = (s + t)/(1 − n s t)`. -/
def halfAngleAdd (n s t : K) : K := (s + t) / (1 - n * s * t)

/-- [proved-standard; formal-checked] The chart denominator in the normal form `field_simp` reads. -/
theorem chart_den_comm {n t : K} (hD : 1 + n * t ^ 2 ≠ 0) : 1 + t ^ 2 * n ≠ 0 := by
  rwa [mul_comm] at hD

/-- [proved-standard; formal-checked] The sine coefficient of the Cayley identity `(1 − tK) C = 1 + tK`. -/
theorem chart_cayley_sine {n t : K} (hD : 1 + n * t ^ 2 ≠ 0) :
    -t + chartSine n t - n * (-t * chartVersine n t + 0 * chartSine n t) = t := by
  have := chart_den_comm hD
  simp only [chartSine, chartVersine]
  field_simp
  ring

/-- [proved-standard; formal-checked] The versine coefficient of the Cayley identity. -/
theorem chart_cayley_versine (n t : K) :
    0 + chartVersine n t + -t * chartSine n t - n * (0 * chartVersine n t) = 0 := by
  simp only [chartSine, chartVersine]
  ring

/-- [proved-standard; formal-checked] The sine coefficient of `CᵀC = 1`. -/
theorem chart_orthogonal_sine (n t : K) :
    -chartSine n t + chartSine n t - n * (-chartSine n t * chartVersine n t +
      chartVersine n t * chartSine n t) = 0 := by
  ring

/-- [proved-standard; formal-checked] The versine coefficient of `CᵀC = 1`: `2γ − σ² − nγ² = 0`. -/
theorem chart_orthogonal_versine {n t : K} (hD : 1 + n * t ^ 2 ≠ 0) :
    chartVersine n t + chartVersine n t + -chartSine n t * chartSine n t -
      n * (chartVersine n t * chartVersine n t) = 0 := by
  have := chart_den_comm hD
  simp only [chartSine, chartVersine]
  field_simp
  ring

/-- [proved-standard; formal-checked] The denominator at a sum:
`1 + n (s ⊕ t)² = (1 + ns²)(1 + nt²)/(1 − nst)²`. -/
theorem chart_den_halfAngleAdd {n s t : K} (h : 1 - n * s * t ≠ 0) :
    1 + n * halfAngleAdd n s t ^ 2 = (1 + n * s ^ 2) * (1 + n * t ^ 2) / (1 - n * s * t) ^ 2 := by
  have h' : 1 - s * n * t ≠ 0 := by rwa [mul_comm n s] at h
  simp only [halfAngleAdd]
  field_simp
  ring

/-- [proved-standard; formal-checked] The sine coefficient composes by half-angle addition. -/
theorem chart_add_sine {n s t : K} (hs : 1 + n * s ^ 2 ≠ 0) (ht : 1 + n * t ^ 2 ≠ 0)
    (h : 1 - n * s * t ≠ 0) :
    chartSine n s + chartSine n t - n * (chartSine n s * chartVersine n t +
      chartVersine n s * chartSine n t) = chartSine n (halfAngleAdd n s t) := by
  have hs' := chart_den_comm hs
  have ht' := chart_den_comm ht
  have h' : 1 - s * n * t ≠ 0 := by rwa [mul_comm n s] at h
  rw [show chartSine n (halfAngleAdd n s t) =
    2 * halfAngleAdd n s t / (1 + n * halfAngleAdd n s t ^ 2) from rfl, chart_den_halfAngleAdd h]
  simp only [chartSine, chartVersine, halfAngleAdd]
  field_simp
  ring

/-- [proved-standard; formal-checked] The versine coefficient composes by half-angle addition. -/
theorem chart_add_versine {n s t : K} (hs : 1 + n * s ^ 2 ≠ 0) (ht : 1 + n * t ^ 2 ≠ 0)
    (h : 1 - n * s * t ≠ 0) :
    chartVersine n s + chartVersine n t + chartSine n s * chartSine n t -
      n * (chartVersine n s * chartVersine n t) = chartVersine n (halfAngleAdd n s t) := by
  have hs' := chart_den_comm hs
  have ht' := chart_den_comm ht
  have h' : 1 - s * n * t ≠ 0 := by rwa [mul_comm n s] at h
  rw [show chartVersine n (halfAngleAdd n s t) =
    2 * halfAngleAdd n s t ^ 2 / (1 + n * halfAngleAdd n s t ^ 2) from rfl, chart_den_halfAngleAdd h]
  simp only [chartSine, chartVersine, halfAngleAdd]
  field_simp
  ring

/-- [definition] The Cayley rotation about the axis `u` at the half-angle parameter `t`:
`1 + σ(t) [u]× + γ(t) [u]×²`, with `n = u·u`. -/
def cayleyRot (u : Fin 3 → K) (t : K) : Matrix (Fin 3) (Fin 3) K :=
  rodrigues u (chartSine (u ⬝ᵥ u) t) (chartVersine (u ⬝ᵥ u) t)

/-- [proved-standard; formal-checked] The Cayley rotation fixes its axis. -/
theorem cayleyRot_mulVec_axis (u : Fin 3 → K) (t : K) : cayleyRot u t *ᵥ u = u :=
  rodrigues_mulVec_self u _ _

/-- [proved-standard; formal-checked] The chart's origin is the identity. -/
theorem cayleyRot_zero (u : Fin 3 → K) : cayleyRot u 0 = 1 := by
  simp [cayleyRot, chartSine, chartVersine, rodrigues]

/-- [proved-standard; formal-checked] The Cayley rotation's skew reading is `2σ(t) u`. -/
theorem cayleyRot_skew (u : Fin 3 → K) (t : K) :
    vee (cayleyRot u t - (cayleyRot u t)ᵀ) = (2 * chartSine (u ⬝ᵥ u) t) • u :=
  rodrigues_skew u _ _

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] The axis quadrance is nonnegative. -/
theorem quadrance_nonneg (u : Fin 3 → K) : 0 ≤ u ⬝ᵥ u := by
  simp only [dotProduct, Fin.sum_univ_three]
  exact add_nonneg (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (mul_self_nonneg _)

/-- [proved-standard; formal-checked] The chart denominator `1 + (u·u) t²` is positive. -/
theorem chart_den_pos (u : Fin 3 → K) (t : K) : 0 < 1 + (u ⬝ᵥ u) * t ^ 2 := by
  have := quadrance_nonneg u
  positivity

/-- [proved-standard; formal-checked] **The Cayley form:** `(1 − t[u]×) C(t) = 1 + t[u]×`. -/
theorem cayleyRot_cayley (u : Fin 3 → K) (t : K) :
    (1 - t • crossMat u) * cayleyRot u t = 1 + t • crossMat u := by
  have h1 : (1 : Matrix (Fin 3) (Fin 3) K) - t • crossMat u = rodrigues u (-t) 0 := by
    simp only [rodrigues, zero_smul, add_zero, neg_smul, sub_eq_add_neg]
  have h2 : (1 : Matrix (Fin 3) (Fin 3) K) + t • crossMat u = rodrigues u t 0 := by
    simp only [rodrigues, zero_smul, add_zero]
  rw [h1, h2, cayleyRot, rodrigues_mul, chart_cayley_sine (chart_den_pos u t).ne',
    chart_cayley_versine]

/-- [proved-standard; formal-checked] The Cayley rotation is orthogonal. -/
theorem cayleyRot_orthogonal (u : Fin 3 → K) (t : K) :
    (cayleyRot u t)ᵀ * cayleyRot u t = 1 := by
  rw [cayleyRot, rodrigues_transpose, rodrigues_mul, chart_orthogonal_sine,
    chart_orthogonal_versine (chart_den_pos u t).ne', rodrigues_zero_zero]

/-- [proved-standard; formal-checked] The Cayley rotation has determinant one. -/
theorem cayleyRot_det (u : Fin 3 → K) (t : K) : (cayleyRot u t).det = 1 := by
  have hD := (chart_den_pos u t).ne'
  have h := congrArg Matrix.det (cayleyRot_cayley u t)
  rw [Matrix.det_mul, det_one_sub_smul_crossMat, det_one_add_smul_crossMat] at h
  exact (mul_eq_left₀ hD).1 h

/-- [proved-standard; formal-checked] The Cayley rotation is proper. -/
theorem cayleyRot_proper (u : Fin 3 → K) (t : K) :
    (cayleyRot u t)ᵀ * cayleyRot u t = 1 ∧ (cayleyRot u t).det = 1 :=
  ⟨cayleyRot_orthogonal u t, cayleyRot_det u t⟩

/-- [proved-standard; formal-checked] The trace reading: `tr C(t) = 1 + 2(1 − nt²)/(1 + nt²)`. -/
theorem cayleyRot_trace (u : Fin 3 → K) (t : K) :
    (cayleyRot u t).trace = 1 + 2 * ((1 - (u ⬝ᵥ u) * t ^ 2) / (1 + (u ⬝ᵥ u) * t ^ 2)) := by
  have hD := (chart_den_pos u t).ne'
  rw [cayleyRot, rodrigues_trace, chartVersine]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The finite chart's group law:**
`C(s) C(t) = C((s + t)/(1 − nst))` when `nst ≠ 1`. -/
theorem cayleyRot_mul (u : Fin 3 → K) {s t : K} (h : 1 - (u ⬝ᵥ u) * s * t ≠ 0) :
    cayleyRot u s * cayleyRot u t = cayleyRot u (halfAngleAdd (u ⬝ᵥ u) s t) := by
  rw [cayleyRot, cayleyRot, cayleyRot, rodrigues_mul,
    chart_add_sine (chart_den_pos u s).ne' (chart_den_pos u t).ne' h,
    chart_add_versine (chart_den_pos u s).ne' (chart_den_pos u t).ne' h]

end Chart

section OwnerChart
open Holonics.Transport.SerialScrewChain

/-- [proved-derived; formal-checked] At `n = 1` the sine coefficient is the owner's `cayleySin`. -/
theorem chartSine_one (q : ℚ) : chartSine 1 q = cayleySin q := by
  simp [chartSine, cayleySin]

/-- [proved-derived; formal-checked] At `n = 1`, one minus the versine is the owner's `cayleyCos`. -/
theorem one_sub_chartVersine_one (q : ℚ) : 1 - chartVersine 1 q = cayleyCos q := by
  have hD : (1 : ℚ) + q ^ 2 ≠ 0 := by positivity
  simp only [chartVersine, cayleyCos, one_mul]
  field_simp
  ring

/-- [proved-derived; formal-checked] Over `ℚ` the Cayley rotation about `e₃` is the linear part of
the owner's `cayleyZChart`. -/
theorem cayleyRot_z (q : ℚ) : cayleyRot ![0, 0, 1] q = (cayleyZChart q).linear := by
  have hD : (1 : ℚ) + q ^ 2 ≠ 0 := by positivity
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cayleyRot, rodrigues, crossMat, chartSine, chartVersine, cayleyZChart, cayleyCos,
      cayleySin, Fin.sum_univ_three, dotProduct] <;> field_simp <;> ring

end OwnerChart

/-! ## 4. The angle reading and the angular rate -/

section Angle
open Real

/-- [proved-standard; formal-checked] `cos(2 arctan t) = (1 − t²)/(1 + t²)`. -/
theorem cos_two_arctan (t : ℝ) : cos (2 * arctan t) = 1 - chartVersine 1 t := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rw [cos_two_mul, cos_arctan, div_pow, Real.sq_sqrt h.le, chartVersine]
  field_simp
  ring

/-- [proved-standard; formal-checked] `sin(2 arctan t) = 2t/(1 + t²)`. -/
theorem sin_two_arctan (t : ℝ) : sin (2 * arctan t) = chartSine 1 t := by
  have h : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hs : √(1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.2 h).ne'
  rw [sin_two_mul, sin_arctan, cos_arctan, chartSine]
  field_simp
  rw [Real.sq_sqrt h.le]

/-- [proved-standard; formal-checked] `θ(t) = 2 arctan t` has `dθ/dt = 2/(1 + t²)`. -/
theorem hasDerivAt_two_arctan (t : ℝ) :
    HasDerivAt (fun s => 2 * arctan s) (angularRate 1 t) t := by
  refine ((hasDerivAt_arctan t).const_mul (2 : ℝ)).congr_deriv ?_
  simp only [angularRate, one_mul]
  ring

/-- [proved-standard; formal-checked] For a unit axis, `C(t) = 1 + sin θ K + (1 − cos θ) K²` with
`θ = 2 arctan t`. -/
theorem cayleyRot_angle {u : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) (t : ℝ) :
    cayleyRot u t = 1 + sin (2 * arctan t) • crossMat u +
      (1 - cos (2 * arctan t)) • (crossMat u * crossMat u) := by
  rw [sin_two_arctan, cos_two_arctan, sub_sub_cancel, cayleyRot, hu, rodrigues]

/-- [proved-standard; formal-checked] For a unit axis, `tr C(t) = 1 + 2 cos(2 arctan t)`. -/
theorem cayleyRot_trace_angle {u : Fin 3 → ℝ} (hu : u ⬝ᵥ u = 1) (t : ℝ) :
    (cayleyRot u t).trace = 1 + 2 * cos (2 * arctan t) := by
  rw [cayleyRot, rodrigues_trace, hu, cos_two_arctan]
  ring

end Angle

section Rate

/-- [proved-standard; formal-checked] `σ' = ω (1 − n γ)`. -/
theorem hasDerivAt_chartSine {n t : ℝ} (hD : 1 + n * t ^ 2 ≠ 0) :
    HasDerivAt (fun s => chartSine n s) (angularRate n t * (1 - n * chartVersine n t)) t := by
  have hD' := chart_den_comm hD
  have hc : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hd : HasDerivAt (fun s : ℝ => 1 + n * s ^ 2) (n * (2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_mul n).const_add (1 : ℝ)
  refine (hc.div hd hD).congr_deriv ?_
  simp only [angularRate, chartVersine]
  field_simp

/-- [proved-standard; formal-checked] `γ' = ω σ`. -/
theorem hasDerivAt_chartVersine {n t : ℝ} (hD : 1 + n * t ^ 2 ≠ 0) :
    HasDerivAt (fun s => chartVersine n s) (angularRate n t * chartSine n t) t := by
  have hD' := chart_den_comm hD
  have hc : HasDerivAt (fun s : ℝ => 2 * s ^ 2) (2 * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul (2 : ℝ)
  have hd : HasDerivAt (fun s : ℝ => 1 + n * s ^ 2) (n * (2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).const_mul n).const_add (1 : ℝ)
  refine (hc.div hd hD).congr_deriv ?_
  simp only [angularRate, chartSine]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The chain derivative of a Cayley joint:**
`C'(t) = (2/(1 + nt²)) [u]× C(t)`, entrywise. -/
theorem hasDerivAt_cayleyRot (u : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun s => cayleyRot u s i j)
      ((angularRate (u ⬝ᵥ u) t • (crossMat u * cayleyRot u t)) i j) t := by
  have hD := (chart_den_pos u t).ne'
  have e : (fun s => cayleyRot u s i j) = fun s => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j +
      chartSine (u ⬝ᵥ u) s * crossMat u i j +
        chartVersine (u ⬝ᵥ u) s * (crossMat u * crossMat u) i j := by
    funext s
    simp [cayleyRot, rodrigues]
  rw [e]
  refine ((((hasDerivAt_chartSine hD).mul_const (crossMat u i j)).const_add
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)).add
      ((hasDerivAt_chartVersine hD).mul_const ((crossMat u * crossMat u) i j))).congr_deriv ?_
  rw [cayleyRot, crossMat_mul_rodrigues]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] The Cayley rotation's inverse is its transpose. -/
theorem cayleyRot_inv (u : Fin 3 → ℝ) (t : ℝ) : (cayleyRot u t)⁻¹ = (cayleyRot u t)ᵀ :=
  Matrix.inv_eq_left_inv (cayleyRot_orthogonal u t)

/-- [proved-standard; formal-checked] **The body rate:** `C⁻¹ C' = (2/(1 + nt²)) [u]×`. -/
theorem cayleyRot_body_rate (u : Fin 3 → ℝ) (t : ℝ) :
    (cayleyRot u t)⁻¹ * (angularRate (u ⬝ᵥ u) t • (crossMat u * cayleyRot u t)) =
      angularRate (u ⬝ᵥ u) t • crossMat u := by
  have hc : crossMat u * cayleyRot u t = cayleyRot u t * crossMat u :=
    (rodrigues_mul_crossMat _ _ _).symm
  rw [cayleyRot_inv, mul_smul_comm, hc, ← Matrix.mul_assoc, cayleyRot_orthogonal, Matrix.one_mul]

/-- [proved-standard; formal-checked] **The spatial rate:** `C' C⁻¹ = (2/(1 + nt²)) [u]×`. -/
theorem cayleyRot_spatial_rate (u : Fin 3 → ℝ) (t : ℝ) :
    (angularRate (u ⬝ᵥ u) t • (crossMat u * cayleyRot u t)) * (cayleyRot u t)⁻¹ =
      angularRate (u ⬝ᵥ u) t • crossMat u := by
  rw [cayleyRot_inv, smul_mul_assoc, Matrix.mul_assoc,
    mul_eq_one_comm.1 (cayleyRot_orthogonal u t), Matrix.mul_one]

/-- [proved-standard; formal-checked] **A revolute joint moves a point at its parameter
generator's velocity:** angular `ωu`, advance `p × ωu`, at the moved point. -/
theorem revolute_point_rate (u x p : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => (cayleyRot u s *ᵥ (x - p) + p) i)
      (((angularRate (u ⬝ᵥ u) t • u) ⨯₃ (cayleyRot u t *ᵥ (x - p) + p) +
        p ⨯₃ (angularRate (u ⬝ᵥ u) t • u)) i) t := by
  have e : (fun s => (cayleyRot u s *ᵥ (x - p) + p) i) =
      fun s => (∑ j, cayleyRot u s i j * (x - p) j) + p i := by
    funext s
    simp [Matrix.mulVec, dotProduct]
  rw [e, cross_pivot]
  refine ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hasDerivAt_cayleyRot u t i j).mul_const ((x - p) j))).add_const (p i)).congr_deriv ?_
  have hv : (angularRate (u ⬝ᵥ u) t • u) ⨯₃ (cayleyRot u t *ᵥ (x - p)) =
      (angularRate (u ⬝ᵥ u) t • (crossMat u * cayleyRot u t)) *ᵥ (x - p) := by
    rw [LinearMap.map_smul₂, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, crossMat_mulVec]
  rw [hv]
  simp [Matrix.mulVec, dotProduct]

end Rate

/-! ## 5. The spatial Jacobian's columns are `Ad` of the prefix -/

section Adjoint
variable {A : Type*} [Ring A]

/-- [definition] The adjoint action `Ad_P ξ = P ξ P⁻¹` (with `Ring.inverse`). -/
noncomputable def adjoint (P ξ : A) : A := P * ξ * Ring.inverse P

/-- [proved-standard; formal-checked] `Ad` of a product of units is the composite:
`Ad_(PQ) = Ad_P ∘ Ad_Q`. -/
theorem adjoint_mul {P Q : A} (hP : IsUnit P) (hQ : IsUnit Q) (ξ : A) :
    adjoint (P * Q) ξ = adjoint P (adjoint Q ξ) := by
  obtain ⟨p, rfl⟩ := hP
  obtain ⟨q, rfl⟩ := hQ
  rw [adjoint, adjoint, adjoint, ← Units.val_mul, Ring.inverse_unit, Ring.inverse_unit,
    Ring.inverse_unit, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  simp only [mul_assoc]

end Adjoint

section Chain
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- [proved-standard; formal-checked] A factor in context differentiates as `P C' S`. -/
theorem hasDerivAt_factor (P S : A) {C : ℝ → A} {C' : A} {t : ℝ} (hC : HasDerivAt C C' t) :
    HasDerivAt (fun s => P * C s * S) (P * C' * S) t :=
  (hC.const_mul P).mul_const S

/-- [proved-standard; formal-checked] **The spatial column is `Ad` of the prefix:** with
`C' = ξ C`, the derivative of `P C S` is `Ad_P ξ · (P C S)`. -/
theorem spatial_column {P : A} (hP : IsUnit P) (S : A) {C : ℝ → A} {ξ : A} {t : ℝ}
    (hC : HasDerivAt C (ξ * C t) t) :
    HasDerivAt (fun s => P * C s * S) (adjoint P ξ * (P * C t * S)) t := by
  refine (hasDerivAt_factor P S hC).congr_deriv ?_
  simp only [adjoint, mul_assoc]
  rw [← mul_assoc (Ring.inverse P) P, Ring.inverse_mul_cancel P hP, one_mul]

/-- [proved-standard; formal-checked] **The body column:** with `C' = C ξ`, the derivative of
`P C S` is `(P C S) · S⁻¹ ξ S`. -/
theorem body_column (P : A) {S : A} (hS : IsUnit S) {C : ℝ → A} {ξ : A} {t : ℝ}
    (hC : HasDerivAt C (C t * ξ) t) :
    HasDerivAt (fun s => P * C s * S) ((P * C t * S) * (Ring.inverse S * ξ * S)) t := by
  refine (hasDerivAt_factor P S hC).congr_deriv ?_
  simp only [mul_assoc]
  rw [← mul_assoc S (Ring.inverse S), Ring.mul_inverse_cancel S hS, one_mul]

/-- [proved-standard; formal-checked] **The chain's spatial column:** in `(pre ++ C s :: post).prod`
the column of the varying factor is `Ad_(pre.prod) ξ`. -/
theorem chain_spatial_column (pre post : List A) (hpre : IsUnit pre.prod) {C : ℝ → A} {ξ : A}
    {t : ℝ} (hC : HasDerivAt C (ξ * C t) t) :
    HasDerivAt (fun s => (pre ++ C s :: post).prod)
      (adjoint pre.prod ξ * (pre ++ C t :: post).prod) t := by
  have e : ∀ s, (pre ++ C s :: post).prod = pre.prod * C s * post.prod := fun s => by
    rw [List.prod_append, List.prod_cons, mul_assoc]
  simp only [e]
  exact spatial_column hpre _ hC

end Chain

section MatrixChain

/-- [proved-standard; formal-checked] The factor-in-context rule entrywise for real matrices. -/
theorem hasDerivAt_entry_factor {m : Type*} [Fintype m] (P S : Matrix m m ℝ)
    {C : ℝ → Matrix m m ℝ} {C' : Matrix m m ℝ} {t : ℝ}
    (hC : ∀ i j, HasDerivAt (fun s => C s i j) (C' i j) t) (i j : m) :
    HasDerivAt (fun s => (P * C s * S) i j) ((P * C' * S) i j) t := by
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum (fun b _ =>
    (HasDerivAt.fun_sum (fun a _ => (hC a b).const_mul (P i a))).mul_const (S b j))

/-- [proved-standard; formal-checked] A product of proper rotations is proper. -/
theorem proper_prod {K : Type*} [Field K] (l : List (Matrix (Fin 3) (Fin 3) K))
    (h : ∀ R ∈ l, Rᵀ * R = 1 ∧ R.det = 1) : l.prodᵀ * l.prod = 1 ∧ l.prod.det = 1 := by
  induction l with
  | nil => simp
  | cons R l ih =>
    obtain ⟨hR, hRd⟩ := h R List.mem_cons_self
    obtain ⟨hl, hld⟩ := ih fun Q hQ => h Q (List.mem_cons_of_mem R hQ)
    refine ⟨?_, ?_⟩
    · rw [List.prod_cons, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hR,
        Matrix.one_mul, hl]
    · rw [List.prod_cons, Matrix.det_mul, hRd, hld, mul_one]

/-- [proved-standard; formal-checked] **A Cayley joint's spatial column behind a proper prefix `P`
is `[P(ωu)]×`**, the prefix applied to the parameter generator's angular part. -/
theorem cayley_chain_column (P S : Matrix (Fin 3) (Fin 3) ℝ) (hP : Pᵀ * P = 1) (hdet : P.det = 1)
    (u : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun s => (P * cayleyRot u s * S) i j)
      ((crossMat (P *ᵥ (angularRate (u ⬝ᵥ u) t • u)) * (P * cayleyRot u t * S)) i j) t := by
  refine (hasDerivAt_entry_factor P S (hasDerivAt_cayleyRot u t) i j).congr_deriv ?_
  rw [Matrix.mulVec_smul, crossMat_smul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (crossMat _) P, proper_crossMat_mul hP hdet, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The Cayley joint's column behind a list prefix of proper
factors (Cayley rotations among them, `cayleyRot_proper`). -/
theorem cayley_chain_column_list (pre post : List (Matrix (Fin 3) (Fin 3) ℝ))
    (hpre : ∀ R ∈ pre, Rᵀ * R = 1 ∧ R.det = 1) (u : Fin 3 → ℝ) (t : ℝ) (i j : Fin 3) :
    HasDerivAt (fun s => (pre ++ cayleyRot u s :: post).prod i j)
      ((crossMat (pre.prod *ᵥ (angularRate (u ⬝ᵥ u) t • u)) *
        (pre ++ cayleyRot u t :: post).prod) i j) t := by
  have e : ∀ s, (pre ++ cayleyRot u s :: post).prod = pre.prod * cayleyRot u s * post.prod :=
    fun s => by rw [List.prod_append, List.prod_cons, Matrix.mul_assoc]
  simp only [e]
  obtain ⟨hP, hdet⟩ := proper_prod pre hpre
  exact cayley_chain_column _ _ hP hdet u t i j

/-- [proved-standard; formal-checked] **The column at a point:** behind a proper affine prefix
`x ↦ P x + b`, a revolute joint moves a point at the velocity of the generator with angular part
`P(ωu)` through the moved pivot `P p + b`. -/
theorem revolute_chain_point_rate (P : Matrix (Fin 3) (Fin 3) ℝ) (hP : Pᵀ * P = 1)
    (hdet : P.det = 1) (b u x p : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    HasDerivAt (fun s => (P *ᵥ (cayleyRot u s *ᵥ (x - p) + p) + b) i)
      (((P *ᵥ (angularRate (u ⬝ᵥ u) t • u)) ⨯₃ (P *ᵥ (cayleyRot u t *ᵥ (x - p) + p) + b) +
        (P *ᵥ p + b) ⨯₃ (P *ᵥ (angularRate (u ⬝ᵥ u) t • u))) i) t := by
  have e : (fun s => (P *ᵥ (cayleyRot u s *ᵥ (x - p) + p) + b) i) =
      fun s => (∑ j, P i j * (cayleyRot u s *ᵥ (x - p) + p) j) + b i := by
    funext s
    simp [Matrix.mulVec, dotProduct]
  rw [e]
  refine ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (revolute_point_rate u x p t j).const_mul (P i j))).add_const (b i)).congr_deriv ?_
  have hv : P *ᵥ (cayleyRot u t *ᵥ (x - p) + p) + b =
      P *ᵥ (cayleyRot u t *ᵥ (x - p)) + (P *ᵥ p + b) := by
    rw [Matrix.mulVec_add, add_assoc]
  rw [hv, cross_pivot, cross_pivot, Holonics.Geometry.Motion.proper_mulVec_cross hP hdet]
  simp [Matrix.mulVec, dotProduct]

end MatrixChain

/-! ## 6. The differential/finite-flow correspondence -/

section FiniteFlow

/-- [proved-standard; formal-checked] The identity is the left unit of half-angle addition. -/
theorem halfAngleAdd_zero_left (n t : ℝ) : halfAngleAdd n 0 t = t := by
  simp [halfAngleAdd]

/-- [proved-standard; formal-checked] **The chart speed of left translation:**
`∂_s (s ⊕ t)|₀ = 1 + n t²`. -/
theorem hasDerivAt_halfAngleAdd (n t : ℝ) :
    HasDerivAt (fun s => halfAngleAdd n s t) (1 + n * t ^ 2) 0 := by
  have hc : HasDerivAt (fun s : ℝ => s + t) 1 0 := (hasDerivAt_id 0).add_const t
  have hd : HasDerivAt (fun s : ℝ => 1 - n * s * t) (-(n * t)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul n).mul_const t
    simpa using this.const_sub (1 : ℝ)
  refine (hc.div hd (by simp)).congr_deriv ?_
  simp
  ring

/-- [proved-standard; formal-checked] The angular rate times the chart speed is the rate at the
identity: `ω(t)(1 + nt²) = 2`. -/
theorem angularRate_mul_den {n t : ℝ} (hD : 1 + n * t ^ 2 ≠ 0) :
    angularRate n t * (1 + n * t ^ 2) = 2 := by
  rw [angularRate, div_mul_cancel₀ _ hD]

/-- [proved-standard; formal-checked] The generator at the identity: `C'(0) = 2 [u]×`. -/
theorem hasDerivAt_cayleyRot_zero (u : Fin 3 → ℝ) (i j : Fin 3) :
    HasDerivAt (fun s => cayleyRot u s i j) (((2 : ℝ) • crossMat u) i j) 0 := by
  refine (hasDerivAt_cayleyRot u 0 i j).congr_deriv ?_
  simp [angularRate, cayleyRot_zero]

/-- [proved-derived; formal-checked] **The group law fixes the rate:** any entrywise derivative of
the Cayley chart at `t` is `(2/(1 + nt²)) [u]× C(t)`, read from `C(s ⊕ t) = C(s) C(t)` at `s = 0`. -/
theorem cayley_rate_of_group_law (u : Fin 3 → ℝ) (t : ℝ) {D : Matrix (Fin 3) (Fin 3) ℝ}
    (hD : ∀ i j, HasDerivAt (fun s => cayleyRot u s i j) (D i j) t) :
    D = angularRate (u ⬝ᵥ u) t • (crossMat u * cayleyRot u t) := by
  ext i j
  have hden := (chart_den_pos u t).ne'
  have h1 : HasDerivAt (fun s => cayleyRot u (halfAngleAdd (u ⬝ᵥ u) s t) i j)
      (D i j * (1 + (u ⬝ᵥ u) * t ^ 2)) 0 :=
    (hD i j).comp_of_eq 0 (hasDerivAt_halfAngleAdd (u ⬝ᵥ u) t) (halfAngleAdd_zero_left _ t).symm
  have h2 : HasDerivAt (fun s => (cayleyRot u s * cayleyRot u t) i j)
      (((2 : ℝ) • crossMat u * cayleyRot u t) i j) 0 := by
    simp only [Matrix.mul_apply]
    exact HasDerivAt.fun_sum (fun k _ => (hasDerivAt_cayleyRot_zero u i k).mul_const _)
  have hev : ∀ᶠ s in nhds (0 : ℝ), 1 - (u ⬝ᵥ u) * s * t ≠ 0 := by
    have hc : ContinuousAt (fun s : ℝ => 1 - (u ⬝ᵥ u) * s * t) 0 := by fun_prop
    exact hc.eventually_ne (by simp)
  have h3 : (fun s => cayleyRot u (halfAngleAdd (u ⬝ᵥ u) s t) i j) =ᶠ[nhds 0]
      (fun s => (cayleyRot u s * cayleyRot u t) i j) := by
    filter_upwards [hev] with s hs
    rw [cayleyRot_mul u hs]
  have h := h1.unique (h2.congr_of_eventuallyEq h3)
  rw [Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.smul_apply, smul_eq_mul, angularRate]
  field_simp
  linarith

end FiniteFlow

/-! ## 7. The rechart on the owner's screws -/

section Screw
open Holonics.Geometry.ScrewGeometry Holonics.Transport.SerialScrewChain

/-- [proved-standard; formal-checked] **Proper recharting carries velocities:**
`(Rω) × (Rx + t) + (Rv + t × Rω) = R (ω × x + v)` over any field. -/
theorem proper_rechart_velocity {K : Type*} [Field K] {R : Matrix (Fin 3) (Fin 3) K}
    (hR : Rᵀ * R = 1) (hdet : R.det = 1) (t ω v x : Fin 3 → K) :
    (R *ᵥ ω) ⨯₃ (R *ᵥ x + t) + (R *ᵥ v + t ⨯₃ (R *ᵥ ω)) = R *ᵥ (ω ⨯₃ x + v) := by
  rw [map_add, Holonics.Geometry.Motion.proper_mulVec_cross hR hdet, Matrix.mulVec_add,
    ← cross_anticomm (R *ᵥ ω) t]
  abel

/-- [definition] The rechart of a screw through the finite chart `f = (R, t)`, the Rust
`ScrewGenerator::rechart`: `(Rω, Rv + t × Rω)`. -/
def rechart (f : AffineMap3) (ξ : Screw) : Screw where
  angular := f.linear *ᵥ ξ.angular
  linear := f.linear *ᵥ ξ.linear + f.translation ⨯₃ (f.linear *ᵥ ξ.angular)

/-- [definition] A finite chart is proper when its linear part is a proper rotation. -/
def IsProper (f : AffineMap3) : Prop := f.linearᵀ * f.linear = 1 ∧ f.linear.det = 1

/-- [proved-derived; formal-checked] **The rechart is `Ad` on velocity fields:**
`V_(rechart f ξ)(f x) = R V_ξ(x)` for a proper chart. -/
theorem rechart_velocity {f : AffineMap3} (hf : IsProper f) (ξ : Screw) (x : Vec) :
    velocity (rechart f ξ) (f.apply x) = f.linear *ᵥ velocity ξ x :=
  proper_rechart_velocity hf.1 hf.2 _ _ _ _

/-- [proved-derived; formal-checked] The identity chart recharts nothing. -/
theorem rechart_identity (ξ : Screw) : rechart AffineMap3.identity ξ = ξ := by
  cases ξ
  simp [rechart, AffineMap3.identity]

/-- [proved-derived; formal-checked] A translation chart's rechart is the owner's
`translationRechart`. -/
theorem rechart_translationChart (t : Vec) (ξ : Screw) :
    rechart (translationChart t) ξ = translationRechart t ξ := by
  cases ξ
  simp [rechart, translationChart, translationRechart, translated]

/-- [proved-derived; formal-checked] Ordered composition of proper charts is proper. -/
theorem isProper_compose {f g : AffineMap3} (hf : IsProper f) (hg : IsProper g) :
    IsProper (f.compose g) := by
  refine ⟨?_, ?_⟩
  · simp only [AffineMap3.compose]
    rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc g.linearᵀ, hg.1,
      Matrix.one_mul, hf.1]
  · simp only [AffineMap3.compose]
    rw [Matrix.det_mul, hg.2, hf.2, mul_one]

/-- [proved-derived; formal-checked] **`Ad` of an ordered product:** applying `f` then a proper
`g` recharts as `rechart g ∘ rechart f`. -/
theorem rechart_compose (f : AffineMap3) {g : AffineMap3} (hg : IsProper g) (ξ : Screw) :
    rechart (f.compose g) ξ = rechart g (rechart f ξ) := by
  cases ξ with
  | mk ω v =>
    simp only [rechart, AffineMap3.compose]
    congr 1
    · rw [Matrix.mulVec_mulVec]
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
        ← Holonics.Geometry.Motion.proper_mulVec_cross hg.1 hg.2, LinearMap.map_add₂]
      abel

/-- [definition] The revolute generator with angular part `ω` about the pivot `p`, the Rust
`parameter_generator`: advance `−(ω × p) = p × ω`. -/
def revoluteGenerator (ω p : Vec) : Screw where
  angular := ω
  linear := p ⨯₃ ω

/-- [proved-derived; formal-checked] A revolute generator recharts to the generator of the moved
axis through the moved pivot. -/
theorem rechart_revolute {f : AffineMap3} (hf : IsProper f) (ω p : Vec) :
    rechart f (revoluteGenerator ω p) = revoluteGenerator (f.linear *ᵥ ω) (f.apply p) := by
  simp only [rechart, revoluteGenerator, AffineMap3.apply]
  congr 1
  rw [← Holonics.Geometry.Motion.proper_mulVec_cross hf.1 hf.2, LinearMap.map_add₂]

/-- [definition] The Rust `spatial_jacobian` loop: each joint's generator recharted through the
current prefix, the prefix then advanced by `f.compose acc`. -/
def spatialColumns : AffineMap3 → List (Screw × AffineMap3) → List Screw
  | _, [] => []
  | acc, (ξ, f) :: js => rechart acc ξ :: spatialColumns (f.compose acc) js

/-- [proved-derived; formal-checked] **The columns are the owner's serial prefixes applied to the
generators:** `spatialColumns base js = zipWith rechart (serialPrefixes base fs) ξs`. -/
theorem spatialColumns_eq_zipWith (base : AffineMap3) (js : List (Screw × AffineMap3)) :
    spatialColumns base js =
      List.zipWith rechart (serialPrefixes base (js.map Prod.snd)) (js.map Prod.fst) := by
  induction js generalizing base with
  | nil => simp [spatialColumns, serialPrefixes]
  | cons j js ih =>
    obtain ⟨ξ, f⟩ := j
    simp [spatialColumns, serialPrefixes, ih]

end Screw

end Holonics.Transport.SerialChainJacobian

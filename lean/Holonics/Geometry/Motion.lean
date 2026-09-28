import Holonics.Geometry.AffineSwing
import Holonics.Geometry.HolonicPantographicSwingJets
import Holonics.Foundation.TransportWord
import Holonics.Compression.Landmark.FixedPoint
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Motion: a move about its pivot, the turn and the boost, free fall, and the path jets

[definition] The motion record of September 28 (`THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_…`, §3 and §9)
re-derives the Swing as a move about a grip. This module proves its exact identities. A receiver
reads a rate `A` against its energy metric `G` (storage `½⟨x, G x⟩`); a finite **move** is
`x ↦ M x + b`; its **pivot** is derived from the move as a solution of `(1 − M) O = b`. The frozen-board Swing `AffineSwing.swing a x = 2a − x` is the move `M = −1`, the
half-turn about `a`.

[proved-standard; formal-checked] What is proved, over any commutative ring or field named in each
statement (`½` is `⅟2`, so characteristic two is excluded by hypothesis, never by a float):

1. **Turn and boost are the receiver's split of a rate** (§3.2). With `A♯ = G⁻¹AᵀG`
   (`adjointIn`), `turn G A = ½(A − A♯)` and `boost G A = ½(A + A♯)` add to `A`
   (`turn_add_boost`); for invertible symmetric `G` the turn is `G`-skew (`turn_isSkew`) and the
   boost `G`-symmetric (`boost_isSymm`); any split into a `G`-skew and a `G`-symmetric part is this
   one (`turn_boost_unique`, which needs only `G` invertible). The receiver's energy rate
   `⟨x, G A x⟩ + ⟨A x, G x⟩` is `2⟨x, G B x⟩` (`energy_rate_is_boost`): a `G`-skew rate contributes
   nothing (`skew_rate_conserves`). One complex channel `ż = (β + iθ) z`, read as the real matrix
   `[[β, −θ], [θ, β]]` against `G = 1`, splits into the turn `[[0, −θ], [θ, 0]]` and the boost
   `β·1` (`complex_rate_split`).
2. **The port-Hamiltonian reading** (§3.3). For `ẋ = (J − R) Q x` with `J` skew, `R` and `Q`
   symmetric and `Q` invertible, the receiver of storage `Q` reads the turn `J Q` and the boost
   `−R Q` (`turn_portHamiltonian`, `boost_portHamiltonian`): in this quadratic chart the
   interconnection turns and the resistive relation is friction, a boost.
3. **A move has the pivot it holds** (§3.4). `(1 − M) O = b` gives `M x + b − O = M (x − O)`
   (`move_about_pivot`); the pivots are exactly the fixed points (`move_fixes_iff_pivot`) and are
   unique when `1 − M` is injective (`pivot_unique`); moves compose as
   `(M₁, b₁) ∘ (M₂, b₂) = (M₁M₂, M₁b₂ + b₁)` (`move_comp`); a pure translation has no pivot
   (`translation_has_no_pivot`, the pivot at infinity); and with `b = b_∥ + b_⊥`, `M b_∥ = b_∥`
   and `(1 − M) O = b_⊥`, the move is `M` about the axis through `O` followed by the free fall
   `b_∥`, with which it commutes (`move_about_axis_then_falls`).
4. **The complex chart** (§3.4). For `k ≠ 1` the pivot `O = b/(1 − k)` gives
   `k z + b − O = k (z − O)` (`complex_move_about_pivot`), which is the pantograph of
   `Geometry/HolonicPantographicSwingJets.pantographicPoint` about `O` with scale `k`
   (`complex_move_is_pantograph`); `k = 1, b ≠ 0` has no pivot (`complex_fall_has_no_pivot`);
   multipliers multiply under composition (`complex_move_comp`); the frozen-board Swing is the move
   `k = −1` whose pivot is its anchor (`swing_is_half_turn_move`, `swing_pivot_is_anchor`).
5. **The multiplier is a cross ratio** (§3.5), on the Möbius navigator of
   `Compression/Landmark/FixedPoint` (atlas `landmark.mobius-fixed-points`). With distinct fixed
   points `z₁, z₂` and `μ_i = c z_i + d`, undivided,
   `(m z − z₁)(z − z₂) μ₁ = μ₂ (z − z₁)(m z − z₂)` (`multiplier_cross_ratio`): two pivots, the body
   and its image make the move. `(μ₁ + μ₂)² (ad − bc) = (a + d)² μ₁μ₂`
   (`multiplier_trace_det_undivided`), so `K + 1/K + 2 = tr²/det` for `K = μ₂/μ₁`
   (`multiplier_trace_det`); and `K = −1` exactly when the trace is zero
   (`multiplier_half_turn_iff_traceless`, `multiplier_ratio_half_turn_iff_traceless`).
6. **Half-turn words are poor in motions** (§2). Every word of half-turns (point reflections) has
   linear part `(−1)^length` (`swing_word_linear_part`): an even word is a translation
   (`even_swing_word_is_translation`) and an odd word a half-turn
   (`odd_swing_word_is_point_reflection`, `odd_swing_word_is_swing`). This is the one owner of the
   half-turn word law. Its length-two case `AffineSwing.twoSwingsAreADoubledTranslation` stays
   beside the half-turn's definition, which this module imports, for its consumers; the circuits
   of length two, three and four of `HolonicsResearch/Geometry/Navigation` are derived from it.
   `det(−1_d) = (−1)^d` (`det_half_turn`): `−1` in odd dimension (`det_half_turn_odd`), `1` in even
   (`det_half_turn_even`).
7. **Point-mass work and the sling** (§3.3, §3.8). In the complex chart, with `v̇ = v ẇ`,
   `Re(v̄ · v ẇ) = |v|² Re ẇ` (`power_is_boost_rate`: the power is the boost rate) and
   `Im(v̄ · v ẇ) = |v|² Im ẇ` (`normal_effort_is_turn_rate`), so for `m ≠ 0`, `v ≠ 0` and
   `F = m v ẇ` the signed turn rate is `θ̇ = Im(v̄ F)/(m|v|²)` and the boost rate
   `β̇ = Re(v̄ F)/(m|v|²)` (`rates_from_effort`). **The sling** is owned here in a receiver's
   metric: if the relative velocities about a moving pivot `V` carry equal `G`-energy,
   `⟨u′, G u′⟩ = ⟨u, G u⟩`, the reading of the absolute velocities changes by
   `⟨V + u′, G(V + u′)⟩ − ⟨V + u, G(V + u)⟩ = 2⟨V, G(u′ − u)⟩` (`sling_energy_gain`). In the
   complex chart, `v_out − V = k (v_in − V)` with `|k|² = 1` gives
   `|v_out|² − |v_in|² = 2 Re(V̄ (v_out − v_in))` (`sling_speed_gain`, derived from it): a turn
   about a pivot `V` changes the speed a receiver centred at rest reads. The finite-coordinate form
   `HolonicsResearch/Geometry/HolonicSlingTransport.gravityAssist_squaredSpeed_difference` is its
   unit-metric case.
8. **The traction disk** (§7). For `v ≠ 0` and `k = v′/v`, `|v′ − v|² = |k − 1|² |v|²`
   (`traction_move_ratio`, `traction_disk`); for `|k|² = 1`, `|k − 1|² = 2 − 2 Re k`
   (`turn_distance_from_one`); the chord of `k = cos θ + i sin θ` is
   `|k − 1|² = 2 − 2cos θ = 4 sin²(θ/2)` (`turn_by_angle_distance_from_one`).
9. **The path jets** (§3.6). With `ẋ = e^w`, `ẍ = e^w ẇ` and `ẇ = (e^w)⁻¹ ẍ`, the Maurer–Cartan
   form (`velocity_rate_is_log_derivative`); the jerk is `e^w (ẇ² + ẅ)` (`acceleration_and_jerk`).
   In any differential ring, `D e = e w₁` gives `Dⁿ e = e Y_n` with `Y_0 = 1`,
   `Y_(n+1) = D Y_n + w₁ Y_n` (`derivation_iterate_of_log_rate`). On the integer jet polynomials
   (`jetDerivation`, `D X_i = X_(i+1)`), the complete Bell recursion `bellJet` has
   `bellJet 1 = X₁`, `bellJet 2 = X₂ + X₁²` (`bellJet_one`, `bellJet_two`), evaluation at the jets
   of `w` differentiates as the derivation (`hasDerivAt_jet_eval`), and every higher derivative of
   the position is `x^(n+1) = e^w · Y_n(ẇ, ẅ, …)` (`position_jets`).
10. **The three kinds of quadratic motion** (§3.1). The flow of
   `H = ½(α p² + 2β p q + γ q²)` on `(q, p)` has generator `X = [[β, α], [−γ, −β]]`
   (`quadraticGenerator`), traceless with `det X = αγ − β²`, the determinant of the energy metric
   `G_H = [[γ, β], [β, α]]` (`quadraticGenerator_trace_det`); `X = J G_H` is `G_H`-skew, a turn of
   its own energy (`quadraticGenerator_is_turn_of_energy`); `X² = −(det X)·1`
   (`quadraticGenerator_sq`). So `det X = ω²` is a turn (`quadratic_turn`), with a definite energy
   when `α > 0` (`quadratic_turn_energy_pos`); `det X = −r²` a boost, `X² = r²·1`
   (`quadratic_boost`); and `det X = 0` free fall, a nilpotent shear whose exact steps compose
   additively (`quadratic_fall`), the free particle's `[[1, h/m], [0, 1]]`
   (`free_particle_step`).
11. **Iwasawa for `SL(2)`** (§3.1), with the root `r² = a² + c²` a hypothesis so that it holds in any
   field containing it: `M = K · diag(r, r⁻¹) · [[1, (ab + cd)/r²], [0, 1]]` with `K` orthogonal
   (`iwasawa`), and the factors are unique once the boost is positive (`iwasawa_unique`): every
   move of `SL(2)` is a turn, a boost and a free-fall shear (the `KAN` split).
12. **The energy law with a moving metric and forcing** (§3.2). Along `ẋ = Ax + f` with metric `G`
   (symmetric) and rate `Ġ`, undivided: `ẋᵀGx + xᵀĠx + xᵀGẋ = xᵀ(AᵀG + GA + Ġ)x + 2xᵀGf`
   (`energy_rate_moving_metric`) `= 2xᵀG B x + xᵀĠx + 2xᵀGf` with `B` the boost
   (`energy_rate_moving_metric_boost`): the boost's work, the moving metric's work (a pump's or a
   deposition's) and the push's power. This is the algebraic form of the law, for any rate `A`
   and any symmetric metric. Its dynamical owner, with learning, is
   `Holon/Deposition.learned_energy_balance`: the derivative over `ℝ` along
   `ẋ = (J − R + L) Q(τ) x + B u`, in the Holon's quadratic port chart (`G = Q`,
   `A = (J − R + L) Q`, `f = B u`, `Ġ = Q̇`). The constant-metric rate form
   `Foundation/CausalChord.rateForm` (its congruence `rateForm_congruence`) and the dissipative
   generator's storage rate `Transport/HolonicInteraction.port_storage_rate`
   (`AᵀG + GA = −2GMG`) are its `Ġ = 0`, `f = 0` readings; `boost_portHamiltonian` is the same
   dissipation read as the boost.

[interpretation] The words grip, push, free fall and sling are the record's readings of these
identities; the split's dependence on the receiver (a different metric for the same motion moves
it; a rechart does not) is the record's §3.2 and is not a further theorem here. Owed and cited in the record, not proved here:
`PSL(2, ℂ) ≅ SO⁺(1, 3)`, Chasles, Lancret, the polar decomposition over an exact field with square
roots.
-/

noncomputable section

namespace Holonics.Geometry.Motion

open Matrix

/-! ## 1. Turn and boost are a receiver's split of a rate -/

section TurnBoost

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- [definition] The adjoint of a rate `A` in the receiver's energy metric `G`:
`A♯ = G⁻¹ Aᵀ G`. -/
def adjointIn (G A : Matrix n n K) : Matrix n n K := G⁻¹ * Aᵀ * G

variable [Invertible (2 : K)]

/-- [definition] The **turn** of a rate `A` read by the receiver of metric `G`:
`T = ½(A − G⁻¹AᵀG)`. -/
def turn (G A : Matrix n n K) : Matrix n n K := (⅟2 : K) • (A - adjointIn G A)

/-- [definition] The **boost** of a rate `A` read by the receiver of metric `G`:
`B = ½(A + G⁻¹AᵀG)`. -/
def boost (G A : Matrix n n K) : Matrix n n K := (⅟2 : K) • (A + adjointIn G A)

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] `G A♯ = Aᵀ G`. -/
theorem mul_adjointIn {G : Matrix n n K} (hG : IsUnit G.det) (A : Matrix n n K) :
    G * adjointIn G A = Aᵀ * G := by
  rw [adjointIn, Matrix.mul_assoc, ← Matrix.mul_assoc G, Matrix.mul_nonsing_inv G hG,
    Matrix.one_mul]

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] For symmetric `G`, `(A♯)ᵀ G = G A`. -/
theorem adjointIn_transpose_mul {G : Matrix n n K} (hG : IsUnit G.det) (hGs : Gᵀ = G)
    (A : Matrix n n K) : (adjointIn G A)ᵀ * G = G * A := by
  rw [adjointIn, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_nonsing_inv, hGs, Matrix.mul_assoc, Matrix.mul_assoc A,
    Matrix.nonsing_inv_mul G hG, Matrix.mul_one]

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] A `G`-skew rate is its own negative adjoint. -/
theorem adjointIn_eq_neg_of_skew {G T : Matrix n n K} (hG : IsUnit G.det)
    (hT : G * T + Tᵀ * G = 0) : adjointIn G T = -T := by
  have h : Tᵀ * G = -(G * T) := eq_neg_of_add_eq_zero_right hT
  rw [adjointIn, Matrix.mul_assoc, h, Matrix.mul_neg, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul G hG, Matrix.one_mul]

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] A `G`-symmetric rate is its own adjoint. -/
theorem adjointIn_eq_self_of_symm {G B : Matrix n n K} (hG : IsUnit G.det)
    (hB : G * B = Bᵀ * G) : adjointIn G B = B := by
  rw [adjointIn, Matrix.mul_assoc, ← hB, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG,
    Matrix.one_mul]

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] The adjoint is additive. -/
theorem adjointIn_add (G A B : Matrix n n K) :
    adjointIn G (A + B) = adjointIn G A + adjointIn G B := by
  simp only [adjointIn, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

omit [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] Against the unit metric the adjoint is the transpose. -/
theorem adjointIn_one (A : Matrix n n K) : adjointIn 1 A = Aᵀ := by
  rw [adjointIn, inv_one, Matrix.one_mul, Matrix.mul_one]

omit [Fintype n] [DecidableEq n] in
private theorem half_add_half (x : Matrix n n K) : (⅟2 : K) • x + (⅟2 : K) • x = x := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

omit [Fintype n] [DecidableEq n] in
private theorem half_smul_add_self (x : Matrix n n K) : (⅟2 : K) • (x + x) = x := by
  rw [smul_add, half_add_half]

/-- [proved-standard; formal-checked] **The turn and the boost add to the rate.** -/
theorem turn_add_boost (G A : Matrix n n K) : turn G A + boost G A = A := by
  rw [turn, boost, ← smul_add, show A - adjointIn G A + (A + adjointIn G A) = A + A by abel,
    half_smul_add_self]

/-- [proved-standard; formal-checked] **The turn is `G`-skew:** `G T + Tᵀ G = 0`. -/
theorem turn_isSkew {G : Matrix n n K} (hG : IsUnit G.det) (hGs : Gᵀ = G) (A : Matrix n n K) :
    G * turn G A + (turn G A)ᵀ * G = 0 := by
  simp only [turn, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_sub,
    Matrix.transpose_sub, Matrix.sub_mul, mul_adjointIn hG, adjointIn_transpose_mul hG hGs]
  module

/-- [proved-standard; formal-checked] **The boost is `G`-symmetric:** `G B = Bᵀ G`. -/
theorem boost_isSymm {G : Matrix n n K} (hG : IsUnit G.det) (hGs : Gᵀ = G) (A : Matrix n n K) :
    G * boost G A = (boost G A)ᵀ * G := by
  simp only [boost, Matrix.mul_smul, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.transpose_add, Matrix.add_mul, mul_adjointIn hG, adjointIn_transpose_mul hG hGs]
  module

/-- [proved-standard; formal-checked] **The split is unique:** any decomposition `A = T + B` into
a `G`-skew `T` and a `G`-symmetric `B` is the turn and the boost. Only `G` invertible is used: a
rate both `G`-skew and `G`-symmetric is zero. -/
theorem turn_boost_unique {G A T B : Matrix n n K} (hG : IsUnit G.det) (hA : T + B = A)
    (hT : G * T + Tᵀ * G = 0) (hB : G * B = Bᵀ * G) : turn G A = T ∧ boost G A = B := by
  subst hA
  rw [turn, boost, adjointIn_add, adjointIn_eq_neg_of_skew hG hT,
    adjointIn_eq_self_of_symm hG hB]
  constructor
  · rw [show T + B - (-T + B) = T + T by abel, half_smul_add_self]
  · rw [show T + B + (-T + B) = B + B by abel, half_smul_add_self]

omit [DecidableEq n] [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] The receiver's energy rate along `ẋ = M x` is the quadratic
form of `G M + Mᵀ G`. -/
theorem rate_quadratic (G M : Matrix n n K) (x : n → K) :
    x ⬝ᵥ (G *ᵥ (M *ᵥ x)) + (M *ᵥ x) ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ ((G * M + Mᵀ * G) *ᵥ x) := by
  have h : (M *ᵥ x) ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ ((Mᵀ * G) *ᵥ x) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  rw [h, Matrix.mulVec_mulVec, Matrix.add_mulVec, dotProduct_add]

omit [DecidableEq n] [Invertible (2 : K)] in
/-- [proved-standard; formal-checked] **A turn does no work:** a `G`-skew rate leaves the
receiver's energy rate zero. -/
theorem skew_rate_conserves {G T : Matrix n n K} (hT : G * T + Tᵀ * G = 0) (x : n → K) :
    x ⬝ᵥ (G *ᵥ (T *ᵥ x)) + (T *ᵥ x) ⬝ᵥ (G *ᵥ x) = 0 := by
  rw [rate_quadratic, hT, Matrix.zero_mulVec, dotProduct_zero]

/-- [proved-standard; formal-checked] **Only the boost changes the receiver's energy:**
`⟨x, G A x⟩ + ⟨A x, G x⟩ = 2⟨x, G B x⟩`, the exact form of `d/dt ½⟨x, Gx⟩ = ⟨x, G B x⟩`. -/
theorem energy_rate_is_boost {G : Matrix n n K} (hG : IsUnit G.det) (A : Matrix n n K)
    (x : n → K) :
    x ⬝ᵥ (G *ᵥ (A *ᵥ x)) + (A *ᵥ x) ⬝ᵥ (G *ᵥ x) = 2 * (x ⬝ᵥ (G *ᵥ (boost G A *ᵥ x))) := by
  have h : G * A + Aᵀ * G = (2 : K) • (G * boost G A) := by
    rw [boost, Matrix.mul_smul, Matrix.mul_add, mul_adjointIn hG, smul_smul, mul_invOf_self,
      one_smul]
  rw [rate_quadratic, h, Matrix.mulVec_mulVec, Matrix.smul_mulVec, dotProduct_smul,
    smul_eq_mul]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **One complex channel.** The rate `ż = (β + iθ) z`, carried
as `[[β, −θ], [θ, β]]` against the unit metric, has the turn `[[0, −θ], [θ, 0]]` (the angular rate
`θ`) and the boost `β·1` (the log-growth rate `β`). -/
theorem complex_rate_split (β θ : K) :
    turn 1 !![β, -θ; θ, β] = !![0, -θ; θ, 0] ∧ boost 1 !![β, -θ; θ, β] = !![β, 0; 0, β] := by
  constructor
  · rw [turn, adjointIn_one, show !![β, -θ; θ, β] - !![β, -θ; θ, β]ᵀ =
      !![0, -θ; θ, 0] + !![0, -θ; θ, 0] by
        ext i j; fin_cases i <;> fin_cases j <;> simp [sub_eq_add_neg],
      half_smul_add_self]
  · rw [boost, adjointIn_one, show !![β, -θ; θ, β] + !![β, -θ; θ, β]ᵀ =
      !![β, 0; 0, β] + !![β, 0; 0, β] by
        ext i j; fin_cases i <;> fin_cases j <;> simp,
      half_smul_add_self]

end TurnBoost

/-! ## 2. The port-Hamiltonian reading: the grip turns, friction boosts -/

section PortHamiltonian

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- [proved-derived; formal-checked] The adjoint of the port-Hamiltonian rate `(J − R) Q` in the
storage metric `Q` is `(−J − R) Q`. -/
theorem adjointIn_portHamiltonian {J R Q : Matrix n n K} (hQ : IsUnit Q.det) (hQs : Qᵀ = Q)
    (hJ : Jᵀ = -J) (hR : Rᵀ = R) : adjointIn Q ((J - R) * Q) = (-J - R) * Q := by
  rw [adjointIn, Matrix.transpose_mul, hQs, Matrix.transpose_sub, hJ, hR, ← Matrix.mul_assoc Q⁻¹,
    Matrix.nonsing_inv_mul Q hQ, Matrix.one_mul]

variable [Invertible (2 : K)]

/-- [proved-derived; formal-checked] **The interconnection is the turn:** the receiver of storage
`Q` reads the turn of `(J − R) Q` as `J Q`. -/
theorem turn_portHamiltonian {J R Q : Matrix n n K} (hQ : IsUnit Q.det) (hQs : Qᵀ = Q)
    (hJ : Jᵀ = -J) (hR : Rᵀ = R) : turn Q ((J - R) * Q) = J * Q := by
  rw [turn, adjointIn_portHamiltonian hQ hQs hJ hR,
    show (J - R) * Q - (-J - R) * Q = J * Q + J * Q by
      simp only [Matrix.sub_mul, Matrix.neg_mul]; abel,
    half_smul_add_self]

/-- [proved-derived; formal-checked] **Friction is the boost:** the receiver of storage `Q` reads
the boost of `(J − R) Q` as `−R Q`. -/
theorem boost_portHamiltonian {J R Q : Matrix n n K} (hQ : IsUnit Q.det) (hQs : Qᵀ = Q)
    (hJ : Jᵀ = -J) (hR : Rᵀ = R) : boost Q ((J - R) * Q) = -(R * Q) := by
  rw [boost, adjointIn_portHamiltonian hQ hQs hJ hR,
    show (J - R) * Q + (-J - R) * Q = -(R * Q) + -(R * Q) by
      simp only [Matrix.sub_mul, Matrix.neg_mul]; abel,
    half_smul_add_self]

end PortHamiltonian

/-! ## 3. A move has the pivot it holds -/

section AffineMove

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- [definition] The finite **move** `x ↦ M x + b`. -/
def move (M : Module.End R V) (b : V) (x : V) : V := M x + b

/-- [proved-standard; formal-checked] **The move about its pivot:** `(1 − M) O = b` gives
`M x + b − O = M (x − O)`. -/
theorem move_about_pivot {M : Module.End R V} {b O : V} (hO : (1 - M) O = b) (x : V) :
    move M b x - O = M (x - O) := by
  rw [move, ← hO, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  abel

/-- [proved-standard; formal-checked] The pivots of a move are exactly its fixed points. -/
theorem move_fixes_iff_pivot (M : Module.End R V) (b O : V) :
    move M b O = O ↔ (1 - M) O = b := by
  rw [move, LinearMap.sub_apply, Module.End.one_apply, sub_eq_iff_eq_add', eq_comm]

/-- [proved-standard; formal-checked] When `1 − M` is injective the pivot is unique. -/
theorem pivot_unique {M : Module.End R V} {b O₁ O₂ : V}
    (hinj : Function.Injective ⇑(1 - M : Module.End R V))
    (h₁ : (1 - M) O₁ = b) (h₂ : (1 - M) O₂ = b) : O₁ = O₂ :=
  hinj (h₁.trans h₂.symm)

/-- [proved-standard; formal-checked] **Moves compose** as
`(M₁, b₁) ∘ (M₂, b₂) = (M₁M₂, M₁b₂ + b₁)`. -/
theorem move_comp (M₁ M₂ : Module.End R V) (b₁ b₂ x : V) :
    move M₁ b₁ (move M₂ b₂ x) = move (M₁ * M₂) (M₁ b₂ + b₁) x := by
  simp only [move, map_add, Module.End.mul_apply]
  abel

/-- [proved-standard; formal-checked] **The pivot at infinity:** a pure translation `b ≠ 0` fixes
no point. -/
theorem translation_has_no_pivot {b : V} (hb : b ≠ 0) (O : V) :
    move (1 : Module.End R V) b O ≠ O := by
  rw [Ne, move_fixes_iff_pivot, sub_self, LinearMap.zero_apply]
  exact fun h ↦ hb h.symm

/-- [proved-derived; formal-checked] **A turn about an axis, then free fall along it.** With
`b = b_∥ + b_⊥`, `M b_∥ = b_∥` and `(1 − M) O = b_⊥`, the move is `M` about `O` followed by the
fall `b_∥`, and it commutes with the fall. -/
theorem move_about_axis_then_falls {M : Module.End R V} {b bPar bPerp O : V}
    (hb : b = bPar + bPerp) (hPar : M bPar = bPar) (hO : (1 - M) O = bPerp) (x : V) :
    move M b x = O + M (x - O) + bPar ∧ move M b (x + bPar) = move M b x + bPar := by
  constructor
  · rw [move, hb, ← hO, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    abel
  · rw [move, move, map_add, hPar]
    abel

end AffineMove

/-! ## 4. The complex chart of a move -/

section ComplexChart

variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] For `k ≠ 1`, the pivot `O = b/(1 − k)` gives
`k z + b − O = k (z − O)`. -/
theorem complex_move_about_pivot {k : K} (hk : k ≠ 1) (b z : K) :
    k * z + b - b / (1 - k) = k * (z - b / (1 - k)) := by
  have h : (1 : K) - k ≠ 0 := sub_ne_zero.mpr hk.symm
  field_simp
  ring

/-- [proved-derived; formal-checked] The complex move is the pantograph about its pivot with
scale `k` (`HolonicPantographicSwingJets.pantographicPoint`). -/
theorem complex_move_is_pantograph {k : K} (hk : k ≠ 1) (b z : K) :
    k * z + b = HolonicPantographicSwingJets.pantographicPoint (b / (1 - k)) k z := by
  rw [HolonicPantographicSwingJets.pantographicPoint, smul_eq_mul,
    ← complex_move_about_pivot hk b z]
  ring

/-- [proved-standard; formal-checked] **Free fall:** `k = 1` with `b ≠ 0` has no pivot. -/
theorem complex_fall_has_no_pivot {b : K} (hb : b ≠ 0) (z : K) : 1 * z + b ≠ z := by
  intro h
  exact hb (by linear_combination h)

/-- [proved-standard; formal-checked] Complex moves compose by multiplying multipliers:
`(k₁, b₁) ∘ (k₂, b₂) = (k₁k₂, k₁b₂ + b₁)`. -/
theorem complex_move_comp (k₁ k₂ b₁ b₂ z : K) :
    k₁ * (k₂ * z + b₂) + b₁ = (k₁ * k₂) * z + (k₁ * b₂ + b₁) := by
  ring

/-- [proved-derived; formal-checked] **The frozen-board Swing is the half-turn move** `k = −1`,
`b = 2a`. -/
theorem swing_is_half_turn_move (a z : K) : AffineSwing.swing a z = (-1) * z + (a + a) := by
  rw [AffineSwing.swing]
  ring

/-- [proved-derived; formal-checked] The half-turn's derived pivot `2a/(1 − (−1))` is the Swing's
anchor. -/
theorem swing_pivot_is_anchor (h2 : (2 : K) ≠ 0) (a : K) : (a + a) / (1 - (-1)) = a := by
  rw [show (1 : K) - (-1) = 2 by ring, show a + a = 2 * a by ring]
  field_simp

end ComplexChart

/-! ## 5. The multiplier is a cross ratio of the two pivots, the body and its image -/

section Multiplier

open Holonics.Compression.Landmark.FixedPoint

variable {K : Type*} [Field K] (m : Mobius K)

/-- [proved-standard; formal-checked] **The multiplier is a cross ratio**, undivided:
`(m z − z₁)(z − z₂) μ₁ = μ₂ (z − z₁)(m z − z₂)` with `μ_i = c z_i + d`, off the pole. The two
pivots, the body and its image make the move. -/
theorem multiplier_cross_ratio {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂)
    {z : K} (hz : m.c * z + m.d ≠ 0) :
    (m.act z - z₁) * (z - z₂) * (m.c * z₁ + m.d) =
      (m.c * z₂ + m.d) * (z - z₁) * (m.act z - z₂) := by
  have e₁ := m.act_sub_fixed h₁ z hz
  have e₂ := m.act_sub_fixed h₂ z hz
  rw [m.other_multiplier h₁ h₂ hne] at e₁
  rw [m.other_multiplier h₂ h₁ hne.symm] at e₂
  rw [e₁, e₂]
  ring

/-- [proved-standard; formal-checked] Undivided, `(μ₁ + μ₂)² (ad − bc) = (a + d)² μ₁ μ₂`. -/
theorem multiplier_trace_det_undivided {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) :
    ((m.c * z₁ + m.d) + (m.c * z₂ + m.d)) ^ 2 * (m.a * m.d - m.b * m.c) =
      (m.a + m.d) ^ 2 * ((m.c * z₁ + m.d) * (m.c * z₂ + m.d)) := by
  have hs := m.multipliers_sum h₁ h₂ hne
  have hp := m.multipliers_prod h₁ h₂ hne
  rw [Mobius.trace] at hs
  rw [Mobius.det] at hp
  rw [hs, hp]

/-- [proved-standard; formal-checked] **`K + 1/K + 2 = tr²/det`** for `K = μ₂/μ₁`, when
`det ≠ 0`: the class of the move is read from its trace and determinant faces. -/
theorem multiplier_trace_det {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂)
    (hdet : m.det ≠ 0) :
    (m.c * z₂ + m.d) / (m.c * z₁ + m.d) + (m.c * z₁ + m.d) / (m.c * z₂ + m.d) + 2 =
      m.trace ^ 2 / m.det := by
  have hs := m.multipliers_sum h₁ h₂ hne
  have hp := m.multipliers_prod h₁ h₂ hne
  have hμ₁ : m.c * z₁ + m.d ≠ 0 := by
    intro h; apply hdet; rw [← hp, h, zero_mul]
  have hμ₂ : m.c * z₂ + m.d ≠ 0 := by
    intro h; apply hdet; rw [← hp, h, mul_zero]
  rw [← hs, ← hp]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The half-turn is the traceless move**, undivided:
`μ₂ = −μ₁` exactly when `a + d = 0`. -/
theorem multiplier_half_turn_iff_traceless {z₁ z₂ : K} (h₁ : m.Fixed z₁) (h₂ : m.Fixed z₂)
    (hne : z₁ ≠ z₂) : m.c * z₂ + m.d = -(m.c * z₁ + m.d) ↔ m.trace = 0 := by
  have hs := m.multipliers_sum h₁ h₂ hne
  constructor
  · intro h; linear_combination h - hs
  · intro h; linear_combination hs + h

/-- [proved-standard; formal-checked] `K = μ₂/μ₁ = −1` exactly when the trace is zero. -/
theorem multiplier_ratio_half_turn_iff_traceless {z₁ z₂ : K} (h₁ : m.Fixed z₁)
    (h₂ : m.Fixed z₂) (hne : z₁ ≠ z₂) (hμ₁ : m.c * z₁ + m.d ≠ 0) :
    (m.c * z₂ + m.d) / (m.c * z₁ + m.d) = -1 ↔ m.trace = 0 := by
  rw [div_eq_iff hμ₁, neg_one_mul]
  exact multiplier_half_turn_iff_traceless m h₁ h₂ hne

end Multiplier

/-! ## 6. Point reflections are poor in motions -/

section PointReflectionWords

open Holonics.Foundation.Chronology

variable {G : Type*} [AddCommGroup G]

/-- [proved-derived; formal-checked] **A word of point reflections has linear part
`(−1)^length`:** `W x − W y = (−1)^|w| (x − y)`. It composes only translations and half-turns. -/
theorem swing_word_linear_part (word : List G) (x y : G) :
    transportWord AffineSwing.swing word x - transportWord AffineSwing.swing word y =
      ((-1 : ℤ) ^ word.length) • (x - y) := by
  induction word with
  | nil => simp
  | cons a w ih =>
    rw [List.length_cons, pow_succ, mul_neg_one, neg_smul, ← ih]
    simp only [transportWord_cons, AffineSwing.swing]
    abel

/-- [proved-derived; formal-checked] An even word of point reflections is a translation. -/
theorem even_swing_word_is_translation {word : List G} (h : Even word.length) (x : G) :
    transportWord AffineSwing.swing word x = x + transportWord AffineSwing.swing word 0 := by
  have hx := swing_word_linear_part word x 0
  rw [h.neg_one_pow, one_smul, sub_zero] at hx
  exact sub_eq_iff_eq_add.mp hx

/-- [proved-derived; formal-checked] An odd word of point reflections is a point reflection:
`W x = W 0 − x`. -/
theorem odd_swing_word_is_point_reflection {word : List G} (h : Odd word.length) (x : G) :
    transportWord AffineSwing.swing word x = transportWord AffineSwing.swing word 0 - x := by
  have hx := swing_word_linear_part word x 0
  rw [h.neg_one_pow, neg_smul, one_smul, sub_zero] at hx
  rw [sub_eq_iff_eq_add] at hx
  rw [hx]
  abel

/-- [proved-derived; formal-checked] An odd word is the Swing about any half `c` of `W 0`. -/
theorem odd_swing_word_is_swing {word : List G} (h : Odd word.length) {c : G}
    (hc : c + c = transportWord AffineSwing.swing word 0) (x : G) :
    transportWord AffineSwing.swing word x = AffineSwing.swing c x := by
  rw [odd_swing_word_is_point_reflection h, AffineSwing.swing, hc]

/-- [proved-standard; formal-checked] `det(−1_d) = (−1)^d`. -/
theorem det_half_turn {K : Type*} [CommRing K] (d : ℕ) :
    (-1 : Matrix (Fin d) (Fin d) K).det = (-1) ^ d := by
  rw [Matrix.det_neg, Matrix.det_one, mul_one, Fintype.card_fin]

/-- [proved-standard; formal-checked] **In odd dimension the point reflection reverses
orientation:** `det(−1_d) = −1`, so it is parity, outside the identity component. -/
theorem det_half_turn_odd {K : Type*} [CommRing K] {d : ℕ} (hd : Odd d) :
    (-1 : Matrix (Fin d) (Fin d) K).det = -1 := by
  rw [det_half_turn, hd.neg_one_pow]

/-- [proved-standard; formal-checked] In even dimension the half-turn keeps orientation. -/
theorem det_half_turn_even {K : Type*} [CommRing K] {d : ℕ} (hd : Even d) :
    (-1 : Matrix (Fin d) (Fin d) K).det = 1 := by
  rw [det_half_turn, hd.neg_one_pow]

end PointReflectionWords

/-! ## 7. Point-mass work and the sling -/

section Work

open Complex ComplexConjugate

/-- [proved-standard; formal-checked] **The power is the boost rate:** with `v̇ = v ẇ`,
`Re(v̄ · v ẇ) = |v|² Re ẇ` (times the mass, `⟨F, v⟩ = m|v|² Re ẇ`). -/
theorem power_is_boost_rate (v w : ℂ) : (conj v * (v * w)).re = normSq v * w.re := by
  simp only [mul_re, mul_im, conj_re, conj_im, normSq_apply]
  ring

/-- [proved-standard; formal-checked] **The normal effort is the turn rate:**
`Im(v̄ · v ẇ) = |v|² Im ẇ`, the effort that does no work. -/
theorem normal_effort_is_turn_rate (v w : ℂ) : (conj v * (v * w)).im = normSq v * w.im := by
  simp only [mul_re, mul_im, conj_re, conj_im, normSq_apply]
  ring

/-- [proved-standard; formal-checked] **The signed rates read from the effort.** For a mass
`m ≠ 0` moving with `v ≠ 0` under the effort `F = m v̇ = m v ẇ`, the signed turn rate is
`θ̇ = Im ẇ = Im(v̄ F)/(m|v|²)` and the boost rate `β̇ = Re ẇ = Re(v̄ F)/(m|v|²)`. -/
theorem rates_from_effort {m : ℝ} {v w F : ℂ} (hm : m ≠ 0) (hv : v ≠ 0)
    (hF : F = m * (v * w)) :
    w.im = (conj v * F).im / (m * normSq v) ∧ w.re = (conj v * F).re / (m * normSq v) := by
  have hn : normSq v ≠ 0 := (normSq_pos.mpr hv).ne'
  have hvF : conj v * F = m * (conj v * (v * w)) := by rw [hF]; ring
  rw [hvF, im_ofReal_mul, re_ofReal_mul, normal_effort_is_turn_rate, power_is_boost_rate]
  constructor <;> field_simp

/-- [proved-standard; formal-checked] **The sling, in a receiver's metric** (the owner of the sling
law). About a moving pivot `V`, if the incoming and outgoing relative velocities `u`, `u′` carry
equal `G`-energy, `⟨u′, G u′⟩ = ⟨u, G u⟩` (a turn about the pivot, or any move holding that
energy), then for symmetric `G` the receiver's reading of the absolute velocities changes by
`⟨V + u′, G(V + u′)⟩ − ⟨V + u, G(V + u)⟩ = 2⟨V, G(u′ − u)⟩`: the pivot's pairing with the turned
relative change. -/
theorem sling_energy_gain {n K : Type*} [Fintype n] [CommRing K] {G : Matrix n n K}
    (hGs : Gᵀ = G) (V u u' : n → K) (hturn : u' ⬝ᵥ (G *ᵥ u') = u ⬝ᵥ (G *ᵥ u)) :
    (V + u') ⬝ᵥ (G *ᵥ (V + u')) - (V + u) ⬝ᵥ (G *ᵥ (V + u)) =
      2 * (V ⬝ᵥ (G *ᵥ (u' - u))) := by
  have hsym : ∀ a b : n → K, a ⬝ᵥ (G *ᵥ b) = b ⬝ᵥ (G *ᵥ a) := by
    intro a b
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hGs]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add,
    dotProduct_sub]
  rw [hsym u' V, hsym u V]
  linear_combination hturn

/-- [proved-standard; formal-checked] **The sling in the complex chart:** a pure turn about the
moving pivot `V`, `v_out − V = k (v_in − V)` with `|k|² = 1`, changes the squared speed read in
another frame by `|v_out|² − |v_in|² = 2 Re(V̄ (v_out − v_in))`. Derived from `sling_energy_gain`
at the unit metric on the plane `(re, im)`. -/
theorem sling_speed_gain {vIn vOut V k : ℂ} (hturn : vOut - V = k * (vIn - V))
    (hk : normSq k = 1) :
    normSq vOut - normSq vIn = 2 * (conj V * (vOut - vIn)).re := by
  have h := congrArg normSq hturn
  rw [normSq_mul, hk, one_mul] at h
  have key := sling_energy_gain (G := (1 : Matrix (Fin 2) (Fin 2) ℝ)) Matrix.transpose_one
    ![V.re, V.im] ![(vIn - V).re, (vIn - V).im] ![(vOut - V).re, (vOut - V).im]
    (by simpa [dotProduct, Fin.sum_univ_two, normSq_apply] using h)
  simp only [Matrix.one_mulVec, dotProduct, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, sub_re, sub_im] at key
  simp only [normSq_apply, sub_re, sub_im, mul_re, conj_re, conj_im]
  linear_combination key

end Work

/-! ## 8. The traction disk -/

section Traction

open Complex

/-- [proved-derived; formal-checked] **The change of velocity is the move ratio's distance from
one:** `|v′ − v|² = |k − 1|² |v|²` for `k = v′/v`. -/
theorem traction_move_ratio {v : ℂ} (hv : v ≠ 0) (v' : ℂ) :
    normSq (v' - v) = normSq (v' / v - 1) * normSq v := by
  rw [← normSq_mul]
  congr 1
  field_simp

/-- [proved-derived; formal-checked] **The traction disk:** a traction bound `|Δv|² ≤ r²` is the
bound `|k − 1|² |v|² ≤ r²` on the move ratio, a disk about `1` that shrinks as `|v|` grows. -/
theorem traction_disk {v : ℂ} (hv : v ≠ 0) (v' : ℂ) (r : ℝ) :
    normSq (v' - v) ≤ r ^ 2 ↔ normSq (v' / v - 1) * normSq v ≤ r ^ 2 := by
  rw [traction_move_ratio hv]

/-- [proved-standard; formal-checked] A pure turn `|k|² = 1` lies at `|k − 1|² = 2 − 2 Re k`
from one. -/
theorem turn_distance_from_one {k : ℂ} (hk : normSq k = 1) : normSq (k - 1) = 2 - 2 * k.re := by
  rw [normSq_apply] at hk ⊢
  simp only [sub_re, one_re, sub_im, one_im]
  linear_combination hk

/-- [proved-standard; formal-checked] **The chord of a turn by `θ`:** for
`k = cos θ + i sin θ`, `|k − 1|² = 2 − 2 cos θ = 4 sin²(θ/2)`. -/
theorem turn_by_angle_distance_from_one (θ : ℝ) :
    normSq ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I - 1) = 2 - 2 * Real.cos θ ∧
      normSq ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I - 1) = 4 * Real.sin (θ / 2) ^ 2 := by
  have hk : normSq ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) = 1 := by
    rw [normSq_add_mul_I, Real.cos_sq_add_sin_sq]
  have h := turn_distance_from_one hk
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero] at h
  refine ⟨h, ?_⟩
  rw [h, Real.sin_sq, Real.cos_sq, show 2 * (θ / 2) = θ by ring]
  ring

end Traction

/-! ## 9. The path jets: the complex log of the velocity carries every higher derivative -/

section PathJets

open Complex MvPolynomial

/-- [proved-standard; formal-checked] With velocity `e^w`, the acceleration is `e^w ẇ`, and
`ẇ = (e^w)⁻¹ (e^w)˙` is the Maurer–Cartan form: boost rate plus `i` times turn rate. -/
theorem velocity_rate_is_log_derivative {w : ℝ → ℂ} {t : ℝ} (hw : DifferentiableAt ℝ w t) :
    deriv (fun s ↦ exp (w s)) t = exp (w t) * deriv w t ∧
      (exp (w t))⁻¹ * deriv (fun s ↦ exp (w s)) t = deriv w t := by
  have h := deriv_cexp hw
  refine ⟨h, ?_⟩
  rw [h, ← mul_assoc, inv_mul_cancel₀ (exp_ne_zero _), one_mul]

/-- [proved-standard; formal-checked] **Acceleration and jerk:** `(e^w)˙ = e^w ẇ` and
`(e^w ẇ)˙ = e^w (ẇ² + ẅ)`. -/
theorem acceleration_and_jerk {w w' w'' : ℝ → ℂ} (hw : ∀ s, HasDerivAt w (w' s) s)
    (hw' : ∀ s, HasDerivAt w' (w'' s) s) (t : ℝ) :
    HasDerivAt (fun s ↦ exp (w s)) (exp (w t) * w' t) t ∧
      HasDerivAt (fun s ↦ exp (w s) * w' s) (exp (w t) * (w' t ^ 2 + w'' t)) t := by
  refine ⟨(hw t).cexp, ?_⟩
  exact ((hw t).cexp.mul (hw' t)).congr_deriv (by ring)

/-- [definition] The derivation of the integer jet polynomials, `D X_i = X_(i+1)`: `X_i` stands
for the `i`-th derivative of the velocity's complex log. -/
def jetDerivation : Derivation ℤ (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ) :=
  mkDerivation ℤ (fun i ↦ X (i + 1))

/-- [definition] The complete Bell recursion `Y₀ = 1`, `Y_(n+1) = D Y_n + X₁ Y_n`. -/
def bellJet : ℕ → MvPolynomial ℕ ℤ
  | 0 => 1
  | n + 1 => jetDerivation (bellJet n) + X 1 * bellJet n

/-- [proved-standard; formal-checked] `Y₁ = X₁`: the acceleration's factor is `ẇ`. -/
theorem bellJet_one : bellJet 1 = X 1 := by
  simp [bellJet, jetDerivation]

/-- [proved-standard; formal-checked] `Y₂ = X₂ + X₁²`: the jerk's factor is `ẅ + ẇ²`. -/
theorem bellJet_two : bellJet 2 = X 2 + X 1 ^ 2 := by
  simp [bellJet, jetDerivation, mkDerivation_X]
  ring

/-- [proved-derived; formal-checked] **The Bell recursion in a differential ring:** if
`D e = e w₁`, then `Dⁿ e = e Y_n` for `Y_0 = 1`, `Y_(n+1) = D Y_n + w₁ Y_n`. -/
theorem derivation_iterate_of_log_rate {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {e w₁ : A} (he : D e = e * w₁) {Y : ℕ → A} (hY0 : Y 0 = 1)
    (hY : ∀ n, Y (n + 1) = D (Y n) + w₁ * Y n) (n : ℕ) : (⇑D)^[n] e = e * Y n := by
  induction n with
  | zero => simp [hY0]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, he, hY, smul_eq_mul, smul_eq_mul]
    ring

/-- [proved-derived; formal-checked] Evaluating a jet polynomial at the jets `W i` of a path
(`W i` has derivative `W (i + 1)`) differentiates as the jet derivation. -/
theorem hasDerivAt_jet_eval {W : ℕ → ℝ → ℂ} (hW : ∀ i s, HasDerivAt (W i) (W (i + 1) s) s)
    (P : MvPolynomial ℕ ℤ) (t : ℝ) :
    HasDerivAt (fun s ↦ aeval (fun i ↦ W i s) P) (aeval (fun i ↦ W i t) (jetDerivation P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    simp only [aeval_C, derivation_C, map_zero]
    exact hasDerivAt_const t _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, aeval_X, Derivation.leibniz, jetDerivation, mkDerivation_X, smul_eq_mul,
      map_add] at hp ⊢
    exact (hp.mul (hW i t)).congr_deriv (by ring)

/-- [proved-derived; formal-checked] **Every higher derivative of motion is `e^w` times a Bell
polynomial in the jets of `w`:** if `ẋ = e^(W 0)` and `W i` has derivative `W (i + 1)`, then
`x^(n+1) = e^(W 0) · Y_n(W 1, W 2, …)`. -/
theorem position_jets {x : ℝ → ℂ} {W : ℕ → ℝ → ℂ}
    (hW : ∀ i s, HasDerivAt (W i) (W (i + 1) s) s)
    (hx : ∀ s, HasDerivAt x (exp (W 0 s)) s) (n : ℕ) :
    iteratedDeriv (n + 1) x = fun s ↦ exp (W 0 s) * aeval (fun i ↦ W i s) (bellJet n) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_one]
    funext s
    simp [bellJet, (hx s).deriv]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    have h : HasDerivAt (fun s ↦ exp (W 0 s) * aeval (fun i ↦ W i s) (bellJet n))
        (exp (W 0 s) * W (0 + 1) s * aeval (fun i ↦ W i s) (bellJet n) +
          exp (W 0 s) * aeval (fun i ↦ W i s) (jetDerivation (bellJet n))) s :=
      (hW 0 s).cexp.mul (hasDerivAt_jet_eval hW (bellJet n) s)
    rw [h.deriv]
    simp only [bellJet, map_add, map_mul, aeval_X, zero_add]
    ring

end PathJets

/-! ## 10. The three kinds of quadratic motion -/

section QuadraticMotion

variable {K : Type*} [CommRing K]

/-- [definition] The generator of the flow of `H = ½(α p² + 2β p q + γ q²)` on `(q, p)`:
`q̇ = ∂H/∂p = β q + α p`, `ṗ = −∂H/∂q = −γ q − β p`. -/
def quadraticGenerator (α β γ : K) : Matrix (Fin 2) (Fin 2) K := !![β, α; -γ, -β]

/-- [definition] The energy metric of `H` on `(q, p)`: `2H = (q, p) G_H (q, p)ᵀ`. -/
def quadraticEnergy (α β γ : K) : Matrix (Fin 2) (Fin 2) K := !![γ, β; β, α]

/-- [proved-standard; formal-checked] The generator is traceless with determinant `αγ − β²`, the
determinant of the energy metric. -/
theorem quadraticGenerator_trace_det (α β γ : K) :
    (quadraticGenerator α β γ).trace = 0 ∧ (quadraticGenerator α β γ).det = α * γ - β ^ 2 ∧
      (quadraticEnergy α β γ).det = (quadraticGenerator α β γ).det := by
  simp only [quadraticGenerator, quadraticEnergy, Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  refine ⟨by ring, by ring, by ring⟩

/-- [proved-standard; formal-checked] **The flow turns its own energy:** `X = J G_H` with the
symplectic `J = [[0, 1], [−1, 0]]`, so `X` is `G_H`-skew and conserves `H`. -/
theorem quadraticGenerator_is_turn_of_energy (α β γ : K) :
    quadraticGenerator α β γ = !![0, 1; -1, 0] * quadraticEnergy α β γ ∧
      quadraticEnergy α β γ * quadraticGenerator α β γ +
        (quadraticGenerator α β γ)ᵀ * quadraticEnergy α β γ = 0 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [quadraticGenerator, quadraticEnergy]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quadraticGenerator, quadraticEnergy, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **Cayley–Hamilton for the traceless generator:**
`X² = −(det X)·1`. -/
theorem quadraticGenerator_sq (α β γ : K) :
    quadraticGenerator α β γ * quadraticGenerator α β γ =
      -(quadraticGenerator α β γ).det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [(quadraticGenerator_trace_det α β γ).2.1]
  simp only [quadraticGenerator, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- [proved-standard; formal-checked] **`det X = ω²`: a turn**, `X² = −ω²·1`. -/
theorem quadratic_turn {α β γ ω : K} (hω : ω ^ 2 = (quadraticGenerator α β γ).det) :
    quadraticGenerator α β γ * quadraticGenerator α β γ = -(ω ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [quadraticGenerator_sq, hω]

/-- [proved-standard; formal-checked] **`det X = −r²`: a boost**, `X² = r²·1`, eigenvalues `±r`. -/
theorem quadratic_boost {α β γ r : K} (hr : r ^ 2 = -(quadraticGenerator α β γ).det) :
    quadraticGenerator α β γ * quadraticGenerator α β γ = r ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [quadraticGenerator_sq, hr]

/-- [proved-standard; formal-checked] **`det X = 0`: free fall**, a nilpotent shear `X² = 0`
whose exact steps `1 + sX` compose additively, `(1 + sX)(1 + tX) = 1 + (s + t)X`. -/
theorem quadratic_fall {α β γ : K} (h0 : (quadraticGenerator α β γ).det = 0) (s t : K) :
    quadraticGenerator α β γ * quadraticGenerator α β γ = 0 ∧
      (1 + s • quadraticGenerator α β γ) * (1 + t • quadraticGenerator α β γ) =
        1 + (s + t) • quadraticGenerator α β γ := by
  have hsq : quadraticGenerator α β γ * quadraticGenerator α β γ = 0 := by
    rw [quadraticGenerator_sq, h0, neg_zero, zero_smul]
  refine ⟨hsq, ?_⟩
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hsq, smul_zero, smul_zero, add_smul]
  abel

/-- [proved-standard; formal-checked] **The free particle** `H = p²/(2m)`: its step is the shear
`1 + hX = [[1, h/m], [0, 1]]`. -/
theorem free_particle_step {F : Type*} [Field F] (m h : F) :
    1 + h • quadraticGenerator m⁻¹ 0 0 = !![1, h / m; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadraticGenerator, div_eq_mul_inv]

/-- [proved-standard; formal-checked] **A turn's energy is definite:** `α > 0` and `αγ − β² > 0`
make `α p² + 2β p q + γ q² > 0` off the origin, since
`α(α p² + 2β p q + γ q²) = (α p + β q)² + (αγ − β²) q²`. -/
theorem quadratic_turn_energy_pos {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {α β γ q p : F} (hα : 0 < α) (hdet : 0 < α * γ - β ^ 2) (hqp : q ≠ 0 ∨ p ≠ 0) :
    0 < α * p ^ 2 + 2 * β * p * q + γ * q ^ 2 := by
  have key : α * (α * p ^ 2 + 2 * β * p * q + γ * q ^ 2) =
      (α * p + β * q) ^ 2 + (α * γ - β ^ 2) * q ^ 2 := by ring
  have hpos : 0 < (α * p + β * q) ^ 2 + (α * γ - β ^ 2) * q ^ 2 := by
    by_cases hq : q = 0
    · subst hq
      have hp : p ≠ 0 := hqp.resolve_left (fun h ↦ h rfl)
      have : 0 < (α * p) ^ 2 := by positivity
      simpa using this
    · have : 0 < (α * γ - β ^ 2) * q ^ 2 := mul_pos hdet (by positivity)
      nlinarith [sq_nonneg (α * p + β * q)]
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos hα.le

end QuadraticMotion

/-! ## 11. Iwasawa for `SL(2)`: a turn, a boost and a shear -/

section Iwasawa

variable {K : Type*} [Field K]

/-- [definition] The turn chart `[[x, −y], [y, x]]`. -/
def turnChart (x y : K) : Matrix (Fin 2) (Fin 2) K := !![x, -y; y, x]

/-- [definition] The boost chart `diag(s, s⁻¹)`. -/
def boostChart (s : K) : Matrix (Fin 2) (Fin 2) K := !![s, 0; 0, s⁻¹]

/-- [definition] The shear chart `[[1, u], [0, 1]]`, free fall's step. -/
def shearChart (u : K) : Matrix (Fin 2) (Fin 2) K := !![1, u; 0, 1]

/-- [proved-standard; formal-checked] **Iwasawa, undivided in `r`.** For `ad − bc = 1` and any `r`
with `r² = a² + c²`, `r ≠ 0`: `M = K · diag(r, r⁻¹) · [[1, (ab + cd)/r²], [0, 1]]` with
`K = [[a/r, −c/r], [c/r, a/r]]` orthogonal, `KᵀK = 1`. It holds in any field containing the root. -/
theorem iwasawa {a b c d r : K} (hdet : a * d - b * c = 1) (hr : r ^ 2 = a ^ 2 + c ^ 2)
    (hr0 : r ≠ 0) :
    !![a, b; c, d] =
        turnChart (a / r) (c / r) * boostChart r * shearChart ((a * b + c * d) / r ^ 2) ∧
      (turnChart (a / r) (c / r))ᵀ * turnChart (a / r) (c / r) = 1 := by
  constructor
  · simp only [turnChart, boostChart, shearChart, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j
    · simp; field_simp
    · simp; field_simp; linear_combination b * hr - c * hdet
    · simp; field_simp
    · simp; field_simp; linear_combination d * hr + a * hdet
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [turnChart, Matrix.mul_apply, Fin.sum_univ_two]; field_simp; linear_combination -hr
    · simp [turnChart, Matrix.mul_apply, Fin.sum_univ_two]; field_simp; ring
    · simp [turnChart, Matrix.mul_apply, Fin.sum_univ_two]; field_simp; ring
    · simp [turnChart, Matrix.mul_apply, Fin.sum_univ_two]; field_simp; linear_combination -hr

/-- [proved-standard; formal-checked] **The Iwasawa factors are unique** once the boost is
positive: if `M = [[x, −y], [y, x]] · diag(s, s⁻¹) · [[1, u], [0, 1]]` with `x² + y² = 1` and
`s > 0`, then `s = r`, `x = a/r`, `y = c/r` and `u = (ab + cd)/r²` for the positive `r` with
`r² = a² + c²`. -/
theorem iwasawa_unique {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {a b c d r x y s u : F} (hr : r ^ 2 = a ^ 2 + c ^ 2) (hr0 : 0 < r) (hxy : x ^ 2 + y ^ 2 = 1)
    (hs : 0 < s) (hM : !![a, b; c, d] = turnChart x y * boostChart s * shearChart u) :
    s = r ∧ x = a / r ∧ y = c / r ∧ u = (a * b + c * d) / r ^ 2 := by
  simp only [turnChart, boostChart, shearChart, Matrix.mul_fin_two] at hM
  have h00 := congrFun (congrFun hM 0) 0
  have h01 := congrFun (congrFun hM 0) 1
  have h10 := congrFun (congrFun hM 1) 0
  have h11 := congrFun (congrFun hM 1) 1
  simp at h00 h01 h10 h11
  have hss : s ^ 2 = r ^ 2 := by
    rw [hr, h00, h10]
    linear_combination (-s ^ 2) * hxy
  have hsr : s = r := (sq_eq_sq₀ hs.le hr0.le).mp hss
  subst hsr
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [h00]; field_simp
  · rw [h10]; field_simp
  · rw [h00, h01, h10, h11]
    field_simp
    linear_combination (-u * s ^ 2) * hxy

end Iwasawa

/-! ## 12. The energy law with a moving metric and forcing -/

section MovingMetric

variable {n K : Type*} [Fintype n] [CommRing K]

/-- [proved-standard; formal-checked] **The energy law, undivided.** Along `ẋ = A x + f` with a
symmetric metric `G` whose rate is `Ġ`, twice the rate of `E = ½ xᵀGx` is
`ẋᵀGx + xᵀĠx + xᵀGẋ = xᵀ(AᵀG + GA + Ġ)x + 2 xᵀG f`. This is the algebraic form; the dynamical
owner in the Holon's quadratic port chart is `Holon/Deposition.learned_energy_balance`. -/
theorem energy_rate_moving_metric {A G Gdot : Matrix n n K} {x f xdot : n → K} (hGs : Gᵀ = G)
    (hx : xdot = A *ᵥ x + f) :
    xdot ⬝ᵥ (G *ᵥ x) + x ⬝ᵥ (Gdot *ᵥ x) + x ⬝ᵥ (G *ᵥ xdot) =
      x ⬝ᵥ ((Aᵀ * G + G * A + Gdot) *ᵥ x) + 2 * (x ⬝ᵥ (G *ᵥ f)) := by
  have hf : f ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ (G *ᵥ f) := by
    have hv : f ᵥ* G = G *ᵥ f := by
      conv_lhs => rw [← hGs]
      exact Matrix.vecMul_transpose G f
    rw [Matrix.dotProduct_mulVec, dotProduct_comm, hv]
  have hA : (A *ᵥ x) ⬝ᵥ (G *ᵥ x) = x ⬝ᵥ ((Aᵀ * G) *ᵥ x) := by
    rw [← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  subst hx
  rw [add_dotProduct, hA, hf, Matrix.mulVec_add, dotProduct_add, Matrix.mulVec_mulVec,
    Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add]
  ring

variable [DecidableEq n] [Invertible (2 : K)]

/-- [proved-derived; formal-checked] **Boost, deposition and push.** The same rate is the
boost's work, the moving metric's work and the push's power:
`ẋᵀGx + xᵀĠx + xᵀGẋ = 2 xᵀG B x + xᵀĠx + 2 xᵀG f` with `B = boost G A`. -/
theorem energy_rate_moving_metric_boost {A G Gdot : Matrix n n K} {x f xdot : n → K}
    (hG : IsUnit G.det) (hGs : Gᵀ = G) (hx : xdot = A *ᵥ x + f) :
    xdot ⬝ᵥ (G *ᵥ x) + x ⬝ᵥ (Gdot *ᵥ x) + x ⬝ᵥ (G *ᵥ xdot) =
      2 * (x ⬝ᵥ (G *ᵥ (boost G A *ᵥ x))) + x ⬝ᵥ (Gdot *ᵥ x) + 2 * (x ⬝ᵥ (G *ᵥ f)) := by
  rw [energy_rate_moving_metric hGs hx, Matrix.add_mulVec, dotProduct_add, add_comm (Aᵀ * G),
    ← rate_quadratic, energy_rate_is_boost hG]

end MovingMetric

end Holonics.Geometry.Motion

section Audit
open Holonics.Geometry.Motion
#print axioms turn_add_boost
#print axioms turn_isSkew
#print axioms boost_isSymm
#print axioms turn_boost_unique
#print axioms skew_rate_conserves
#print axioms energy_rate_is_boost
#print axioms complex_rate_split
#print axioms turn_portHamiltonian
#print axioms boost_portHamiltonian
#print axioms move_about_pivot
#print axioms move_fixes_iff_pivot
#print axioms pivot_unique
#print axioms move_comp
#print axioms translation_has_no_pivot
#print axioms move_about_axis_then_falls
#print axioms complex_move_about_pivot
#print axioms complex_move_is_pantograph
#print axioms complex_fall_has_no_pivot
#print axioms swing_is_half_turn_move
#print axioms swing_pivot_is_anchor
#print axioms multiplier_cross_ratio
#print axioms multiplier_trace_det_undivided
#print axioms multiplier_trace_det
#print axioms multiplier_half_turn_iff_traceless
#print axioms multiplier_ratio_half_turn_iff_traceless
#print axioms swing_word_linear_part
#print axioms even_swing_word_is_translation
#print axioms odd_swing_word_is_point_reflection
#print axioms odd_swing_word_is_swing
#print axioms det_half_turn_odd
#print axioms power_is_boost_rate
#print axioms normal_effort_is_turn_rate
#print axioms sling_energy_gain
#print axioms sling_speed_gain
#print axioms traction_disk
#print axioms turn_distance_from_one
#print axioms turn_by_angle_distance_from_one
#print axioms velocity_rate_is_log_derivative
#print axioms acceleration_and_jerk
#print axioms bellJet_two
#print axioms derivation_iterate_of_log_rate
#print axioms position_jets
#print axioms rates_from_effort
#print axioms quadraticGenerator_trace_det
#print axioms quadraticGenerator_is_turn_of_energy
#print axioms quadraticGenerator_sq
#print axioms quadratic_turn
#print axioms quadratic_boost
#print axioms quadratic_fall
#print axioms free_particle_step
#print axioms quadratic_turn_energy_pos
#print axioms iwasawa
#print axioms iwasawa_unique
#print axioms energy_rate_moving_metric
#print axioms energy_rate_moving_metric_boost
end Audit

import Holonics.Geometry.Motion

/-!
# A linear diffusion: its stationary metric reads the drift as excess and housekeeping

[definition] Issue #410; the swing record, §5.4:
`research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md`.
A linear diffusion has the drift `A` and the noise covariance rate `D` (`Dᵀ = D`). Its
stationary metric `G` is the precision of its stationary law, `G = Σ⁻¹`, and the receiver of that
metric splits the drift by `Geometry/Motion` into a turn and a boost. The stationary law fixes the
boost and leaves the turn free. The boost is the excess part, the relaxation toward the stationary
law. The turn is the housekeeping part, the current that persists at stationarity.

[proved-standard] The analytic chart, cited and not formalized here.
- The process is `dx = A x dt + dW` with `⟨dW dWᵀ⟩ = D dt`. Its law obeys the Fokker–Planck
  equation `∂ₜp = −∇·(A x p) + ½ ∇·(D ∇p)`.
- The Gaussian `p ∝ exp(−½ xᵀ G x)` is stationary exactly when the Lyapunov equation
  `A Σ + Σ Aᵀ + D = 0` holds (for a stable `A` and `D ⪰ 0` it is the unique stationary law).
- The stationary probability current is `J(x) = (A + ½ D G) x · p(x)`.
- The time-reversed stationary process is a diffusion with the same `D` and the drift
  `−A x + D ∇log p = (−A − D G) x` (Anderson, 1982; Haussmann and Pardoux, 1986). The process is
  reversible, its law equal to that of its time reversal, exactly when the two drifts agree.
- The entropy production splits into a housekeeping part, `∫ (J/p)ᵀ (½D)⁻¹ (J/p) p`, which keeps the
  stationary current, and an excess part, which drives relaxation and vanishes at stationarity
  (Hatano and Sasa, 2001). The drift is `A = (J − ½ D) G` with `J` skew (Kwon, Ao and Thouless,
  2005).

[proved-derived; formal-checked] What is proved, over a commutative ring with `⅟2` and an
invertible symmetric `G`.

1. **The stationary law in its own metric** (`Stationary`, `stationary_iff_covariance`): the
   Lyapunov equation is `G A + Aᵀ G + G D G = 0`.
2. **The reversed drift is the adjoint in the stationary metric**
   (`adjointIn_of_stationary`): `G⁻¹ Aᵀ G = Σ Aᵀ Σ⁻¹ = −A − D G`.
3. **The stationary law fixes the boost** (`boost_of_stationary`): `boost_G A = −½ D G`, the
   gradient flow of the stationary potential `½ xᵀ G x` with mobility `½ D`. This is the excess
   part. Only it changes the stationary potential (`potential_rate_of_stationary`).
4. **The turn is the current** (`turn_of_stationary`): `turn_G A = A + ½ D G`, the coefficient of
   the stationary current. This is the housekeeping part.
5. **The turn is free** (`stationary_add_iff`, `stationary_iff_portHamiltonian`): adding a rate
   keeps the stationary law exactly when the rate is `G`-skew, and the drifts with stationary law
   `(G, D)` are exactly the port-Hamiltonian rates `(J − ½ D) G` with `Jᵀ = −J`. Through
   `Geometry/Motion.turn_portHamiltonian` the interconnection `J` is the circulation and the
   resistance is half the noise.
6. **The stationary current circulates** (`trace_eq_zero_of_skew`, `current_tangent`): a
   `G`-skew rate has trace zero and `(T x)·(G x) = 0`. So `∇·J = (tr T − (T x)·(G x)) p = 0`: the
   current is divergence-free and runs along the level sets of the stationary law.
7. **Reversible exactly when there is no turn** (`reversible_iff`): the reversed drift equals the
   drift, the turn vanishes, `G A = Aᵀ G` (`A Σ = Σ Aᵀ`), and `A = −½ D G` are equivalent. Against
   any resistance `M` positive on nonzero vectors (`M = (½D)⁻¹` in the chart), the housekeeping
   density `(T x)·M(T x)` is nonnegative (`housekeeping_nonneg`) and vanishes everywhere exactly
   when the turn does (`reversible_iff_no_housekeeping`).

[counterexample; formal-checked] **The stationary law does not decide the arrow**
(`same_law_two_arrows`). Over `ℚ` with `G = 1` and `D = 2`, the drifts `[[−1, −1], [1, −1]]` and
`−1` share the stationary law. The first has the turn `[[0, −1], [1, 0]]` and is irreversible. The
second has no turn and is reversible.

This is the linear-diffusion face of `ChainAxes`: there a stationary arrow lives on a ring's cycle
current, here on the turn. Rust owner: none. No machinery consumes a continuous diffusion; this is
a physical instance stated for the thermal law.
-/

namespace Holonics.Physics.Thermal.LinearDiffusion

open Matrix Holonics.Geometry.Motion

section Split

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K]

/-- [definition] **The stationary law of a linear diffusion**, written in its stationary metric
`G = Σ⁻¹`: the drift `A` and noise covariance rate `D` satisfy `G A + Aᵀ G + G D G = 0`. -/
def Stationary (G A D : Matrix n n K) : Prop := G * A + Aᵀ * G + G * D * G = 0

/-- [proved-standard; formal-checked] The stationary law is the Lyapunov equation
`A Σ + Σ Aᵀ + D = 0` with `Σ = G⁻¹`. -/
theorem stationary_iff_covariance {G A D : Matrix n n K} (hG : IsUnit G.det) :
    Stationary G A D ↔ A * G⁻¹ + G⁻¹ * Aᵀ + D = 0 := by
  have hconj : ∀ X : Matrix n n K, G⁻¹ * (G * X * G) * G⁻¹ = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.mul_one]
  have hid : G * (A * G⁻¹ + G⁻¹ * Aᵀ + D) * G = G * A + Aᵀ * G + G * D * G := by
    simp only [Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG,
      Matrix.one_mul]
    rw [Matrix.mul_assoc _ G⁻¹ G, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]
  rw [Stationary, ← hid]
  constructor
  · intro h
    rw [← hconj (A * G⁻¹ + G⁻¹ * Aᵀ + D), h, Matrix.mul_zero, Matrix.zero_mul]
  · intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul]

/-- [proved-standard; formal-checked] **The reversed drift is the adjoint in the stationary
metric:** `G⁻¹ Aᵀ G = −A − D G`, the drift `−A + D ∇log p` of the time-reversed process. -/
theorem adjointIn_of_stationary {G A D : Matrix n n K} (hG : IsUnit G.det)
    (h : Stationary G A D) : adjointIn G A = -A - D * G := by
  have h' : Aᵀ * G = -(G * A) - G * D * G :=
    eq_of_sub_eq_zero (by rw [← h]; abel)
  rw [adjointIn, Matrix.mul_assoc, h', Matrix.mul_sub, Matrix.mul_neg, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul G hG, Matrix.one_mul, Matrix.mul_assoc G D G, ← Matrix.mul_assoc G⁻¹,
    Matrix.nonsing_inv_mul G hG, Matrix.one_mul]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **Two drifts with one stationary law differ by a `G`-skew
rate, and only by one:** adding `T` keeps the stationary law exactly when `G T + Tᵀ G = 0`. -/
theorem stationary_add_iff {G A D : Matrix n n K} (h : Stationary G A D) (T : Matrix n n K) :
    Stationary G (A + T) D ↔ G * T + Tᵀ * G = 0 := by
  have hsplit : G * (A + T) + (A + T)ᵀ * G + G * D * G =
      (G * A + Aᵀ * G + G * D * G) + (G * T + Tᵀ * G) := by
    rw [Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]; abel
  have h0 : G * A + Aᵀ * G + G * D * G = 0 := h
  rw [Stationary, hsplit, h0, zero_add]

omit [Fintype n] [DecidableEq n] in
private theorem half_add_half (x : Matrix n n K) [Invertible (2 : K)] :
    (⅟2 : K) • x + (⅟2 : K) • x = x := by
  rw [← add_smul, invOf_two_add_invOf_two, one_smul]

variable [Invertible (2 : K)]

/-- [proved-derived; formal-checked] **The stationary law fixes the boost:** read by its
stationary metric, the drift's boost is `−½ D G`, the excess part. -/
theorem boost_of_stationary {G A D : Matrix n n K} (hG : IsUnit G.det) (h : Stationary G A D) :
    boost G A = -((⅟2 : K) • (D * G)) := by
  rw [boost, adjointIn_of_stationary hG h, show A + (-A - D * G) = -(D * G) by abel, smul_neg]

/-- [proved-derived; formal-checked] **The turn is the stationary current:** read by its
stationary metric, the drift's turn is `A + ½ D G`, the coefficient of `J(x) = (A + ½ D G) x p`,
the housekeeping part. -/
theorem turn_of_stationary {G A D : Matrix n n K} (hG : IsUnit G.det) (h : Stationary G A D) :
    turn G A = A + (⅟2 : K) • (D * G) := by
  rw [turn, adjointIn_of_stationary hG h,
    show A - (-A - D * G) = (A + (⅟2 : K) • (D * G)) + (A + (⅟2 : K) • (D * G)) by
      rw [show (A + (⅟2 : K) • (D * G)) + (A + (⅟2 : K) • (D * G)) =
        A + A + ((⅟2 : K) • (D * G) + (⅟2 : K) • (D * G)) by abel, half_add_half]; abel,
    smul_add, half_add_half]

omit [DecidableEq n] [Invertible (2 : K)] in
/-- [proved-derived; formal-checked] **Only the excess changes the stationary potential:** along
the drift, the rate of `½ xᵀ G x` is `−½ xᵀ G D G x`; the turn contributes nothing
(`Geometry/Motion.skew_rate_conserves`). -/
theorem potential_rate_of_stationary {G A D : Matrix n n K} (h : Stationary G A D) (x : n → K) :
    x ⬝ᵥ (G *ᵥ (A *ᵥ x)) + (A *ᵥ x) ⬝ᵥ (G *ᵥ x) = -(x ⬝ᵥ ((G * D * G) *ᵥ x)) := by
  rw [rate_quadratic, show G * A + Aᵀ * G = -(G * D * G) from eq_neg_of_add_eq_zero_left h,
    Matrix.neg_mulVec, dotProduct_neg]

/-- [proved-standard; formal-checked] **Kwon–Ao–Thouless:** the drifts with stationary law
`(G, D)` are exactly the port-Hamiltonian rates `(J − ½ D) G` with `J` skew. -/
theorem stationary_iff_portHamiltonian {G A D : Matrix n n K} (hG : IsUnit G.det)
    (hGs : Gᵀ = G) (hD : Dᵀ = D) :
    Stationary G A D ↔ ∃ J : Matrix n n K, Jᵀ = -J ∧ A = (J - (⅟2 : K) • D) * G := by
  constructor
  · intro h
    refine ⟨A * G⁻¹ + (⅟2 : K) • D, ?_, ?_⟩
    · have hc := (stationary_iff_covariance hG).1 h
      apply eq_neg_of_add_eq_zero_left
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hGs,
        Matrix.transpose_smul, hD, ← hc,
        show G⁻¹ * Aᵀ + (⅟2 : K) • D + (A * G⁻¹ + (⅟2 : K) • D) =
          A * G⁻¹ + G⁻¹ * Aᵀ + ((⅟2 : K) • D + (⅟2 : K) • D) by abel, half_add_half]
    · rw [add_sub_cancel_right, Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.mul_one]
  · rintro ⟨J, hJ, rfl⟩
    have hfold : G * ((J - (⅟2 : K) • D) * G) + ((J - (⅟2 : K) • D) * G)ᵀ * G + G * D * G =
        G * ((J + Jᵀ) + (D - ((⅟2 : K) • D + (⅟2 : K) • D))) * G := by
      rw [Matrix.transpose_mul, hGs, Matrix.transpose_sub, Matrix.transpose_smul, hD]
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      abel
    rw [Stationary, hfold, hJ, half_add_half, add_neg_cancel, sub_self, add_zero,
      Matrix.mul_zero, Matrix.zero_mul]

/-- [proved-derived; formal-checked] **A `G`-skew rate has trace zero:**
`tr T = tr(G⁻¹ G T) = −tr(G⁻¹ Tᵀ G) = −tr T`. -/
theorem trace_eq_zero_of_skew {G T : Matrix n n K} (hG : IsUnit G.det)
    (hT : G * T + Tᵀ * G = 0) : T.trace = 0 := by
  have h' : G * T = -(Tᵀ * G) := eq_neg_of_add_eq_zero_left hT
  have hneg : T.trace = -T.trace := by
    calc T.trace = (G⁻¹ * (G * T)).trace := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul G hG, Matrix.one_mul]
      _ = -(G⁻¹ * (Tᵀ * G)).trace := by rw [h', Matrix.mul_neg, Matrix.trace_neg]
      _ = -((Tᵀ * G) * G⁻¹).trace := by rw [Matrix.trace_mul_comm]
      _ = -T.trace := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv G hG, Matrix.mul_one,
            Matrix.trace_transpose]
  have h2 : (2 : K) * T.trace = 0 := by rw [two_mul]; nth_rewrite 2 [hneg]; exact add_neg_cancel _
  rw [← one_mul T.trace, ← invOf_mul_self (2 : K), mul_assoc, h2, mul_zero]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The current runs along the level sets:** for symmetric `G`
and `G`-skew `T`, `(T x)·(G x) = 0`. -/
theorem current_tangent {G T : Matrix n n K} (hGs : Gᵀ = G) (hT : G * T + Tᵀ * G = 0)
    (x : n → K) : (T *ᵥ x) ⬝ᵥ (G *ᵥ x) = 0 := by
  have h := skew_rate_conserves hT x
  have hsym : x ⬝ᵥ (G *ᵥ (T *ᵥ x)) = (T *ᵥ x) ⬝ᵥ (G *ᵥ x) := by
    rw [Matrix.dotProduct_mulVec, ← hGs, Matrix.vecMul_transpose, hGs, dotProduct_comm]
  rw [hsym, ← two_mul] at h
  rw [← one_mul ((T *ᵥ x) ⬝ᵥ (G *ᵥ x)), ← invOf_mul_self (2 : K), mul_assoc, h, mul_zero]

/-- [proved-derived; formal-checked] **The stationary current circulates:** its coefficient, the
turn, has trace zero and runs along the level sets of the stationary law, so
`∇·J = (tr T − (T x)·(G x)) p = 0`. -/
theorem stationary_current_circulates {G A D : Matrix n n K} (hG : IsUnit G.det) (hGs : Gᵀ = G)
    (h : Stationary G A D) :
    (A + (⅟2 : K) • (D * G)).trace = 0 ∧
      ∀ x, ((A + (⅟2 : K) • (D * G)) *ᵥ x) ⬝ᵥ (G *ᵥ x) = 0 := by
  rw [← turn_of_stationary hG h]
  exact ⟨trace_eq_zero_of_skew hG (turn_isSkew hG hGs A),
    current_tangent hGs (turn_isSkew hG hGs A)⟩

/-- [proved-standard; formal-checked] **A linear diffusion is reversible exactly when its drift has
no turn against its stationary metric.** Under the stationary law these are equivalent: the
reversed drift equals the drift, the turn vanishes, `G A = Aᵀ G` (detailed balance, `A Σ = Σ Aᵀ`),
and the drift is the pure excess `−½ D G`. -/
theorem reversible_iff {G A D : Matrix n n K} (hG : IsUnit G.det) (h : Stationary G A D) :
    (adjointIn G A = A ↔ turn G A = 0) ∧ (turn G A = 0 ↔ G * A = Aᵀ * G) ∧
      (turn G A = 0 ↔ A = -((⅟2 : K) • (D * G))) := by
  have hrev : adjointIn G A = A ↔ turn G A = 0 := by
    constructor
    · intro he
      rw [turn, he, sub_self, smul_zero]
    · intro ht
      have hsub : A - adjointIn G A = 0 := by
        rw [← one_smul K (A - adjointIn G A), ← mul_invOf_self (2 : K), mul_smul, ← turn, ht,
          smul_zero]
      exact (sub_eq_zero.1 hsub).symm
  refine ⟨hrev, ?_, ?_⟩
  · rw [← hrev]
    constructor
    · intro he
      rw [← mul_adjointIn hG, he]
    · exact adjointIn_eq_self_of_symm hG
  · rw [turn_of_stationary hG h, add_eq_zero_iff_eq_neg]

end Split

/-! ## The housekeeping production -/

section Housekeeping

variable {n K : Type*} [Fintype n] [DecidableEq n] [CommRing K] [PartialOrder K]

/-- [definition] **The housekeeping density** of a stationary current of coefficient `T` against
the resistance `M`: `(T x)·M(T x)`. In the analytic chart `M = (½D)⁻¹` and the housekeeping
production is its mean over the stationary law. -/
def housekeeping (M T : Matrix n n K) (x : n → K) : K := (T *ᵥ x) ⬝ᵥ (M *ᵥ (T *ᵥ x))

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] The housekeeping density is nonnegative against a resistance
positive on nonzero vectors. -/
theorem housekeeping_nonneg {M : Matrix n n K} (hM : ∀ y : n → K, y ≠ 0 → 0 < y ⬝ᵥ (M *ᵥ y))
    (T : Matrix n n K) (x : n → K) : 0 ≤ housekeeping M T x := by
  by_cases hy : T *ᵥ x = 0
  · rw [housekeeping, hy, Matrix.mulVec_zero, dotProduct_zero]
  · exact le_of_lt (hM _ hy)

/-- [proved-derived; formal-checked] The housekeeping density vanishes everywhere exactly when the
current's coefficient does. -/
theorem housekeeping_eq_zero_iff {M : Matrix n n K}
    (hM : ∀ y : n → K, y ≠ 0 → 0 < y ⬝ᵥ (M *ᵥ y)) (T : Matrix n n K) :
    (∀ x, housekeeping M T x = 0) ↔ T = 0 := by
  constructor
  · intro h
    ext i j
    by_contra hij
    have hy : T *ᵥ Pi.single j 1 ≠ 0 := by
      intro h0
      apply hij
      have := congrFun h0 i
      simpa [Matrix.mulVec_single_one, Matrix.col_apply] using this
    exact (ne_of_gt (hM _ hy)) (h (Pi.single j 1))
  · rintro rfl x
    rw [housekeeping, Matrix.zero_mulVec, zero_dotProduct]

variable [Invertible (2 : K)]

/-- [proved-standard; formal-checked] **Reversible exactly when no housekeeping is produced:**
under the stationary law, the reversed drift equals the drift exactly when the housekeeping
density of the turn vanishes everywhere. -/
theorem reversible_iff_no_housekeeping {G A D M : Matrix n n K} (hG : IsUnit G.det)
    (h : Stationary G A D) (hM : ∀ y : n → K, y ≠ 0 → 0 < y ⬝ᵥ (M *ᵥ y)) :
    adjointIn G A = A ↔ ∀ x, housekeeping M (turn G A) x = 0 := by
  rw [housekeeping_eq_zero_iff hM]
  exact (reversible_iff hG h).1

end Housekeeping

/-! ## The stationary law does not decide the arrow -/

section Witness

/-- [counterexample; formal-checked] **One stationary law, two arrows.** With `G = 1` and `D = 2`
over `ℚ`, the drifts `[[−1, −1], [1, −1]]` and `−1` are both stationary. The first has the turn
`[[0, −1], [1, 0]]`, a circulation, and is irreversible. The second has no turn and is
reversible. -/
theorem same_law_two_arrows :
    Stationary (1 : Matrix (Fin 2) (Fin 2) ℚ) !![-1, -1; 1, -1] !![2, 0; 0, 2] ∧
      Stationary (1 : Matrix (Fin 2) (Fin 2) ℚ) (-1) !![2, 0; 0, 2] ∧
      turn (1 : Matrix (Fin 2) (Fin 2) ℚ) !![-1, -1; 1, -1] = !![0, -1; 1, 0] ∧
      adjointIn (1 : Matrix (Fin 2) (Fin 2) ℚ) !![-1, -1; 1, -1] ≠ !![-1, -1; 1, -1] ∧
      adjointIn (1 : Matrix (Fin 2) (Fin 2) ℚ) (-1) = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [Stationary, Matrix.one_mul, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · simp only [Stationary, Matrix.one_mul, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> norm_num
  · simpa using (complex_rate_split (K := ℚ) (-1) 1).1
  · rw [adjointIn_one]
    intro h
    have := congrFun (congrFun h 0) 1
    simp at this
    norm_num at this
  · rw [adjointIn_one, Matrix.transpose_neg, Matrix.transpose_one]

end Witness

section Audit

#print axioms stationary_iff_covariance
#print axioms adjointIn_of_stationary
#print axioms stationary_add_iff
#print axioms boost_of_stationary
#print axioms turn_of_stationary
#print axioms potential_rate_of_stationary
#print axioms stationary_iff_portHamiltonian
#print axioms trace_eq_zero_of_skew
#print axioms current_tangent
#print axioms stationary_current_circulates
#print axioms reversible_iff
#print axioms housekeeping_nonneg
#print axioms housekeeping_eq_zero_iff
#print axioms reversible_iff_no_housekeeping
#print axioms same_law_two_arrows

end Audit

end Holonics.Physics.Thermal.LinearDiffusion

import Mathlib

/-!
# The information form of a comparison's update: precisions add, in any order

[proved-standard] The source is the learner record of September 27
(`research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md`,
§5 "Overcorrection is tampering", plan item 11 "Gain by precision" and §14.6 "Gain"). The record cites the Kalman gain
(Kalman, 1960) as the weight of a correction, the ratio of the prior's uncertainty to the total, and names the normal
law's deposit `H ← H + w f fᵀ` as the information-form slot, with `w` the reading's precision.

The statements are matrix algebra over a field, with no probability: a prior holds a precision `Λ` and an information
vector `η = Λ μ`; a comparison through an observation map `H` with noise precision `W` and reading `y` deposits

  `Λ′ = Λ + Hᵀ W H`,  `η′ = η + Hᵀ W y`.

What is proved.

1. **Deposits add and commute.** Two comparisons taken in either order give the same pair
   (`precision_comm`, `information_comm`), and so does the one stacked comparison that holds both
   (`precision_stacked`, `information_stacked`). A list of comparisons deposits the sum of its terms
   (`depositAll_eq`), so every reordering of the list gives the same pair (`depositAll_perm`). This is the precision
   law's schedule-free sum: the terms meet at one grain and nothing is released between them.
2. **The covariance form is the same update.** With `P = Λ⁻¹`, `R = W⁻¹` and `S = R + H P Hᵀ` invertible,
   `Λ′ (P Hᵀ) = Hᵀ R⁻¹ S` (`precision_mul_covariance_transpose`), hence
   `Λ′⁻¹ = P − P Hᵀ S⁻¹ H P` (`covariance_form`, Woodbury's identity, proved here from that one line), the gain is
   `K = P Hᵀ S⁻¹ = Λ′⁻¹ Hᵀ R⁻¹` (`gain_eq`), the covariance after is `(1 − K H) P` (`covariance_eq_one_sub_gain`), and
   the mean `μ′ = μ + K (y − H μ)` is `Λ′⁻¹ η′` (`mean_update`).
3. **The mean is the cost's stationary point.** For symmetric `Λ` and `W` the doubled cost
   `(x − μ)ᵀ Λ (x − μ) + (y − H x)ᵀ W (y − H x)` satisfies
   `cost (x + h) = cost x + 2 hᵀ(Λ′ x − η′) + hᵀ Λ′ h` (`cost_add`), so its slope vanishes where the normal equation
   `Λ′ x = η′` holds (`slope_eq_zero_iff`), there the cost is `cost x + hᵀ Λ′ h` (`cost_at_stationary`), and over the
   reals with `Λ′` positive semidefinite that point is a least one (`stationary_is_least`). With the inverses of
   statement 2 the normal equation has the one solution `μ + K (y − H μ)` (`stationary_iff_mean`).
4. **Precision never falls.** Over the reals, `Λ′ − Λ = Hᵀ W H` is positive semidefinite when `W` is
   (`precision_gain_posSemidef`), and `Λ′` is positive semidefinite when `Λ` and `W` are (`precision_posSemidef`).
5. **The record's slot.** One reading along a covector `f` with precision `w` deposits `w f fᵀ`
   (`rank_one_slot`), and its information vector gains `w y f` (`rank_one_information`).
6. **The scalar ruler of §14.6.** With variances `P`, `R`: the information form `(m/P + y/R)/(1/P + 1/R)` is
   `m + K (y − m)` at `K = P/(P + R)` (`scalar_gain`); the precision after is the sum `1/P + 1/R`
   (`scalar_precision_adds`); the cost is a square about that point plus a constant (`scalar_square`), so over an
   ordered field it is least there (`scalar_least`).

Limits. No law of probability is stated: that the two quadratic terms are a Gaussian prior's and a Gaussian reading's
code lengths is the reading, and the statements hold for any symmetric forms. The noise precision is declared, never
derived from a grain's width (the record's counterexample of §14.6: one interval carries laws of two variances). The
prediction step of the filter (a transport between readings) is not here; statement 1 is of comparisons at one grain
with no transport and no release between them.

The computational object is the helical pair interaction: a comparison is a pair contact's reading, and its deposit
`Hᵀ W H` is the contact material `Σ w J* D J` of one slip. Of the winding guide's six general objects this touches the
pair (the comparison and its covector) and faces and placement (the grain at which the terms meet); the helix, cell
holonomy, tube and tower thread stay attached.

Consumers: #410's box "Classical results cited in the learner record … the Kalman information-form update"; the
deposition step's Gram `H ← H + w f fᵀ` (the record's item 11); the precision law's schedule-free sum in the
repository's guide.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.InformationUpdate

open Matrix

section Deposit

variable {n m m₁ m₂ : Type*} [Fintype m] [Fintype m₁] [Fintype m₂] {K : Type*} [Field K]

/-- [definition] The precision after a comparison through `H` with noise precision `W`. -/
def precision (Λ : Matrix n n K) (H : Matrix m n K) (W : Matrix m m K) : Matrix n n K :=
  Λ + Hᵀ * W * H

/-- [definition] The information vector after a comparison through `H` with noise precision `W` and reading `y`. -/
def information (η : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K) : n → K :=
  η + (Hᵀ * W) *ᵥ y

/-! ## 1. Deposits add and commute -/

/-- [proved-standard] Two comparisons deposit the same precision in either order. -/
theorem precision_comm (Λ : Matrix n n K) (H₁ : Matrix m₁ n K) (W₁ : Matrix m₁ m₁ K)
    (H₂ : Matrix m₂ n K) (W₂ : Matrix m₂ m₂ K) :
    precision (precision Λ H₁ W₁) H₂ W₂ = precision (precision Λ H₂ W₂) H₁ W₁ := by
  unfold precision
  abel

/-- [proved-standard] Two comparisons deposit the same information vector in either order. -/
theorem information_comm (η : n → K) (H₁ : Matrix m₁ n K) (W₁ : Matrix m₁ m₁ K) (y₁ : m₁ → K)
    (H₂ : Matrix m₂ n K) (W₂ : Matrix m₂ m₂ K) (y₂ : m₂ → K) :
    information (information η H₁ W₁ y₁) H₂ W₂ y₂ = information (information η H₂ W₂ y₂) H₁ W₁ y₁ := by
  unfold information
  abel

/-- [proved-standard] **Two comparisons taken together are the two taken in turn**: the stacked observation map with
the block-diagonal noise precision deposits the same precision. -/
theorem precision_stacked (Λ : Matrix n n K) (H₁ : Matrix m₁ n K) (W₁ : Matrix m₁ m₁ K)
    (H₂ : Matrix m₂ n K) (W₂ : Matrix m₂ m₂ K) :
    precision Λ (fromRows H₁ H₂) (fromBlocks W₁ 0 0 W₂) = precision (precision Λ H₁ W₁) H₂ W₂ := by
  unfold precision
  rw [transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp [add_assoc]

/-- [proved-standard] The stacked comparison deposits the same information vector. -/
theorem information_stacked (η : n → K) (H₁ : Matrix m₁ n K) (W₁ : Matrix m₁ m₁ K) (y₁ : m₁ → K)
    (H₂ : Matrix m₂ n K) (W₂ : Matrix m₂ m₂ K) (y₂ : m₂ → K) :
    information η (fromRows H₁ H₂) (fromBlocks W₁ 0 0 W₂) (Sum.elim y₁ y₂)
      = information (information η H₁ W₁ y₁) H₂ W₂ y₂ := by
  unfold information
  rw [transpose_fromRows, fromCols_mul_fromBlocks]
  simp [add_assoc]

/-- [definition] The deposits of a list of comparisons of one shape, taken in the list's order. -/
def depositAll (s : Matrix n n K × (n → K)) (obs : List (Matrix m n K × Matrix m m K × (m → K))) :
    Matrix n n K × (n → K) :=
  obs.foldl (fun s o => (precision s.1 o.1 o.2.1, information s.2 o.1 o.2.1 o.2.2)) s

/-- [proved-standard] **A list of comparisons deposits the sum of its terms.** -/
theorem depositAll_eq (s : Matrix n n K × (n → K)) (obs : List (Matrix m n K × Matrix m m K × (m → K))) :
    depositAll s obs = (s.1 + (obs.map fun o => o.1ᵀ * o.2.1 * o.1).sum,
      s.2 + (obs.map fun o => (o.1ᵀ * o.2.1) *ᵥ o.2.2).sum) := by
  induction obs generalizing s with
  | nil => simp [depositAll]
  | cons o obs ih =>
    have h := ih (precision s.1 o.1 o.2.1, information s.2 o.1 o.2.1 o.2.2)
    simp only [depositAll, List.foldl_cons] at h ⊢
    rw [h]
    simp [precision, information, add_assoc]

/-- [proved-standard] **The deposit is schedule-free**: every reordering of the comparisons gives the same precision
and the same information vector. -/
theorem depositAll_perm (s : Matrix n n K × (n → K)) {obs obs' : List (Matrix m n K × Matrix m m K × (m → K))}
    (h : obs.Perm obs') : depositAll s obs = depositAll s obs' := by
  rw [depositAll_eq, depositAll_eq, (h.map _).sum_eq, (h.map _).sum_eq]

end Deposit

/-! ## 2. The covariance form -/

section Covariance

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] {K : Type*} [Field K]

/-- [proved-standard] The one line the covariance form rests on: `Λ′ (P Hᵀ) = Hᵀ R⁻¹ S` with `P = Λ⁻¹` and
`S = R + H P Hᵀ`. -/
theorem precision_mul_covariance_transpose (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) :
    precision Λ H R⁻¹ * (Λ⁻¹ * Hᵀ) = Hᵀ * R⁻¹ * (R + H * Λ⁻¹ * Hᵀ) := by
  have hΛd := (isUnit_iff_isUnit_det Λ).mp hΛ
  have hRd := (isUnit_iff_isUnit_det R).mp hR
  unfold precision
  rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc Λ, mul_nonsing_inv Λ hΛd, Matrix.one_mul,
    Matrix.mul_assoc Hᵀ R⁻¹ R, nonsing_inv_mul R hRd, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/-- [proved-standard] The covariance form is a right inverse of the precision after. -/
theorem precision_mul_covariance (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    precision Λ H R⁻¹ * (Λ⁻¹ - Λ⁻¹ * Hᵀ * (R + H * Λ⁻¹ * Hᵀ)⁻¹ * H * Λ⁻¹) = 1 := by
  have hΛd := (isUnit_iff_isUnit_det Λ).mp hΛ
  have hSd := (isUnit_iff_isUnit_det _).mp hS
  have key := precision_mul_covariance_transpose Λ H R hΛ hR
  have e1 : precision Λ H R⁻¹ * (Λ⁻¹ * Hᵀ * (R + H * Λ⁻¹ * Hᵀ)⁻¹ * H * Λ⁻¹) = Hᵀ * R⁻¹ * H * Λ⁻¹ := by
    have assoc : Λ⁻¹ * Hᵀ * (R + H * Λ⁻¹ * Hᵀ)⁻¹ * H * Λ⁻¹
        = (Λ⁻¹ * Hᵀ) * ((R + H * Λ⁻¹ * Hᵀ)⁻¹ * (H * Λ⁻¹)) := by
      simp only [Matrix.mul_assoc]
    rw [assoc, ← Matrix.mul_assoc, key, Matrix.mul_assoc (Hᵀ * R⁻¹),
      ← Matrix.mul_assoc (R + H * Λ⁻¹ * Hᵀ), mul_nonsing_inv _ hSd, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  have e2 : precision Λ H R⁻¹ * Λ⁻¹ = 1 + Hᵀ * R⁻¹ * H * Λ⁻¹ := by
    unfold precision
    rw [Matrix.add_mul, mul_nonsing_inv Λ hΛd]
  rw [Matrix.mul_sub, e1, e2]
  abel

/-- [proved-standard] The precision after is invertible when the prior's precision, the noise and `S` are. -/
theorem precision_det_isUnit (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    IsUnit (precision Λ H R⁻¹).det :=
  isUnit_det_of_right_inverse (precision_mul_covariance Λ H R hΛ hR hS)

/-- [proved-standard] **The covariance form** (Woodbury's identity): with `P = Λ⁻¹` and `S = R + H P Hᵀ`,
`(Λ + Hᵀ R⁻¹ H)⁻¹ = P − P Hᵀ S⁻¹ H P`. -/
theorem covariance_form (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    (precision Λ H R⁻¹)⁻¹ = Λ⁻¹ - Λ⁻¹ * Hᵀ * (R + H * Λ⁻¹ * Hᵀ)⁻¹ * H * Λ⁻¹ :=
  inv_eq_right_inv (precision_mul_covariance Λ H R hΛ hR hS)

/-- [definition] The gain `K = P Hᵀ S⁻¹`, with `P = Λ⁻¹` and `S = R + H P Hᵀ`. -/
noncomputable def gain (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K) : Matrix n m K :=
  Λ⁻¹ * Hᵀ * (R + H * Λ⁻¹ * Hᵀ)⁻¹

/-- [proved-standard] The precision after carries the gain to `Hᵀ R⁻¹`. -/
theorem precision_mul_gain (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    precision Λ H R⁻¹ * gain Λ H R = Hᵀ * R⁻¹ := by
  have hSd := (isUnit_iff_isUnit_det _).mp hS
  unfold gain
  rw [← Matrix.mul_assoc, precision_mul_covariance_transpose Λ H R hΛ hR,
    mul_nonsing_inv_cancel_right _ _ hSd]

/-- [proved-standard] **The gain in both forms**: `P Hᵀ S⁻¹ = Λ′⁻¹ Hᵀ R⁻¹`. -/
theorem gain_eq (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    gain Λ H R = (precision Λ H R⁻¹)⁻¹ * Hᵀ * R⁻¹ := by
  have hU := precision_det_isUnit Λ H R hΛ hR hS
  calc gain Λ H R = (precision Λ H R⁻¹)⁻¹ * (precision Λ H R⁻¹ * gain Λ H R) :=
        (nonsing_inv_mul_cancel_left _ _ hU).symm
    _ = (precision Λ H R⁻¹)⁻¹ * (Hᵀ * R⁻¹) := by rw [precision_mul_gain Λ H R hΛ hR hS]
    _ = (precision Λ H R⁻¹)⁻¹ * Hᵀ * R⁻¹ := (Matrix.mul_assoc _ _ _).symm

/-- [proved-standard] The covariance after is `(1 − K H) P`. -/
theorem covariance_eq_one_sub_gain (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) :
    (precision Λ H R⁻¹)⁻¹ = (1 - gain Λ H R * H) * Λ⁻¹ := by
  rw [covariance_form Λ H R hΛ hR hS, Matrix.sub_mul, Matrix.one_mul]
  rfl

/-- [proved-standard] **The mean in both forms**: `μ + K (y − H μ) = Λ′⁻¹ η′` with `η = Λ μ`. -/
theorem mean_update (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) (μ : n → K) (y : m → K) :
    μ + gain Λ H R *ᵥ (y - H *ᵥ μ) = (precision Λ H R⁻¹)⁻¹ *ᵥ information (Λ *ᵥ μ) H R⁻¹ y := by
  have hU := precision_det_isUnit Λ H R hΛ hR hS
  have h : precision Λ H R⁻¹ *ᵥ (μ + gain Λ H R *ᵥ (y - H *ᵥ μ)) = information (Λ *ᵥ μ) H R⁻¹ y := by
    rw [mulVec_add, mulVec_mulVec, precision_mul_gain Λ H R hΛ hR hS]
    unfold precision information
    rw [add_mulVec, mulVec_sub, mulVec_mulVec]
    abel
  rw [← h, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]

/-- [proved-standard] With the inverses of the covariance form, the normal equation has the one solution
`μ + K (y − H μ)`. -/
theorem stationary_iff_mean (Λ : Matrix n n K) (H : Matrix m n K) (R : Matrix m m K)
    (hΛ : IsUnit Λ) (hR : IsUnit R) (hS : IsUnit (R + H * Λ⁻¹ * Hᵀ)) (μ : n → K) (y : m → K) (x : n → K) :
    precision Λ H R⁻¹ *ᵥ x = information (Λ *ᵥ μ) H R⁻¹ y ↔ x = μ + gain Λ H R *ᵥ (y - H *ᵥ μ) := by
  have hU := precision_det_isUnit Λ H R hΛ hR hS
  rw [mean_update Λ H R hΛ hR hS]
  constructor
  · intro h
    rw [← h, mulVec_mulVec, nonsing_inv_mul _ hU, one_mulVec]
  · intro h
    rw [h, mulVec_mulVec, mul_nonsing_inv _ hU, one_mulVec]

end Covariance

/-! ## 3. The mean is the cost's stationary point -/

section Cost

variable {n m : Type*} [Fintype n] [Fintype m] {K : Type*} [Field K]

/-- [definition] The doubled cost of a state `x`: the prior's form about `μ` and the reading's form about `y`. -/
def cost (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K) (x : n → K) : K :=
  (x - μ) ⬝ᵥ Λ *ᵥ (x - μ) + (y - H *ᵥ x) ⬝ᵥ W *ᵥ (y - H *ᵥ x)

/-- [definition] The cost's slope at `x` (half its gradient for symmetric forms): `Λ′ x − η′`. -/
def slope (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K) (x : n → K) : n → K :=
  precision Λ H W *ᵥ x - information (Λ *ᵥ μ) H W y

/-- [proved-standard] The slope is the prior's pull less the reading's: `Λ (x − μ) − Hᵀ W (y − H x)`. -/
theorem slope_eq (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K) (x : n → K) :
    slope Λ μ H W y x = Λ *ᵥ (x - μ) - (Hᵀ * W) *ᵥ (y - H *ᵥ x) := by
  unfold slope precision information
  rw [add_mulVec, mulVec_sub, mulVec_sub, mulVec_mulVec]
  abel

/-- [proved-standard] **The normal equation**: the slope vanishes where `Λ′ x = η′`. -/
theorem slope_eq_zero_iff (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K)
    (x : n → K) :
    slope Λ μ H W y x = 0 ↔ precision Λ H W *ᵥ x = information (Λ *ᵥ μ) H W y :=
  sub_eq_zero

omit [Fintype m] in
private theorem sym_swap {A : Matrix n n K} (hA : Aᵀ = A) (u v : n → K) : u ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ u := by
  rw [dotProduct_comm u, ← vecMul_transpose, hA, ← dotProduct_mulVec]

private theorem mulVec_dot (B : Matrix m n K) (h : n → K) (v : m → K) : (B *ᵥ h) ⬝ᵥ v = h ⬝ᵥ Bᵀ *ᵥ v := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- [proved-standard] **The cost about any state**, for symmetric forms:
`cost (x + h) = cost x + 2 hᵀ(Λ′ x − η′) + hᵀ Λ′ h`. -/
theorem cost_add (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K)
    (hΛ : Λᵀ = Λ) (hW : Wᵀ = W) (x h : n → K) :
    cost Λ μ H W y (x + h)
      = cost Λ μ H W y x + 2 * (h ⬝ᵥ slope Λ μ H W y x) + h ⬝ᵥ precision Λ H W *ᵥ h := by
  have hx : x + h - μ = (x - μ) + h := by abel
  have hy : y - H *ᵥ (x + h) = (y - H *ᵥ x) - H *ᵥ h := by
    rw [mulVec_add]
    abel
  rw [slope_eq]
  unfold cost
  rw [hx, hy]
  generalize x - μ = a
  generalize y - H *ᵥ x = b
  have s1 : a ⬝ᵥ Λ *ᵥ h = h ⬝ᵥ Λ *ᵥ a := sym_swap hΛ a h
  have s2 : b ⬝ᵥ W *ᵥ (H *ᵥ h) = h ⬝ᵥ (Hᵀ * W) *ᵥ b := by
    rw [sym_swap hW, mulVec_dot, mulVec_mulVec]
  have s3 : (H *ᵥ h) ⬝ᵥ W *ᵥ b = h ⬝ᵥ (Hᵀ * W) *ᵥ b := by
    rw [mulVec_dot, mulVec_mulVec]
  have s4 : (H *ᵥ h) ⬝ᵥ W *ᵥ (H *ᵥ h) = h ⬝ᵥ (Hᵀ * W * H) *ᵥ h := by
    rw [mulVec_dot, mulVec_mulVec, mulVec_mulVec]
  simp only [mulVec_add, mulVec_sub, add_dotProduct, dotProduct_add, sub_dotProduct, dotProduct_sub, precision,
    add_mulVec, s1, s2, s3, s4]
  ring

/-- [proved-standard] At a solution of the normal equation the cost is `cost x + hᵀ Λ′ h`. -/
theorem cost_at_stationary (Λ : Matrix n n K) (μ : n → K) (H : Matrix m n K) (W : Matrix m m K) (y : m → K)
    (hΛ : Λᵀ = Λ) (hW : Wᵀ = W) {x : n → K}
    (hx : precision Λ H W *ᵥ x = information (Λ *ᵥ μ) H W y) (h : n → K) :
    cost Λ μ H W y (x + h) = cost Λ μ H W y x + h ⬝ᵥ precision Λ H W *ᵥ h := by
  rw [cost_add Λ μ H W y hΛ hW, (slope_eq_zero_iff Λ μ H W y x).mpr hx]
  simp

end Cost

/-! ## 5. The record's slot: one reading along a covector -/

section Slot

variable {n : Type*} {K : Type*} [Field K]

/-- [proved-standard] **The information-form slot** of the record: one reading along the covector `f` with precision
`w` deposits `w f fᵀ`. -/
theorem rank_one_slot (Λ : Matrix n n K) (f : n → K) (w : K) :
    precision Λ (replicateRow Unit f) (w • (1 : Matrix Unit Unit K)) = Λ + w • vecMulVec f f := by
  unfold precision
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply]

/-- [proved-standard] The same reading `y` adds `w y f` to the information vector. -/
theorem rank_one_information (η : n → K) (f : n → K) (w y : K) :
    information η (replicateRow Unit f) (w • (1 : Matrix Unit Unit K)) (fun _ => y) = η + (w * y) • f := by
  unfold information
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm, mul_left_comm]

end Slot

/-! ## 4. Precision never falls -/

section Real

variable {n m : Type*} [Fintype n] [Fintype m]

/-- [proved-standard] **Precision never falls**: the deposit `Λ′ − Λ = Hᵀ W H` is positive semidefinite when the
noise precision is. -/
theorem precision_gain_posSemidef (Λ : Matrix n n ℝ) (H : Matrix m n ℝ) {W : Matrix m m ℝ} (hW : W.PosSemidef) :
    (precision Λ H W - Λ).PosSemidef := by
  have h := hW.conjTranspose_mul_mul_same H
  rw [conjTranspose_eq_transpose_of_trivial] at h
  unfold precision
  rwa [add_sub_cancel_left]

/-- [proved-standard] The precision after is positive semidefinite when the prior's and the noise's are. -/
theorem precision_posSemidef {Λ : Matrix n n ℝ} (hΛ : Λ.PosSemidef) (H : Matrix m n ℝ) {W : Matrix m m ℝ}
    (hW : W.PosSemidef) : (precision Λ H W).PosSemidef := by
  have h := hW.conjTranspose_mul_mul_same H
  rw [conjTranspose_eq_transpose_of_trivial] at h
  exact hΛ.add h

/-- [proved-standard] **The stationary point is a least one**: over the reals, with symmetric forms and `Λ′`
positive semidefinite, a solution of the normal equation costs no more than any other state. -/
theorem stationary_is_least (Λ : Matrix n n ℝ) (μ : n → ℝ) (H : Matrix m n ℝ) (W : Matrix m m ℝ) (y : m → ℝ)
    (hΛ : Λᵀ = Λ) (hW : Wᵀ = W) (hpos : (precision Λ H W).PosSemidef) {x : n → ℝ}
    (hx : precision Λ H W *ᵥ x = information (Λ *ᵥ μ) H W y) (z : n → ℝ) :
    cost Λ μ H W y x ≤ cost Λ μ H W y z := by
  have h := cost_at_stationary Λ μ H W y hΛ hW hx (z - x)
  rw [add_sub_cancel] at h
  have hnn := hpos.dotProduct_mulVec_nonneg (z - x)
  rw [star_trivial] at hnn
  linarith

end Real

/-! ## 6. The scalar ruler of the record's §14.6 -/

section Scalar

variable {K : Type*} [Field K]

/-- [proved-derived] **The scalar gain**: the information form `(m/P + y/R)/(1/P + 1/R)` is `m + K (y − m)` at
`K = P/(P + R)`. -/
theorem scalar_gain (m y P R : K) (hP : P ≠ 0) (hR : R ≠ 0) (hPR : P + R ≠ 0) :
    (m / P + y / R) / (1 / P + 1 / R) = m + P / (P + R) * (y - m) := by
  have h : 1 / P + 1 / R = (P + R) / (P * R) := by
    field_simp
    ring
  rw [h]
  field_simp
  ring

/-- [proved-derived] The precision after is the sum of the two precisions: `1/((1 − K) P) = 1/P + 1/R`. -/
theorem scalar_precision_adds (P R : K) (hP : P ≠ 0) (hR : R ≠ 0) (hPR : P + R ≠ 0) :
    1 / ((1 - P / (P + R)) * P) = 1 / P + 1 / R := by
  have h : (1 - P / (P + R)) * P = P * R / (P + R) := by
    field_simp
    ring
  rw [h]
  field_simp
  ring

/-- [proved-derived] **The cost is a square about the updated mean**, plus what no state removes:
`(x − m)²/P + (y − x)²/R = (1/P + 1/R)(x − x⁺)² + (y − m)²/(P + R)`. -/
theorem scalar_square (x m y P R : K) (hP : P ≠ 0) (hR : R ≠ 0) (hPR : P + R ≠ 0) :
    (x - m) ^ 2 / P + (y - x) ^ 2 / R
      = (1 / P + 1 / R) * (x - (m + P / (P + R) * (y - m))) ^ 2 + (y - m) ^ 2 / (P + R) := by
  field_simp
  ring

/-- [proved-derived] Over an ordered field with positive variances the cost is least at `m + K (y − m)`. -/
theorem scalar_least [LinearOrder K] [IsStrictOrderedRing K] (x m y P R : K) (hP : 0 < P) (hR : 0 < R) :
    (m + P / (P + R) * (y - m) - m) ^ 2 / P + (y - (m + P / (P + R) * (y - m))) ^ 2 / R
      ≤ (x - m) ^ 2 / P + (y - x) ^ 2 / R := by
  have hPR : P + R ≠ 0 := (add_pos hP hR).ne'
  rw [scalar_square x m y P R hP.ne' hR.ne' hPR,
    scalar_square (m + P / (P + R) * (y - m)) m y P R hP.ne' hR.ne' hPR, sub_self]
  have h1 : 0 ≤ (1 / P + 1 / R) * (x - (m + P / (P + R) * (y - m))) ^ 2 :=
    mul_nonneg (add_pos (one_div_pos.mpr hP) (one_div_pos.mpr hR)).le (sq_nonneg _)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add]
  linarith

end Scalar

end Holonics.Foundation.InformationUpdate

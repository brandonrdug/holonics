import Mathlib

/-!
# The comparison's symmetries, and where the Gauss–Newton step points

[proved-derived; formal-checked] for the theorems (the record
`research/records/2026-10-02_THE_COMPARISON_IS_INVARIANT_UNDER_THE_RINGS_SHIFTS_AND_A_GLOBAL_PHASE_AND_THE_GAUSS_NEWTON_STEP_POINTS_TOWARD_A_LOWER_POINT_EXACTLY_WHEN_ITS_CHORD_DESCENDS.md`).

The executed comparison reads `E` only through the receiving bank's growths, and each growth only
through its monodromy's characteristic polynomial. The bank is one realified node whose tick adds
the pump's reflection block `−2p R_c` to its stiffness, `c` the placed carrier.

1. **The pump block's symmetries** (`reflection`, `rotor`, `rotor_mul_reflection`,
   `rotor_conj_reflection`, `flip_conj_reflection`): a rotor `Q = pI + qJ` carries `R_c` to
   `R_((p + iq)² c)`, and the flip `S = diag(1, −1)` carries it to `R_c̄`. Everything else in a tick
   is a multiple of the identity.
2. **The monodromy's characteristic polynomial** (`conj_list_prod`, `charpoly_conj_ticks`,
   `charpoly_rotate_ticks`): conjugating every tick by one invertible matrix, or starting the turn
   at another tick, leaves it unchanged.
3. **The orbit's tangent is unread** (`fderiv_orbit_tangent`, `mass_orthogonal_unread`): a
   comparison constant along a curve has no derivative along its tangent, and the minimum-mass
   step is mass-orthogonal to every direction the readings do not read.
4. **The Gauss–Newton step's pairing** (`gaussNewton_pairing`): in the form `AᵀFA`, the step pairs
   with any chord as minus the comparison's derivative along it.
5. **A convex chord descends at first order** (`convex_chord_slope_le`,
   `nonconvex_of_uphill_lower`): if the comparison falls along a chord whose slope at the start is
   not negative, the chord is not convex.
6. **The distance to a phase orbit** (`dist_phase_orbit_sq_ge`, `dist_phase_orbit_sq_eq`): over
   unit phases, `‖x − w y‖²` is least at `‖x‖² + ‖y‖² − 2‖⟪y, x⟫‖`.
7. **The leap and the throw** (`pairing_nonpos_of_steps`, `comparison_le_energy`, `leap_confined`,
   `throw`, `throw_solves`, `throw_between`): a velocity summed from steps that each point away
   points away; along a path whose energy does not rise the comparison never exceeds the opening
   energy, so a move from rest never crosses a pass above its start; in one quadratic mode the throw
   from rest moves only toward and past its equilibrium, at most twice as far.
8. **Why the receiver's step turns from the gradient** (`fisher_step_target_only`,
   `throw_le_free_fall`, `carried_velocity`): one lock's Gauss–Newton change raises only its target,
   by `1/θ_t`; a throw's flight caps every mode at the force's free fall `|g|t²/2`, whatever its
   stiffness; a carried velocity accumulates a push that keeps its sign.
9. **The throw through the accreted mass** (`accretion_loss`, `accretion_dissipates`,
   `thrown_move`, `throw_velocity_le_terminal`, `throw_velocity_rises`, `leap_velocity_le`,
   `throw_velocity_le_unaccreted`, `throw_reach_le_free_fall`): a
   deposit accretes mass onto the port and conserves the carried momentum, so its kinetic reading
   falls by exactly `p² f/(2m(m + f))`; the thrown move is the impulse plus the coast, the leap's
   impulse alone from rest; under a constant impulse the throw's velocity rises toward the impulse
   over the per-deposit mass while the leap's falls like `1/k`; and a throw from rest reaches no
   further than free fall `(i/m₀)·n(n + 1)/2` (the record
   `research/records/2026-10-02_THE_THROW_CARRIES_ITS_MOMENTUM_THROUGH_THE_DEPOSITS_ACCRETED_MASS_AND_A_HALVING_HALVES_IT.md`).
-/

namespace Holonics.HNN.MoveDirection

open Matrix

/-! ## 1. The pump block -/

/-- The reflection block `R_c = [[Re c, Im c], [Im c, −Re c]]`: `z ↦ c z̄` on the realified node. -/
def reflection (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, -a]

/-- The rotor `pI + qJ`: multiplication by `p + iq` on the realified node. -/
def rotor (p q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![p, -q; q, p]

/-- The flip `diag(1, −1)`: complex conjugation on the realified node. -/
def flip : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `(α + iβ) · (c z̄) = ((α + iβ)c) z̄`: a rotor applied after the reflection is the reflection of
the multiplied carrier. -/
theorem rotor_mul_reflection (α β a b : ℝ) :
    rotor α β * reflection a b = reflection (α * a - β * b) (β * a + α * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotor, reflection, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

/-- **The rotor carries the reflection to the doubled phase**: `Q R_c Qᵀ = R_((p + iq)² c)`, for
every `p, q`. With `p² + q² = 1`, `Qᵀ = Q⁻¹`, so the pump block at the carrier `e^(iφ)c` is the
block at `c` conjugated by the rotor of `e^(iφ/2)`. -/
theorem rotor_conj_reflection (p q a b : ℝ) :
    rotor p q * reflection a b * (rotor p q)ᵀ =
      reflection ((p ^ 2 - q ^ 2) * a - 2 * p * q * b) (2 * p * q * a + (p ^ 2 - q ^ 2) * b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotor, reflection, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring

/-- **The flip carries the reflection to the conjugate carrier**: `S R_c S = R_c̄`. -/
theorem flip_conj_reflection (a b : ℝ) : flip * reflection a b * flip = reflection a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flip, reflection, Matrix.mul_apply, Fin.sum_univ_two]

/-- The rotor of a unit `p + iq` is orthogonal. -/
theorem rotor_mul_transpose {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) : rotor p q * (rotor p q)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> nlinarith [h]

/-! ## 2. The monodromy's characteristic polynomial -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Conjugating every tick by one unit conjugates their product. -/
theorem conj_list_prod (U : (Matrix n n ℝ)ˣ) (Ts : List (Matrix n n ℝ)) :
    (Ts.map fun T => (U : Matrix n n ℝ) * T * (U⁻¹ : (Matrix n n ℝ)ˣ)).prod =
      (U : Matrix n n ℝ) * Ts.prod * (U⁻¹ : (Matrix n n ℝ)ˣ) := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    rw [List.map_cons, List.prod_cons, ih, List.prod_cons]
    have h : ((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * (U : Matrix n n ℝ) = 1 := by simp
    calc (U : Matrix n n ℝ) * T * (U⁻¹ : (Matrix n n ℝ)ˣ) *
          ((U : Matrix n n ℝ) * Ts.prod * (U⁻¹ : (Matrix n n ℝ)ˣ))
        = (U : Matrix n n ℝ) * T * (((U⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
            (U : Matrix n n ℝ)) * Ts.prod * (U⁻¹ : (Matrix n n ℝ)ˣ) := by
          simp only [Matrix.mul_assoc]
      _ = (U : Matrix n n ℝ) * (T * Ts.prod) * (U⁻¹ : (Matrix n n ℝ)ˣ) := by
          rw [h, Matrix.mul_one, Matrix.mul_assoc (U : Matrix n n ℝ)]

/-- **A global conjugation of the turn leaves its characteristic polynomial**: if every tick map is
conjugated by the same unit (the rotor of a global phase, the flip of a conjugation), the turn's
monodromy has the same characteristic polynomial, hence the same growth. -/
theorem charpoly_conj_ticks (U : (Matrix n n ℝ)ˣ) (Ts : List (Matrix n n ℝ)) :
    (Ts.map fun T => (U : Matrix n n ℝ) * T * (U⁻¹ : (Matrix n n ℝ)ˣ)).prod.charpoly =
      Ts.prod.charpoly := by
  rw [conj_list_prod, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj U Ts.prod

/-- **Starting the turn at another tick leaves its characteristic polynomial**: the monodromy read
from tick `k` is a cyclic rotation of the product, `BA` for `AB`. -/
theorem charpoly_rotate_ticks (Ts : List (Matrix n n ℝ)) (k : ℕ) :
    (Ts.rotate k).prod.charpoly = Ts.prod.charpoly := by
  rw [List.rotate_eq_drop_append_take_mod, List.prod_append]
  conv_rhs => rw [← List.take_append_drop (k % Ts.length) Ts, List.prod_append]
  exact Matrix.charpoly_mul_comm _ _

/-! ## 3. The orbit's tangent is unread -/

/-- **A comparison constant along a curve has no derivative along its tangent**: if `f ∘ γ` is
constant near `0` and `γ' 0 = w`, then `f'(γ 0) w = 0`. With `γ θ = e^(Jθ) E`, the curve of
global phases, `w = JE`: the comparison's gradient is orthogonal to the orbit. -/
theorem fderiv_orbit_tangent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → ℝ} {f' : V →L[ℝ] ℝ} {γ : ℝ → V} {w : V}
    (hf : HasFDerivAt f f' (γ 0)) (hγ : HasDerivAt γ w 0)
    (hconst : ∀ᶠ θ in nhds (0 : ℝ), f (γ θ) = f (γ 0)) : f' w = 0 := by
  have hcomp : HasDerivAt (f ∘ γ) (f' w) 0 := hf.comp_hasDerivAt 0 hγ
  have hc : HasDerivAt (fun _ : ℝ => f (γ 0)) 0 0 := hasDerivAt_const 0 (f (γ 0))
  have heq : (f ∘ γ) =ᶠ[nhds 0] fun _ => f (γ 0) := hconst
  exact (hcomp.congr_of_eventuallyEq heq.symm).unique hc

/-- **The minimum-mass step is mass-orthogonal to every unread direction**: a step `v` with
`Mv = Aᵀμ` (the kinetic solve's iterates, `v = M⁻¹Aᵀμ`) pairs with `w` in the mass as `μ` pairs with
`Aw`, so it is mass-orthogonal to every `w` the readings do not read (`Aw = 0`), among them the
orbit's tangent `JE`. -/
theorem mass_orthogonal_unread {m r : Type*} [Fintype m] [Fintype r]
    (M : Matrix m m ℝ) (A : Matrix r m ℝ) (μ : r → ℝ) (v w : m → ℝ)
    (hv : M *ᵥ v = Aᵀ *ᵥ μ) (hw : A *ᵥ w = 0) : (M *ᵥ v) ⬝ᵥ w = 0 := by
  rw [hv, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, hw, dotProduct_zero]

/-! ## 4. The Gauss–Newton step's pairing -/

/-- **The step pairs with a chord as minus the comparison's derivative along it**: if `v` solves
the Gauss–Newton normal equation `AᵀFAv = −Aᵀc` (`A` the readings' Jacobian, `F` the receiver's
Fisher form, `c` its covector, `g = Aᵀc` the comparison's gradient), then for every chord `u`,
`⟨Au, F Av⟩ = −⟨g, u⟩`. In the form `AᵀFA` the step's cosine with `u` has the sign of the
comparison's descent along `u`, whatever the mass that selected `v`. -/
theorem gaussNewton_pairing {m r : Type*} [Fintype m] [Fintype r]
    (A : Matrix r m ℝ) (F : Matrix r r ℝ) (c : r → ℝ) (u v : m → ℝ)
    (hv : (Aᵀ * F * A) *ᵥ v = -(Aᵀ *ᵥ c)) :
    (A *ᵥ u) ⬝ᵥ (F *ᵥ (A *ᵥ v)) = -((Aᵀ *ᵥ c) ⬝ᵥ u) := by
  have h1 : (A *ᵥ u) ⬝ᵥ (F *ᵥ (A *ᵥ v)) = u ⬝ᵥ ((Aᵀ * F * A) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Aᵀ,
      Matrix.vecMul_transpose]
  rw [h1, hv, dotProduct_neg, dotProduct_comm]

/-! ## 5. A convex chord descends at first order -/

/-- **A convex chord's slope at its start is at most its fall**: if `f` is convex on `[0, 1]` with
right derivative `d` at `0`, then `d ≤ f 1 − f 0`. -/
theorem convex_chord_slope_le {f : ℝ → ℝ} {d : ℝ} (hf : ConvexOn ℝ (Set.Icc 0 1) f)
    (hd : HasDerivWithinAt f d (Set.Ioi 0) 0) : d ≤ f 1 - f 0 := by
  have hlim := hasDerivWithinAt_iff_tendsto_slope.mp hd
  rw [Set.sdiff_singleton_eq_self (by simp)] at hlim
  apply le_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
  obtain ⟨ht0, ht1⟩ := ht
  have hconv := hf.2 (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)
    (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hconv
  rw [slope_def_field, sub_zero, div_le_iff₀ ht0]
  nlinarith

/-- **A lower point uphill at first order lies across a nonconvex chord**: if the comparison is
lower at the chord's end (`f 1 < f 0`) but its slope at the start is not negative, the chord is
not convex. With `f τ = L(E + τu)`, `d = ⟨g, u⟩`: the Gauss–Newton step points away from such a
point in its own form (`gaussNewton_pairing`), and so does every descent step in its own metric. -/
theorem nonconvex_of_uphill_lower {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivWithinAt f d (Set.Ioi 0) 0) (hup : 0 ≤ d) (hlow : f 1 < f 0) :
    ¬ ConvexOn ℝ (Set.Icc 0 1) f := fun hf => by
  have := convex_chord_slope_le hf hd
  linarith

/-! ## 6. The distance to a phase orbit -/

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- **No unit phase brings `y` closer to `x` than `‖x‖² + ‖y‖² − 2‖⟪y, x⟫‖`**. -/
theorem dist_phase_orbit_sq_ge (x y : W) {w : ℂ} (hw : ‖w‖ = 1) :
    ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖inner ℂ y x‖ ≤ ‖x - w • y‖ ^ 2 := by
  rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, hw, one_mul]
  have h1 : RCLike.re (w * inner ℂ x y) ≤ ‖inner ℂ y x‖ := by
    calc RCLike.re (w * inner ℂ x y) ≤ ‖w * inner ℂ x y‖ := RCLike.re_le_norm _
      _ = ‖inner ℂ y x‖ := by rw [norm_mul, hw, one_mul, norm_inner_symm]
  linarith

/-- **Some unit phase attains it**. -/
theorem dist_phase_orbit_sq_eq (x y : W) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ‖x - w • y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 - 2 * ‖inner ℂ y x‖ := by
  by_cases h0 : inner ℂ y x = 0
  · refine ⟨1, by simp, ?_⟩
    have hxy : inner ℂ x y = 0 := by rw [← inner_conj_symm, h0, map_zero]
    rw [@norm_sub_sq ℂ, one_smul, hxy, h0]
    simp
  · have hn : (‖inner ℂ y x‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h0
    refine ⟨inner ℂ y x / ‖inner ℂ y x‖, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr h0)]
    · rw [@norm_sub_sq ℂ, inner_smul_right, norm_smul, norm_div, Complex.norm_real, norm_norm,
        div_self (norm_ne_zero_iff.mpr h0), one_mul]
      have hc : inner ℂ y x / (‖inner ℂ y x‖ : ℂ) * inner ℂ x y = (‖inner ℂ y x‖ : ℂ) := by
        rw [← inner_conj_symm x y, div_mul_eq_mul_div, Complex.mul_conj', div_eq_iff hn]
        ring
      have hr : RCLike.re ((‖inner ℂ y x‖ : ℂ)) = ‖inner ℂ y x‖ := by simp
      rw [hc, hr]
      ring

/-! ## 7. The leap and the throw -/

/-- **A positive sum of steps that each point away points away**: if every step `v_j` pairs
nonpositively with the chord `u` and the weights are nonnegative, so does `Σ a_j v_j`. A carried
velocity built from the same steps at the same states is such a sum. -/
theorem pairing_nonpos_of_steps {m ι : Type*} [Fintype m] (s : Finset ι) (a : ι → ℝ)
    (v : ι → m → ℝ) (u : m → ℝ) (ha : ∀ j ∈ s, 0 ≤ a j) (hv : ∀ j ∈ s, v j ⬝ᵥ u ≤ 0) :
    (∑ j ∈ s, a j • v j) ⬝ᵥ u ≤ 0 := by
  rw [sum_dotProduct]
  exact Finset.sum_nonpos fun j hj => by
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (ha j hj) (hv j hj)

/-- **Energy bounds the reachable comparison**: along any path whose energy `K + L` (kinetic `K ≥ 0`
plus the comparison `L`) does not rise, the comparison never exceeds the opening energy. A pass of
height `p` is crossed only if `p ≤ K 0 + L 0`. -/
theorem comparison_le_energy {K L : ℕ → ℝ} (hK : ∀ k, 0 ≤ K k)
    (hH : Antitone fun k => K k + L k) (k : ℕ) : L k ≤ K 0 + L 0 := by
  have := hH (Nat.zero_le k)
  linarith [hK k]

/-- **From rest, the leap never crosses a pass above its start**: with no carried energy (`K 0 = 0`)
the comparison stays at or below its opening value along the whole path. -/
theorem leap_confined {K L : ℕ → ℝ} (hK : ∀ k, 0 ≤ K k) (h0 : K 0 = 0)
    (hH : Antitone fun k => K k + L k) (k : ℕ) : L k ≤ L 0 := by
  have := comparison_le_energy hK hH k
  linarith

/-- The undamped throw from rest toward an equilibrium `x*` in one mode of frequency `ω`. -/
noncomputable def throw (xs ω t : ℝ) : ℝ := xs * (1 - Real.cos (ω * t))

/-- **The throw solves the mode's equation from rest**: `x'' = ω²(x* − x)`, `x(0) = 0`,
`x'(0) = 0`. -/
theorem throw_solves (xs ω t : ℝ) :
    HasDerivAt (fun t => xs * ω * Real.sin (ω * t)) (ω ^ 2 * (xs - throw xs ω t)) t ∧
      HasDerivAt (throw xs ω) (xs * ω * Real.sin (ω * t)) t ∧ throw xs ω 0 = 0 := by
  refine ⟨?_, ?_, by simp [throw]⟩
  · have h := ((hasDerivAt_id t).const_mul ω).sin.const_mul (xs * ω)
    exact h.congr_deriv (by unfold throw; simp only [id, mul_one]; ring)
  · have h := (((hasDerivAt_id t).const_mul ω).cos.const_sub 1).const_mul xs
    exact h.congr_deriv (by simp only [id, mul_one]; ring)

/-- **The throw moves each mode only toward and past its equilibrium, at most twice as far**:
`x(t)` lies between `0` and `2x*`. Within one quadratic model the throw reaches no direction the
leap does not. -/
theorem throw_between (xs ω t : ℝ) :
    0 ≤ xs * throw xs ω t ∧ xs * throw xs ω t ≤ 2 * xs ^ 2 := by
  have h1 := Real.cos_le_one (ω * t)
  have h2 := Real.neg_one_le_cos (ω * t)
  unfold throw
  constructor <;> nlinarith [sq_nonneg xs]

/-! ## 8. Why the receiver's step turns from the gradient -/

/-- **The Gauss–Newton change of one lock's readings raises only the target, by the inverse of its
share**: with the Fisher form `F = diag θ − θθᵀ` on the non-resting sheets and the covector
`c = θ − e_t`, the readings' change `w = e_t/θ_t` solves `Fw = −c`. The gradient weighs the same
target by `1 − θ_t`, so the step reweighs each station by about `1/θ_t` against the gradient: the
worst-read targets dominate it. -/
theorem fisher_step_target_only {k : Type*} [Fintype k] [DecidableEq k] (θ : k → ℝ) (t : k)
    (ht : θ t ≠ 0) :
    (Matrix.diagonal θ - Matrix.vecMulVec θ θ) *ᵥ Pi.single t (1 / θ t) =
      -(θ - Pi.single t 1) := by
  ext i
  have hv : ∀ j, Matrix.vecMulVec θ θ i j = θ i * θ j := fun j => rfl
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.sub_apply, Matrix.diagonal_apply, hv,
    Pi.neg_apply, Pi.sub_apply]
  by_cases hi : i = t
  · subst hi; simp only [if_true]; field_simp; ring
  · simp only [hi, if_false]; field_simp; ring

/-- **A throw's flight caps every mode at the force's free fall**: in a mode of stiffness `ω²`
pushed by a force `g`, the throw from rest toward `x* = g/ω²` has moved at most `|g| t²/2` by time
`t`, whatever `ω`. The leap moves the same mode by `|g|/ω²`, without bound as the mode softens. -/
theorem throw_le_free_fall (g ω t : ℝ) (hω : ω ≠ 0) : |throw (g / ω ^ 2) ω t| ≤ |g| * t ^ 2 / 2 := by
  unfold throw
  have h1 : 1 - Real.cos (ω * t) ≤ (ω * t) ^ 2 / 2 := by
    have := Real.one_sub_sq_div_two_le_cos (x := ω * t)
    linarith
  have h0 : 0 ≤ 1 - Real.cos (ω * t) := by linarith [Real.cos_le_one (ω * t)]
  rw [abs_mul, abs_of_nonneg h0, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ω ^ 2)]
  calc |g| / ω ^ 2 * (1 - Real.cos (ω * t)) ≤ |g| / ω ^ 2 * ((ω * t) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = |g| * t ^ 2 / 2 := by field_simp

/-- **A carried velocity accumulates a persistent push**: with `v (k+1) = β v k + a` from rest,
`v k = a (1 − β^k)/(1 − β)`, so a push that keeps its sign builds toward `a/(1 − β)` while one that
alternates averages out. -/
theorem carried_velocity {β a : ℝ} (hβ : β ≠ 1) (v : ℕ → ℝ) (h0 : v 0 = 0)
    (hv : ∀ k, v (k + 1) = β * v k + a) (k : ℕ) : v k = a * (1 - β ^ k) / (1 - β) := by
  have hne : (1 - β) ≠ 0 := sub_ne_zero.mpr (Ne.symm hβ)
  induction k with
  | zero => simp [h0]
  | succ k ih => rw [hv, ih, pow_succ]; field_simp; ring

/-! ## 9. The throw through the accreted mass -/

/-- **Accretion dissipates a carried momentum, by exactly its sticking loss**: a momentum `p`
carried across a deposit that accretes `f ≥ 0` onto the mass `m > 0` is kept, and its kinetic
reading `p²/(2m)` falls to `p²/(2(m + f))`, by `p² f/(2m(m + f))`. -/
theorem accretion_loss (p m f : ℝ) (hm : 0 < m) (hf : 0 ≤ f) :
    p ^ 2 / (2 * m) - p ^ 2 / (2 * (m + f)) = p ^ 2 * f / (2 * m * (m + f)) := by
  have h : 0 < m + f := by linarith
  field_simp
  ring

/-- **The accreted mass is the throw's damping**: the kinetic reading never rises across a
deposit's accretion. -/
theorem accretion_dissipates (p m f : ℝ) (hm : 0 < m) (hf : 0 ≤ f) :
    p ^ 2 / (2 * (m + f)) ≤ p ^ 2 / (2 * m) := by
  have h := accretion_loss p m f hm hf
  have h' : 0 ≤ p ^ 2 * f / (2 * m * (m + f)) := by
    have : 0 < m + f := by linarith
    positivity
  linarith

/-- **The thrown move is the impulse plus the coast**: the carried momentum `p` and the deposit's
impulse `i` move the port by `(p + i)/(m + f)`, the impulse's move `i/(m + f)` (the leap's) plus
the coast `p/(m + f)`; from rest (`p = 0`) it is the leap. -/
theorem thrown_move (p i m f : ℝ) :
    (p + i) / (m + f) = i / (m + f) + p / (m + f) ∧ (0 + i) / (m + f) = i / (m + f) := by
  constructor
  · ring
  · rw [zero_add]

/-- **Under a constant impulse the throw's velocity stays below the impulse over the per-deposit
mass**: after `k` deposits of mass `f > 0` onto `m₀ > 0`, each with impulse `i ≥ 0`, the carried
momentum `k i` moves the port by `k i/(m₀ + k f) ≤ i/f`. -/
theorem throw_velocity_le_terminal (i m₀ f : ℝ) (k : ℕ) (hi : 0 ≤ i) (hm : 0 < m₀) (hf : 0 < f) :
    k * i / (m₀ + k * f) ≤ i / f := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_le_div_iff₀ (by positivity) hf]
  nlinarith [mul_nonneg hi hm.le]

/-- **The throw's velocity rises with every deposit under a constant impulse**. -/
theorem throw_velocity_rises (i m₀ f : ℝ) (k : ℕ) (hi : 0 ≤ i) (hm : 0 < m₀) (hf : 0 < f) :
    k * i / (m₀ + k * f) ≤ (k + 1) * i / (m₀ + (k + 1) * f) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hi hm.le]

/-- **The leap's velocity falls like `1/k`**: the leap spends its momentum at every deposit, so
after `k ≥ 1` deposits its move is `i/(m₀ + k f) ≤ i/(k f)`. -/
theorem leap_velocity_le (i m₀ f : ℝ) (k : ℕ) (hk : 1 ≤ k) (hi : 0 ≤ i) (hm : 0 < m₀)
    (hf : 0 < f) : i / (m₀ + k * f) ≤ i / (k * f) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  apply div_le_div_of_nonneg_left hi (by positivity)
  linarith

/-- **Accretion never speeds the throw past its unaccreted mass**: after `k` deposits of mass
`f ≥ 0` onto `m₀ > 0`, each with impulse `i ≥ 0`, the carried momentum `k i` moves the port by
`k i/(m₀ + k f) ≤ k i/m₀`, the velocity of free fall under `g = i/m₀`. -/
theorem throw_velocity_le_unaccreted (i m₀ f : ℝ) (k : ℕ) (hi : 0 ≤ i) (hm : 0 < m₀)
    (hf : 0 ≤ f) : k * i / (m₀ + k * f) ≤ k * i / m₀ := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  apply div_le_div_of_nonneg_left (mul_nonneg hk hi) hm
  nlinarith

/-- **A throw from rest reaches no further than free fall**: under a constant impulse `i ≥ 0` on
`m₀ > 0` with per-deposit mass `f ≥ 0`, the port's displacement over moves `0, …, n` is at most
`(i/m₀)·n(n + 1)/2`, the discrete `|g| t²/2` with `g = i/m₀`. At `f = 0` it is free fall's own
reach; a positive `f` only damps it. -/
theorem throw_reach_le_free_fall (i m₀ f : ℝ) (hi : 0 ≤ i) (hm : 0 < m₀) (hf : 0 ≤ f) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) * i / (m₀ + k * f) ≤ i / m₀ * (n * (n + 1) / 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h := throw_velocity_le_unaccreted i m₀ f (n + 1) hi hm hf
    push_cast at h ⊢
    have e : i / m₀ * (((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / 2)
        = i / m₀ * ((n : ℝ) * ((n : ℝ) + 1) / 2) + ((n : ℝ) + 1) * i / m₀ := by
      field_simp
      ring
    linarith

end Holonics.HNN.MoveDirection

import Mathlib

/-!
# A dissipative field has one global flow: every truncated fluid runs for all time

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§7; this
module's companion to `Fluid/NavierStokesGalerkinInstance`, whose truncation takes a solution as a
hypothesis). It imports Mathlib alone.

[definition] A field `F : E → E` on a real inner product space is **dissipative** when it does no
positive work against the state, `⟪x, F x⟫ ≤ 0` for every `x` (`Dissipative`), and it is
**Lipschitz on balls** when on every closed ball about the origin it is Lipschitz with some constant
(`LipschitzOnBalls`). The truncated fluid is both: its damping is a linear map with
`⟪x, A x⟫ ≤ 0`, and its feed is a bilinear map that does no work, `⟪x, B x x⟫ = 0`.

[proved-derived; formal-checked] The energy reading, on any convex set of times:

* `norm_antitoneOn`: a solution of a dissipative field has a norm that never rises;
* `norm_le_exp_mul_of_damped`: if `⟪x, F x⟫ ≤ -ν * ‖x‖ ^ 2` then `‖x t‖ ≤ exp (-ν t) * ‖x 0‖`.

[proved-derived; formal-checked] Existence and uniqueness for every time, in a complete space:

* `exists_step`: from a point of the ball of radius `ρ`, a solution for a time `stepTime F K ρ`
  that depends on the ball and not on the point (Picard–Lindelöf on the ball of radius one about
  the point);
* `exists_on_Icc`: a solution on `[0, n * stepTime F K ρ]` for every `n`, by steps whose starts
  never leave the ball, because the norm never rises;
* `eqOn_Icc`, `eqOn_Ici`: two solutions from one state agree on every `[0, T]` and on `[0, ∞)`;
* `exists_global`: a solution on `[0, ∞)` from every state, with `‖x t‖ ≤ ‖x 0‖`;
* `existsUnique_global`: it is the only one on `[0, ∞)`.

[proved-derived; formal-checked] The truncated fluid's shape. A linear map `A` and a bilinear
map `B` give a field `x ↦ A x + B x x` that is Lipschitz on balls (`lipschitzOnBalls_linear_add_bilinear`,
constant `‖A‖ + 2‖B‖R` on the ball of radius `R`), and that is dissipative when `⟪x, A x⟫ ≤ 0` and
`⟪x, B x x⟫ = 0` (`dissipative_linear_add_bilinear`). So such a law has one flow for all time from
every state (`exists_global_quadratic`, `existsUnique_global_quadratic`), and with a damping rate,
`⟪x, A x⟫ ≤ -ν‖x‖²`, the flow decays at `exp (-ν t)` (`norm_le_exp_quadratic`).

## What this does not state

The energy conservation of the fluid's own triads (that the Leray truncation's feed is a `B` with
`⟪x, B x x⟫ = 0` on real, divergence-free data) is a separate statement, proved in
`Fluid/NavierStokesTriadConservation`; here it enters as the hypothesis `⟪x, B x x⟫ = 0`, and
`Fluid/NavierStokesTruncatedGlobal` joins the two. Nothing here is a statement about the fluid's equation
with infinitely many modes, about a limit of truncations, or about a bound that is uniform in the
truncation beyond the energy: the step time depends on the field's Lipschitz constant on a ball,
which grows with the number of modes. The flow is forward in time only.

## The computational object

The helical pair interaction, read in its tube (a clocked span): the flow is the tube's clock run
without end, and the energy is the one reading the tube's interior keeps below its opening. The
other five objects (helix, pair, faces and placement, cell holonomy, tower thread) stay attached
through the consumers.

Consumers: `Fluid/NavierStokesTruncatedGlobal` (the truncated fluid of
`Fluid/NavierStokesGalerkinInstance`, whose `Truncation` and `Evolves` take a solution as given),
the atlas row `ns.dissipative-global-flow`, and any region whose law is dissipative.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Set Metric Filter Topology
open scoped NNReal RealInnerProductSpace

namespace Holonics.Fluid.DissipativeGlobalFlow

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## D1. Definitions -/

/-- [definition] A field that does no positive work against the state. -/
def Dissipative (F : E → E) : Prop := ∀ x, ⟪x, F x⟫ ≤ 0

/-- [definition] A field that is Lipschitz, with some constant, on every closed ball about the
origin. -/
def LipschitzOnBalls (F : E → E) : Prop :=
  ∀ R : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K F (closedBall (0 : E) R)

/-! ## D2. The energy reading -/

/-- [proved-derived; formal-checked] The derivative of the energy `⟪x, x⟫` along a solution. -/
theorem hasDerivWithinAt_energy {F : E → E} {D : Set ℝ} {x : ℝ → E} {t : ℝ}
    (hx : HasDerivWithinAt x (F (x t)) D t) :
    HasDerivWithinAt (fun s => ⟪x s, x s⟫) (2 * ⟪x t, F (x t)⟫) D t := by
  have h := HasDerivWithinAt.inner ℝ hx hx
  rw [real_inner_comm (x t) (F (x t))] at h
  exact h.congr_deriv (by ring)

/-- [proved-derived; formal-checked] A solution of a dissipative field, on any convex set of
times, has a norm that never rises. -/
theorem norm_antitoneOn {F : E → E} (hF : Dissipative F) {D : Set ℝ} (hD : Convex ℝ D)
    {x : ℝ → E} (hx : ∀ t ∈ D, HasDerivWithinAt x (F (x t)) D t) :
    AntitoneOn (fun t => ‖x t‖) D := by
  have he : AntitoneOn (fun s => ⟪x s, x s⟫) D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos hD
      (fun t ht => (hasDerivWithinAt_energy (hx t ht)).continuousWithinAt)
      (fun t ht => (hasDerivWithinAt_energy (hx t (interior_subset ht))).mono interior_subset)
      (fun t _ => ?_)
    have := hF (x t)
    linarith
  intro s hs t ht hst
  have h := he hs ht hst
  simp only [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (x s), norm_nonneg (x t)]

/-- [proved-derived; formal-checked] With a damping rate, `⟪x, F x⟫ ≤ -ν * ‖x‖ ^ 2`, a solution
on `[0, ∞)` decays at `exp (-ν t)`. -/
theorem norm_le_exp_mul_of_damped {F : E → E} {ν : ℝ} (hF : ∀ x, ⟪x, F x⟫ ≤ -ν * ‖x‖ ^ 2)
    {x : ℝ → E} (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : ‖x t‖ ≤ Real.exp (-ν * t) * ‖x 0‖ := by
  set g : ℝ → ℝ := fun s => Real.exp (2 * ν * s) * ⟪x s, x s⟫ with hg
  have hderiv : ∀ s, 0 ≤ s → HasDerivWithinAt g
      (Real.exp (2 * ν * s) * (2 * ν) * ⟪x s, x s⟫ + Real.exp (2 * ν * s) * (2 * ⟪x s, F (x s)⟫))
      (Ici 0) s := by
    intro s hs
    have h1 : HasDerivWithinAt (fun s => Real.exp (2 * ν * s)) (Real.exp (2 * ν * s) * (2 * ν))
        (Ici 0) s := by
      have := ((hasDerivAt_id s).const_mul (2 * ν)).exp
      simpa using this.hasDerivWithinAt
    exact h1.mul (hasDerivWithinAt_energy (hx s hs))
  have hanti : AntitoneOn g (Ici 0) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun s hs => (hderiv s hs).continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs)).mono interior_subset) (fun s _ => ?_)
    have hpos := Real.exp_pos (2 * ν * s)
    have h1 := hF (x s)
    rw [real_inner_self_eq_norm_sq]
    have : Real.exp (2 * ν * s) * (2 * ν) * ‖x s‖ ^ 2 +
        Real.exp (2 * ν * s) * (2 * ⟪x s, F (x s)⟫) =
        2 * Real.exp (2 * ν * s) * (⟪x s, F (x s)⟫ + ν * ‖x s‖ ^ 2) := by ring
    rw [this]
    have : ⟪x s, F (x s)⟫ + ν * ‖x s‖ ^ 2 ≤ 0 := by linarith
    nlinarith
  have hle := hanti (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici (0 : ℝ) from ht) ht
  simp only [hg, mul_zero, Real.exp_zero, one_mul, real_inner_self_eq_norm_sq] at hle
  -- `exp (2νt) ‖x t‖² ≤ ‖x 0‖²`, so `‖x t‖² ≤ (exp (-νt) ‖x 0‖)²`.
  have hsq : ‖x t‖ ^ 2 ≤ (Real.exp (-ν * t) * ‖x 0‖) ^ 2 := by
    have he : Real.exp (2 * ν * t) * Real.exp (-ν * t) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      norm_num
      ring
    have hpos := Real.exp_pos (2 * ν * t)
    have : ‖x t‖ ^ 2 = Real.exp (-ν * t) ^ 2 * (Real.exp (2 * ν * t) * ‖x t‖ ^ 2) := by
      rw [← mul_assoc, mul_comm (Real.exp (-ν * t) ^ 2), he, one_mul]
    rw [this, mul_pow]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  have h0 : 0 ≤ Real.exp (-ν * t) * ‖x 0‖ := mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  nlinarith [norm_nonneg (x t)]

/-! ## D3. One step from a ball -/

/-- [definition] The step time from the ball of radius `ρ`: the inverse of a bound for the field
on the ball of radius `ρ + 1`, read from its value at the origin and its Lipschitz constant. -/
def stepTime (F : E → E) (K : ℝ≥0) (ρ : ℝ) : ℝ := 1 / (‖F 0‖ + K * (ρ + 1) + 1)

omit [InnerProductSpace ℝ E] in
theorem stepTime_pos (F : E → E) (K : ℝ≥0) {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 < stepTime F K ρ := by
  unfold stepTime
  have : (0 : ℝ) ≤ (K : ℝ) * (ρ + 1) := mul_nonneg K.2 (by linarith)
  positivity

/-- A derivative within a closed interval that does not contain the point: nothing to check. -/
theorem hasDerivWithinAt_Icc_of_notMem {f : ℝ → E} {f' : E} {a b t : ℝ} (ht : t ∉ Icc a b) :
    HasDerivWithinAt f f' (Icc a b) t := by
  have : t ∉ closure (Icc a b) := by rwa [closure_Icc]
  exact HasFDerivWithinAt.of_notMem_closure this

/-- A derivative within `[0, T]` at a point before `T` is a right derivative. -/
theorem hasDerivWithinAt_Ici_of_Icc {f : ℝ → E} {f' : E} {T t : ℝ} (ht : t ∈ Ico 0 T)
    (h : HasDerivWithinAt f f' (Icc 0 T) t) : HasDerivWithinAt f f' (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  exact mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)

variable [CompleteSpace E]

/-- [proved-derived; formal-checked] From any point of the ball of radius `ρ`, a solution for the
step time, by Picard–Lindelöf on the ball of radius one about the point. -/
theorem exists_step {F : E → E} {K : ℝ≥0} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hK : LipschitzOnWith K F (closedBall (0 : E) (ρ + 1))) {y : E} (hy : ‖y‖ ≤ ρ) (s : ℝ) :
    ∃ β : ℝ → E, β s = y ∧ ∀ t ∈ Icc s (s + stepTime F K ρ),
      HasDerivWithinAt β (F (β t)) (Icc s (s + stepTime F K ρ)) t := by
  have hh := stepTime_pos F K hρ
  set h := stepTime F K ρ with hh_def
  have hKρ : (0 : ℝ) ≤ (K : ℝ) * (ρ + 1) := mul_nonneg K.2 (by linarith)
  set L : ℝ≥0 := ⟨‖F 0‖ + K * (ρ + 1) + 1, by positivity⟩ with hL
  have hLval : (L : ℝ) = ‖F 0‖ + K * (ρ + 1) + 1 := rfl
  have hsub : closedBall y 1 ⊆ closedBall (0 : E) (ρ + 1) := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    rw [mem_closedBall, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - y) + y‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
      _ ≤ 1 + ρ := add_le_add hz hy
      _ = ρ + 1 := add_comm _ _
  have hb : ∀ z ∈ closedBall y (1 : ℝ≥0), ‖F z‖ ≤ L := by
    intro z hz
    have hz' := hsub (by simpa using hz)
    have hz0 : ‖z‖ ≤ ρ + 1 := mem_closedBall_zero_iff.mp hz'
    have h0 : (0 : E) ∈ closedBall (0 : E) (ρ + 1) := mem_closedBall_self (by linarith)
    have hl := hK.norm_sub_le hz' h0
    rw [sub_zero] at hl
    rw [hLval]
    calc ‖F z‖ ≤ ‖F z - F 0‖ + ‖F 0‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖z‖ + ‖F 0‖ := by linarith
      _ ≤ K * (ρ + 1) + ‖F 0‖ := by gcongr
      _ ≤ ‖F 0‖ + K * (ρ + 1) + 1 := by linarith
  have hl : LipschitzOnWith K F (closedBall y (1 : ℝ≥0)) :=
    hK.mono (by simpa using hsub)
  have hm : (L : ℝ) * max (s + h - s) (s - s) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ) := by
    have : max (s + h - s) (s - s) = h := by
      rw [add_sub_cancel_left, sub_self]
      exact max_eq_left hh.le
    rw [this, hh_def, stepTime, ← hLval]
    have hLpos : (0 : ℝ) < L := by rw [hLval]; positivity
    simp [hLpos.ne']
  have hs : s ∈ Icc s (s + h) := ⟨le_rfl, by linarith⟩
  have hPL := IsPicardLindelof.of_time_independent (tmin := s) (tmax := s + h)
    (t₀ := ⟨s, hs⟩) (x₀ := y) (a := 1) (r := 0) (L := L) (K := K) hb hl hm
  obtain ⟨β, hβ0, hβ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨β, hβ0, hβ⟩

/-! ## D4. A solution on every bounded interval -/

/-- [proved-derived; formal-checked] A solution on `[0, n * stepTime F K ρ]` from every state of
the ball of radius `ρ`, for every `n`: each step starts where the last ended, and that point is
still in the ball because the norm never rises. -/
theorem exists_on_Icc {F : E → E} (hF : Dissipative F) {K : ℝ≥0} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hK : LipschitzOnWith K F (closedBall (0 : E) (ρ + 1))) {x₀ : E} (hx₀ : ‖x₀‖ ≤ ρ) (n : ℕ) :
    ∃ α : ℝ → E, α 0 = x₀ ∧ ∀ t ∈ Icc 0 (n * stepTime F K ρ),
      HasDerivWithinAt α (F (α t)) (Icc 0 (n * stepTime F K ρ)) t := by
  have hh := stepTime_pos F K hρ
  set h := stepTime F K ρ with hh_def
  induction n with
  | zero =>
    obtain ⟨β, hβ0, hβ⟩ := exists_step hρ hK hx₀ 0
    refine ⟨β, hβ0, fun t ht => ?_⟩
    have hsub : Icc (0 : ℝ) ((0 : ℕ) * h) ⊆ Icc 0 (0 + h) := by
      apply Icc_subset_Icc le_rfl; simp; linarith
    exact (hβ t (hsub ht)).mono hsub
  | succ n ih =>
    obtain ⟨α, hα0, hα⟩ := ih
    set T : ℝ := n * h with hT
    have hT0 : 0 ≤ T := mul_nonneg (Nat.cast_nonneg n) hh.le
    have hnorm : ‖α T‖ ≤ ρ := by
      have hanti := norm_antitoneOn hF (convex_Icc 0 T) hα
      have := hanti (left_mem_Icc.mpr hT0) (right_mem_Icc.mpr hT0) hT0
      simp only at this
      rw [hα0] at this
      linarith
    obtain ⟨β, hβT, hβ⟩ := exists_step hρ hK hnorm T
    set γ : ℝ → E := fun t => if t ≤ T then α t else β t with hγ
    have hγα : EqOn γ α (Icc 0 T) := fun t ht => by simp [hγ, ht.2]
    have hγβ : EqOn γ β (Icc T (T + h)) := by
      intro t ht
      by_cases htT : t ≤ T
      · have : t = T := le_antisymm htT ht.1
        simp [hγ, this, hβT]
      · simp [hγ, htT]
    have hend : ((n + 1 : ℕ) : ℝ) * h = T + h := by rw [hT]; push_cast; ring
    refine ⟨γ, by simp [hγ, hT0, hα0], fun t ht => ?_⟩
    rw [hend] at ht ⊢
    have hunion : Icc 0 T ∪ Icc T (T + h) = Icc 0 (T + h) :=
      Icc_union_Icc_eq_Icc hT0 (by linarith)
    rw [← hunion]
    apply HasDerivWithinAt.union
    · by_cases htm : t ∈ Icc 0 T
      · have := (hα t htm).congr_of_mem hγα htm
        rwa [← hγα htm] at this
      · exact hasDerivWithinAt_Icc_of_notMem htm
    · by_cases htm : t ∈ Icc T (T + h)
      · have := (hβ t htm).congr_of_mem hγβ htm
        rwa [← hγβ htm] at this
      · exact hasDerivWithinAt_Icc_of_notMem htm

/-! ## D5. Uniqueness -/

omit [CompleteSpace E] in
/-- [proved-derived; formal-checked] Two solutions of a dissipative field that is Lipschitz on
balls, from one state, agree on every `[0, T]`: both stay in the ball of the opening norm, where the
field is Lipschitz. -/
theorem eqOn_Icc {F : E → E} (hF : Dissipative F) (hLip : LipschitzOnBalls F) {T : ℝ}
    {x y : ℝ → E} (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (F (x t)) (Icc 0 T) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (F (y t)) (Icc 0 T) t) (h0 : x 0 = y 0) :
    EqOn x y (Icc 0 T) := by
  obtain ⟨K, hK⟩ := hLip ‖x 0‖
  have hxa := norm_antitoneOn hF (convex_Icc 0 T) hx
  have hya := norm_antitoneOn hF (convex_Icc 0 T) hy
  by_cases hT : 0 ≤ T
  swap
  · intro t ht; exact absurd (ht.1.trans ht.2) hT
  have h0mem : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT
  apply ODE_solution_unique_of_mem_Icc_right (v := fun _ => F)
    (s := fun _ => closedBall (0 : E) ‖x 0‖) (K := K)
  · exact fun _ _ => hK
  · exact fun t ht => (hx t ht).continuousWithinAt
  · exact fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hx t (Ico_subset_Icc_self ht))
  · intro t ht
    rw [mem_closedBall_zero_iff]
    exact hxa h0mem (Ico_subset_Icc_self ht) ht.1
  · exact fun t ht => (hy t ht).continuousWithinAt
  · exact fun t ht => hasDerivWithinAt_Ici_of_Icc ht (hy t (Ico_subset_Icc_self ht))
  · intro t ht
    rw [mem_closedBall_zero_iff, h0]
    exact hya h0mem (Ico_subset_Icc_self ht) ht.1
  · exact h0

omit [CompleteSpace E] in
/-- [proved-derived; formal-checked] Two solutions on `[0, ∞)` from one state agree on
`[0, ∞)`. -/
theorem eqOn_Ici {F : E → E} (hF : Dissipative F) (hLip : LipschitzOnBalls F) {x y : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t)
    (hy : ∀ t, 0 ≤ t → HasDerivWithinAt y (F (y t)) (Ici 0) t) (h0 : x 0 = y 0) :
    EqOn x y (Ici 0) := by
  intro t ht
  have hsub : Icc (0 : ℝ) t ⊆ Ici 0 := Icc_subset_Ici_self
  exact eqOn_Icc hF hLip (T := t) (fun s hs => (hx s hs.1).mono hsub)
    (fun s hs => (hy s hs.1).mono hsub) h0 ⟨ht, le_rfl⟩

/-! ## D6. The global flow -/

/-- [proved-derived; formal-checked] **Global existence.** A dissipative field that is Lipschitz
on balls has, from every state, a solution on `[0, ∞)`, and its norm never rises above the
opening one. -/
theorem exists_global {F : E → E} (hF : Dissipative F) (hLip : LipschitzOnBalls F) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧ (∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → ‖x t‖ ≤ ‖x₀‖ := by
  set ρ := ‖x₀‖ with hρ_def
  have hρ : 0 ≤ ρ := norm_nonneg _
  obtain ⟨K, hK⟩ := hLip (ρ + 1)
  have hh := stepTime_pos F K hρ
  set h := stepTime F K ρ with hh_def
  have hex := fun n : ℕ => exists_on_Icc hF hρ hK le_rfl n
  choose α hα0 hα using hex
  -- The pieces agree where both are defined.
  have hagree : ∀ m n : ℕ, m ≤ n → EqOn (α m) (α n) (Icc 0 (m * h)) := by
    intro m n hmn
    have hsub : Icc (0 : ℝ) (m * h) ⊆ Icc 0 (n * h) :=
      Icc_subset_Icc le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hh.le)
    exact eqOn_Icc hF hLip (fun t ht => hα m t ht)
      (fun t ht => (hα n t (hsub ht)).mono hsub) ((hα0 m).trans (hα0 n).symm)
  set N : ℝ → ℕ := fun t => ⌈t / h⌉₊ + 1 with hN
  have hNlt : ∀ t, t < N t * h := by
    intro t
    have h1 : t / h ≤ ⌈t / h⌉₊ := Nat.le_ceil _
    have h2 : t = t / h * h := by field_simp
    have : (N t : ℝ) = ⌈t / h⌉₊ + 1 := by simp [hN]
    rw [this]
    nlinarith
  set x : ℝ → E := fun t => α (N t) t with hx_def
  have hxα : ∀ M : ℕ, EqOn x (α M) (Icc 0 (M * h)) := by
    intro M s hs
    simp only [hx_def]
    rcases le_total (N s) M with hle | hle
    · exact hagree (N s) M hle ⟨hs.1, (hNlt s).le⟩
    · exact (hagree M (N s) hle hs).symm
  have hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t := by
    intro t ht
    set M := N t
    have htM : t ∈ Icc 0 (M * h) := ⟨ht, (hNlt t).le⟩
    have h1 := (hα M t htM).congr_of_mem (hxα M) htM
    rw [← hxα M htM] at h1
    apply h1.mono_of_mem_nhdsWithin
    rw [mem_nhdsWithin]
    exact ⟨Iio (M * h), isOpen_Iio, hNlt t, fun s hs => ⟨hs.2, le_of_lt hs.1⟩⟩
  have hx0 : x 0 = x₀ := hα0 (N 0)
  refine ⟨x, hx0, hderiv, fun t ht => ?_⟩
  have hanti := norm_antitoneOn hF (convex_Ici 0) (fun s hs => hderiv s hs)
  have := hanti (Set.mem_Ici.mpr le_rfl) (show t ∈ Ici (0 : ℝ) from ht) ht
  simpa [hx0] using this

/-- [proved-derived; formal-checked] **The global flow is unique.** From every state there is
one solution on `[0, ∞)`, up to its values before time zero. -/
theorem existsUnique_global {F : E → E} (hF : Dissipative F) (hLip : LipschitzOnBalls F)
    (x₀ : E) :
    (∃ x : ℝ → E, x 0 = x₀ ∧ ∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t) ∧
      ∀ x y : ℝ → E, x 0 = x₀ → (∀ t, 0 ≤ t → HasDerivWithinAt x (F (x t)) (Ici 0) t) →
        y 0 = x₀ → (∀ t, 0 ≤ t → HasDerivWithinAt y (F (y t)) (Ici 0) t) → EqOn x y (Ici 0) := by
  refine ⟨?_, fun x y hx0 hx hy0 hy => eqOn_Ici hF hLip hx hy (hx0.trans hy0.symm)⟩
  obtain ⟨x, hx0, hx, -⟩ := exists_global hF hLip x₀
  exact ⟨x, hx0, hx⟩

end

/-! ## D7. The truncated fluid's shape: a damping and a feed that does no work -/

section Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] A linear map plus the diagonal of a bilinear map is
Lipschitz on every ball, with constant `‖A‖ + 2 ‖B‖ |R|` on the ball of radius `R`. -/
theorem lipschitzOnBalls_linear_add_bilinear (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) :
    LipschitzOnBalls (fun x => A x + B x x) := by
  intro R
  refine ⟨⟨‖A‖ + 2 * ‖B‖ * |R|, by positivity⟩, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  rw [mem_closedBall_zero_iff] at hx hy
  have hxR : ‖x‖ ≤ |R| := hx.trans (le_abs_self R)
  have hyR : ‖y‖ ≤ |R| := hy.trans (le_abs_self R)
  simp only [dist_eq_norm]
  have hBsub : B (x - y) x = B x x - B y x := by rw [map_sub]; rfl
  have hsplit : A x + B x x - (A y + B y y) = A (x - y) + (B (x - y) x + B y (x - y)) := by
    rw [hBsub, map_sub, (B y).map_sub]
    abel
  rw [hsplit]
  have h1 : ‖A (x - y)‖ ≤ ‖A‖ * ‖x - y‖ := A.le_opNorm _
  have h2 : ‖B (x - y) x‖ ≤ ‖B‖ * ‖x - y‖ * ‖x‖ := B.le_opNorm₂ _ _
  have h3 : ‖B y (x - y)‖ ≤ ‖B‖ * ‖y‖ * ‖x - y‖ := B.le_opNorm₂ _ _
  have hB := norm_nonneg B
  have hd := norm_nonneg (x - y)
  calc ‖A (x - y) + (B (x - y) x + B y (x - y))‖
      ≤ ‖A (x - y)‖ + ‖B (x - y) x + B y (x - y)‖ := norm_add_le _ _
    _ ≤ ‖A (x - y)‖ + (‖B (x - y) x‖ + ‖B y (x - y)‖) := by gcongr; exact norm_add_le _ _
    _ ≤ ‖A‖ * ‖x - y‖ + (‖B‖ * ‖x - y‖ * ‖x‖ + ‖B‖ * ‖y‖ * ‖x - y‖) := by gcongr
    _ ≤ ‖A‖ * ‖x - y‖ + (‖B‖ * ‖x - y‖ * |R| + ‖B‖ * |R| * ‖x - y‖) := by gcongr
    _ = (‖A‖ + 2 * ‖B‖ * |R|) * ‖x - y‖ := by ring

/-- [proved-derived; formal-checked] A damping that does no positive work and a feed that does
none give a dissipative field. -/
theorem dissipative_linear_add_bilinear {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E}
    (hA : ∀ x, ⟪x, A x⟫ ≤ 0) (hB : ∀ x, ⟪x, B x x⟫ = 0) :
    Dissipative (fun x => A x + B x x) := by
  intro x
  simp only [inner_add_right, hB, add_zero]
  exact hA x

/-- [proved-derived; formal-checked] With a damping rate, `⟪x, A x⟫ ≤ -ν ‖x‖²`, and a feed that
does no work, every solution decays at `exp (-ν t)`. -/
theorem norm_le_exp_quadratic {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E} {ν : ℝ}
    (hA : ∀ x, ⟪x, A x⟫ ≤ -ν * ‖x‖ ^ 2) (hB : ∀ x, ⟪x, B x x⟫ = 0) {x : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (A (x t) + B (x t) (x t)) (Ici 0) t) {t : ℝ}
    (ht : 0 ≤ t) : ‖x t‖ ≤ Real.exp (-ν * t) * ‖x 0‖ :=
  norm_le_exp_mul_of_damped (F := fun x => A x + B x x)
    (fun z => by simp only [inner_add_right, hB, add_zero]; exact hA z) hx ht

variable [CompleteSpace E]

/-- [proved-derived; formal-checked] **Every such law runs for all time.** With a damping that
does no positive work and a feed that does no work, there is a solution on `[0, ∞)` from every
state, its energy never rises, and it is the only one. -/
theorem exists_global_quadratic {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E}
    (hA : ∀ x, ⟪x, A x⟫ ≤ 0) (hB : ∀ x, ⟪x, B x x⟫ = 0) (x₀ : E) :
    ∃ x : ℝ → E, x 0 = x₀ ∧
      (∀ t, 0 ≤ t → HasDerivWithinAt x (A (x t) + B (x t) (x t)) (Ici 0) t) ∧
      ∀ t, 0 ≤ t → ‖x t‖ ≤ ‖x₀‖ :=
  exists_global (F := fun x => A x + B x x) (dissipative_linear_add_bilinear hA hB)
    (lipschitzOnBalls_linear_add_bilinear A B) x₀

omit [CompleteSpace E] in
/-- [proved-derived; formal-checked] The solution of `exists_global_quadratic` is unique on
`[0, ∞)`. -/
theorem existsUnique_global_quadratic {A : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E}
    (hA : ∀ x, ⟪x, A x⟫ ≤ 0) (hB : ∀ x, ⟪x, B x x⟫ = 0) {x y : ℝ → E}
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (A (x t) + B (x t) (x t)) (Ici 0) t)
    (hy : ∀ t, 0 ≤ t → HasDerivWithinAt y (A (y t) + B (y t) (y t)) (Ici 0) t)
    (h0 : x 0 = y 0) : EqOn x y (Ici 0) :=
  eqOn_Ici (F := fun x => A x + B x x) (dissipative_linear_add_bilinear hA hB)
    (lipschitzOnBalls_linear_add_bilinear A B) hx hy h0

end Quadratic

/-! ## Audit -/

section Audit

#print axioms norm_antitoneOn
#print axioms norm_le_exp_mul_of_damped
#print axioms exists_step
#print axioms exists_on_Icc
#print axioms eqOn_Icc
#print axioms eqOn_Ici
#print axioms exists_global
#print axioms existsUnique_global
#print axioms lipschitzOnBalls_linear_add_bilinear
#print axioms dissipative_linear_add_bilinear
#print axioms exists_global_quadratic
#print axioms existsUnique_global_quadratic
#print axioms norm_le_exp_quadratic

end Audit

end Holonics.Fluid.DissipativeGlobalFlow

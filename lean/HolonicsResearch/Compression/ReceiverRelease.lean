import Mathlib

/-!
# The receiver-conditioned release is the one law of least divergence and cost, and a ladder of hazards pays its rung

[proved-derived] Issue #410 (two boxes). The source is the record of September 27
(`research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md`,
§14.3 and §14.6); atlas `release.receiver-conditioned-law`, `switching.hazard-ladder-bound`.

What is proved.

1. **The receiver-conditioned release** (`objective_eq_div_release`, `objective_ge`, `objective_release`,
   `objective_eq_min_iff`, `release_unique_minimizer`). On a finite viable set `A` with the population's law
   `P₀ > 0`, the receiver's face `L_R > 0` and a cost `c_R` in bits, write `Q_R = P₀ · L_R · 2^(−c_R)/Z_R` on `A`.
   For every law `Q` on `A`, `D(Q‖P₀) + E_Q[c_R − log₂ L_R] = D(Q‖Q_R) − log₂ Z_R`; the divergence is nonnegative
   and vanishes only at `Q = Q_R` (`div2_nonneg`, `div2_eq_zero_iff`, from the term's bound `term_ge` and its case of
   equality `term_eq_iff`), so the objective is at least `−log₂ Z_R`, `Q_R` reaches it, and a law reaches it only by
   agreeing with `Q_R` on `A`.
2. **A mixture pays its rung** (`mixture_code_le`): for nonnegative weights `π` and the rungs' probabilities `p` of
   one outcome (a whole path included), `−log₂ Σ_i π_i p_i ≤ −log₂ p_j − log₂ π_j` at every rung with `π_j > 0` and
   `p_j > 0`. This is `L_adapt ≤ L_j − log₂ π_j`.
3. **The switch-and-stay charge** (`ladder_rung`, `switch_and_stay_charge`, `adaptive_code_le`). With `k` switches
   among `N` transitions, `1 ≤ k ≤ N/2`, the rung `j = ⌈log₂(N/k)⌉` is at least one, stands under
   `log₂(N/k) + 1` and has `N/k ≤ 2^j`; the fixed share's charge at that rung, `k j + 3 s/2^j` for `s` stays with
   `k + s = N` (`Compression/Landmark/Context/Dormancy.share_path_code_le`), is at most `k log₂(N/k) + 4k`; and a
   mixture over a ladder that holds the rung codes within `k log₂(N/k) + 4k − log₂ π_j` of the comparator path,
   without knowing where the switches fall.

Existing owners, cited and not repeated: `Compression/Landmark/Context/LocalWeighing` (the forward mixture, the fixed
share's kernel, `switches`, `stays`) and `Compression/Landmark/Context/Dormancy` (`share_path_code`, `stay_code_le`,
`share_path_code_le`: the charge `k j + 3 s/2^j` at the share `2^(−j)`).

Limits. The release is one receiver's law on one finite viable set at one state; timing, stopping and the choice
between sampling `Q_R` and taking its greatest term are not here. Statement 1 compares laws on `A` only, so its
uniqueness is agreement on `A`. Statement 3 is the arithmetic of the rung against the cited charge: the hypothesis
`hrung` of `adaptive_code_le` is `share_path_code_le`'s conclusion joined to a forward mixture's dominance, which
this module does not re-prove, and the ladder is assumed to hold the rung `⌈log₂(N/k)⌉`.

The computational object is the helical pair interaction: a release is the face a source's law shows a receiver
through their contact, the cost and the face's logarithm adding in the additive chart of the ratio. Of the winding
guide's six general objects this touches faces and placement (the release's face and the mixture's face) and the tube
(a path of stays and switches along a span); the helix, pair, cell holonomy and tower thread stay attached.

Consumers: #410's boxes "The receiver-conditioned release" and "The hazard-ladder mixture bound".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.ReceiverRelease

open Finset

/-! ## 1. The divergence of two laws on a finite set -/

section Divergence

variable {Ω : Type*}

/-- [definition] A law on a finite set: nonnegative there and of sum one. -/
structure IsLawOn (A : Finset Ω) (Q : Ω → ℝ) : Prop where
  nonneg : ∀ e ∈ A, 0 ≤ Q e
  sum_one : ∑ e ∈ A, Q e = 1

/-- [definition] The divergence in nats, `Σ_A Q ln(Q/R)`, a vanishing `Q` contributing nothing. -/
noncomputable def divNat (A : Finset Ω) (Q R : Ω → ℝ) : ℝ := ∑ e ∈ A, Q e * Real.log (Q e / R e)

/-- [definition] The divergence in bits, `Σ_A Q log₂(Q/R)`. -/
noncomputable def div2 (A : Finset Ω) (Q R : Ω → ℝ) : ℝ := ∑ e ∈ A, Q e * Real.logb 2 (Q e / R e)

/-- [proved-standard] **A term's bound**: `q − r ≤ q ln(q/r)` for `q ≥ 0`, `r > 0`. -/
theorem term_ge {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) : q - r ≤ q * Real.log (q / r) := by
  rcases hq.eq_or_lt with h | h
  · rw [← h, zero_mul]
    linarith
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hr h)
    have hinv : Real.log (q / r) = -Real.log (r / q) := by rw [← Real.log_inv, inv_div]
    have h2 : q * (r / q - 1) = r - q := by
      field_simp
    rw [hinv]
    nlinarith [mul_le_mul_of_nonneg_left hlog h.le]

/-- [proved-standard] **The term's bound is reached only at `q = r`.** -/
theorem term_eq_iff {q r : ℝ} (hq : 0 ≤ q) (hr : 0 < r) : q * Real.log (q / r) = q - r ↔ q = r := by
  constructor
  · intro heq
    by_contra hne
    rcases hq.eq_or_lt with h | h
    · rw [← h, zero_mul] at heq
      linarith
    · have hne' : r / q ≠ 1 := by
        intro h1
        rw [div_eq_one_iff_eq h.ne'] at h1
        exact hne h1.symm
      have hlog := Real.log_lt_sub_one_of_pos (div_pos hr h) hne'
      have hinv : Real.log (q / r) = -Real.log (r / q) := by rw [← Real.log_inv, inv_div]
      have h2 : q * (r / q - 1) = r - q := by
        field_simp
      rw [hinv] at heq
      nlinarith [mul_lt_mul_of_pos_left hlog h]
  · rintro rfl
    rw [div_self hr.ne', Real.log_one, mul_zero, sub_self]

variable {A : Finset Ω} {Q R : Ω → ℝ}

/-- [proved-standard] **The divergence is nonnegative** (Gibbs). -/
theorem divNat_nonneg (hQ : IsLawOn A Q) (hR : IsLawOn A R) (hRpos : ∀ e ∈ A, 0 < R e) : 0 ≤ divNat A Q R := by
  have h : ∑ e ∈ A, (Q e - R e) ≤ divNat A Q R :=
    Finset.sum_le_sum fun e he => term_ge (hQ.nonneg e he) (hRpos e he)
  rw [Finset.sum_sub_distrib, hQ.sum_one, hR.sum_one, sub_self] at h
  exact h

/-- [proved-standard] **The divergence vanishes only where the laws agree.** -/
theorem divNat_eq_zero_iff (hQ : IsLawOn A Q) (hR : IsLawOn A R) (hRpos : ∀ e ∈ A, 0 < R e) :
    divNat A Q R = 0 ↔ ∀ e ∈ A, Q e = R e := by
  have hsum : divNat A Q R = ∑ e ∈ A, (Q e * Real.log (Q e / R e) - (Q e - R e)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hQ.sum_one, hR.sum_one]
    unfold divNat
    ring
  rw [hsum, Finset.sum_eq_zero_iff_of_nonneg fun e he =>
    sub_nonneg.mpr (term_ge (hQ.nonneg e he) (hRpos e he))]
  refine forall₂_congr fun e he => ?_
  rw [sub_eq_zero, term_eq_iff (hQ.nonneg e he) (hRpos e he)]

/-- [proved-standard] Bits are nats over `ln 2`. -/
theorem div2_eq (A : Finset Ω) (Q R : Ω → ℝ) : div2 A Q R = divNat A Q R / Real.log 2 := by
  unfold div2 divNat
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Real.logb]
  ring

/-- [proved-standard] The divergence in bits is nonnegative. -/
theorem div2_nonneg (hQ : IsLawOn A Q) (hR : IsLawOn A R) (hRpos : ∀ e ∈ A, 0 < R e) : 0 ≤ div2 A Q R := by
  rw [div2_eq]
  exact div_nonneg (divNat_nonneg hQ hR hRpos) (Real.log_pos (by norm_num)).le

/-- [proved-standard] The divergence in bits vanishes only where the laws agree. -/
theorem div2_eq_zero_iff (hQ : IsLawOn A Q) (hR : IsLawOn A R) (hRpos : ∀ e ∈ A, 0 < R e) :
    div2 A Q R = 0 ↔ ∀ e ∈ A, Q e = R e := by
  rw [div2_eq, div_eq_zero_iff, divNat_eq_zero_iff hQ hR hRpos]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  simp [hlog]

end Divergence

/-! ## 2. The receiver-conditioned release -/

section Release

variable {Ω : Type*}

/-- [definition] A viable set with a positive prior and a positive receiver face on it. -/
structure Viable (A : Finset Ω) (P₀ L : Ω → ℝ) : Prop where
  nonempty : A.Nonempty
  prior_pos : ∀ e ∈ A, 0 < P₀ e
  face_pos : ∀ e ∈ A, 0 < L e

/-- [definition] An emission's weight: the prior times the receiver's face times `2^(−cost)`. -/
noncomputable def weight (P₀ L c : Ω → ℝ) (e : Ω) : ℝ := P₀ e * L e * (2 : ℝ) ^ (-c e)

/-- [definition] The normalizer `Z_R`, the sum of the weights over the viable set. -/
noncomputable def partition (A : Finset Ω) (P₀ L c : Ω → ℝ) : ℝ := ∑ e ∈ A, weight P₀ L c e

/-- [definition] The receiver-conditioned release `Q_R` on the viable set. -/
noncomputable def release (A : Finset Ω) (P₀ L c : Ω → ℝ) (e : Ω) : ℝ := weight P₀ L c e / partition A P₀ L c

/-- [definition] The objective `D(Q‖P₀) + E_Q[c_R − log₂ L_R]`, in bits. -/
noncomputable def objective (A : Finset Ω) (P₀ L c Q : Ω → ℝ) : ℝ :=
  div2 A Q P₀ + ∑ e ∈ A, Q e * (c e - Real.logb 2 (L e))

variable {A : Finset Ω} {P₀ L : Ω → ℝ}

/-- [proved-standard] A viable emission's weight is positive. -/
theorem weight_pos (h : Viable A P₀ L) (c : Ω → ℝ) {e : Ω} (he : e ∈ A) : 0 < weight P₀ L c e :=
  mul_pos (mul_pos (h.prior_pos e he) (h.face_pos e he)) (Real.rpow_pos_of_pos (by norm_num) _)

/-- [proved-standard] The normalizer is positive. -/
theorem partition_pos (h : Viable A P₀ L) (c : Ω → ℝ) : 0 < partition A P₀ L c :=
  Finset.sum_pos (fun _ he => weight_pos h c he) h.nonempty

/-- [proved-standard] The release is positive on the viable set. -/
theorem release_pos (h : Viable A P₀ L) (c : Ω → ℝ) {e : Ω} (he : e ∈ A) : 0 < release A P₀ L c e :=
  div_pos (weight_pos h c he) (partition_pos h c)

/-- [proved-standard] The release is a law on the viable set. -/
theorem release_isLaw (h : Viable A P₀ L) (c : Ω → ℝ) : IsLawOn A (release A P₀ L c) where
  nonneg := fun _ he => (release_pos h c he).le
  sum_one := by
    unfold release
    rw [← Finset.sum_div]
    exact div_self (partition_pos h c).ne'

/-- [proved-derived] **The variational identity**: for a law `Q` on the viable set,
`D(Q‖P₀) + E_Q[c_R − log₂ L_R] = D(Q‖Q_R) − log₂ Z_R`. -/
theorem objective_eq_div_release (h : Viable A P₀ L) (c : Ω → ℝ) {Q : Ω → ℝ} (hQ : IsLawOn A Q) :
    objective A P₀ L c Q = div2 A Q (release A P₀ L c) - Real.logb 2 (partition A P₀ L c) := by
  have hZ := partition_pos h c
  have hterm : ∀ e ∈ A, Q e * Real.logb 2 (Q e / P₀ e) + Q e * (c e - Real.logb 2 (L e)) =
      Q e * Real.logb 2 (Q e / release A P₀ L c e) - Q e * Real.logb 2 (partition A P₀ L c) := by
    intro e he
    rcases (hQ.nonneg e he).eq_or_lt with h0 | h0
    · rw [← h0]
      simp
    · have hP := h.prior_pos e he
      have hL := h.face_pos e he
      have hw := weight_pos h c he
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (-c e) := Real.rpow_pos_of_pos (by norm_num) _
      have hrel : Real.logb 2 (Q e / release A P₀ L c e) =
          Real.logb 2 (Q e) - (Real.logb 2 (P₀ e) + Real.logb 2 (L e) + -c e) +
            Real.logb 2 (partition A P₀ L c) := by
        unfold release
        rw [Real.logb_div h0.ne' (div_pos hw hZ).ne', Real.logb_div hw.ne' hZ.ne']
        unfold weight
        rw [Real.logb_mul (mul_pos hP hL).ne' h2.ne', Real.logb_mul hP.ne' hL.ne',
          Real.logb_rpow (by norm_num) (by norm_num)]
        ring
      rw [hrel, Real.logb_div h0.ne' hP.ne']
      ring
  unfold objective div2
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.sum_mul,
    hQ.sum_one, one_mul]

/-- [proved-derived] **The objective's floor**: every law on the viable set stands at or above `−log₂ Z_R`. -/
theorem objective_ge (h : Viable A P₀ L) (c : Ω → ℝ) {Q : Ω → ℝ} (hQ : IsLawOn A Q) :
    -Real.logb 2 (partition A P₀ L c) ≤ objective A P₀ L c Q := by
  rw [objective_eq_div_release h c hQ]
  have := div2_nonneg hQ (release_isLaw h c) fun e he => release_pos h c he
  linarith

/-- [proved-derived] **The floor is reached only at the release.** -/
theorem objective_eq_min_iff (h : Viable A P₀ L) (c : Ω → ℝ) {Q : Ω → ℝ} (hQ : IsLawOn A Q) :
    objective A P₀ L c Q = -Real.logb 2 (partition A P₀ L c) ↔ ∀ e ∈ A, Q e = release A P₀ L c e := by
  rw [objective_eq_div_release h c hQ,
    ← div2_eq_zero_iff hQ (release_isLaw h c) fun e he => release_pos h c he]
  constructor
  · intro heq
    linarith
  · intro heq
    rw [heq]
    ring

/-- [proved-derived] **The release reaches the floor.** -/
theorem objective_release (h : Viable A P₀ L) (c : Ω → ℝ) :
    objective A P₀ L c (release A P₀ L c) = -Real.logb 2 (partition A P₀ L c) :=
  (objective_eq_min_iff h c (release_isLaw h c)).mpr fun _ _ => rfl

/-- [proved-derived] **The receiver-conditioned release is the unique minimizer**: a law on the viable set has the
least `D(Q‖P₀) + E_Q[c_R − log₂ L_R]` among the laws on it exactly when it agrees with `Q_R` there. -/
theorem release_unique_minimizer (h : Viable A P₀ L) (c : Ω → ℝ) {Q : Ω → ℝ} (hQ : IsLawOn A Q) :
    (∀ Q' : Ω → ℝ, IsLawOn A Q' → objective A P₀ L c Q ≤ objective A P₀ L c Q') ↔
      ∀ e ∈ A, Q e = release A P₀ L c e := by
  constructor
  · intro hmin
    have h1 := hmin _ (release_isLaw h c)
    rw [objective_release h c] at h1
    exact (objective_eq_min_iff h c hQ).mp (le_antisymm h1 (objective_ge h c hQ))
  · intro heq Q' hQ'
    rw [(objective_eq_min_iff h c hQ).mpr heq]
    exact objective_ge h c hQ'

end Release

/-! ## 3. A mixture pays its rung, and the switch-and-stay charge -/

section Ladder

/-- [proved-standard] **A mixture pays its rung** (`L_adapt ≤ L_j − log₂ π_j`): the mixture's code of an outcome is
within `−log₂ π_j` of rung `j`'s. -/
theorem mixture_code_le {J : Type*} [Fintype J] (π p : J → ℝ) (hπ : ∀ i, 0 ≤ π i) (hp : ∀ i, 0 ≤ p i) (j : J)
    (hπj : 0 < π j) (hpj : 0 < p j) :
    -Real.logb 2 (∑ i, π i * p i) ≤ -Real.logb 2 (p j) - Real.logb 2 (π j) := by
  have hterm : π j * p j ≤ ∑ i, π i * p i :=
    Finset.single_le_sum (f := fun i => π i * p i) (fun i _ => mul_nonneg (hπ i) (hp i)) (Finset.mem_univ j)
  have hpos : 0 < π j * p j := mul_pos hπj hpj
  have hmono : Real.logb 2 (π j * p j) ≤ Real.logb 2 (∑ i, π i * p i) :=
    (Real.logb_le_logb (by norm_num) hpos (lt_of_lt_of_le hpos hterm)).mpr hterm
  rw [Real.logb_mul hπj.ne' hpj.ne'] at hmono
  linarith

/-- [proved-derived] **The ladder's rung** for `k` switches among `N` transitions, `1 ≤ k ≤ N/2`:
`j = ⌈log₂(N/k)⌉` is at least one, stands under `log₂(N/k) + 1`, and `N/k ≤ 2^j`. -/
theorem ladder_rung {N k : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ N) :
    1 ≤ ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ ∧
      (⌈Real.logb 2 ((N : ℝ) / k)⌉₊ : ℝ) < Real.logb 2 ((N : ℝ) / k) + 1 ∧
      (N : ℝ) / k ≤ 2 ^ ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN2 : (2 : ℝ) * k ≤ N := by exact_mod_cast hkN
  have hratio : (2 : ℝ) ≤ (N : ℝ) / k := by
    rw [le_div_iff₀ hk0]
    exact hN2
  have hpos : (0 : ℝ) < (N : ℝ) / k := by linarith
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 ((N : ℝ) / k) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hpos, Real.rpow_one]
    exact hratio
  refine ⟨?_, Nat.ceil_lt_add_one (by linarith), ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith)).ne'
  · calc (N : ℝ) / k = (2 : ℝ) ^ Real.logb 2 ((N : ℝ) / k) :=
          (Real.rpow_logb (by norm_num) (by norm_num) hpos).symm
      _ ≤ (2 : ℝ) ^ ((⌈Real.logb 2 ((N : ℝ) / k)⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ := Real.rpow_natCast _ _

/-- [proved-derived] **The switch-and-stay charge**: at the rung `j = ⌈log₂(N/k)⌉` the fixed share's charge
`k j + 3 s/2^j` for `k` switches and `s` stays, `k + s = N`, `1 ≤ k ≤ N/2`, is at most `k log₂(N/k) + 4k`. -/
theorem switch_and_stay_charge {N k s : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ N) (hs : k + s = N) :
    (k : ℝ) * ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ + s * (3 * (1 / 2 : ℝ) ^ ⌈Real.logb 2 ((N : ℝ) / k)⌉₊) ≤
      k * Real.logb 2 ((N : ℝ) / k) + 4 * k := by
  obtain ⟨_, hlt, hpow⟩ := ladder_rung hk hkN
  set j := ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ with hj
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hN0 : (0 : ℝ) < N := by
    have : (2 : ℝ) * k ≤ N := by exact_mod_cast hkN
    linarith
  have hsN : (s : ℝ) ≤ N := by
    have : (k : ℝ) + s = N := by exact_mod_cast hs
    linarith
  have h2j : (0 : ℝ) < 2 ^ j := by positivity
  have hhalf : (1 / 2 : ℝ) ^ j = 1 / 2 ^ j := by rw [one_div, inv_pow, one_div]
  have hinv : (1 : ℝ) / 2 ^ j ≤ k / N := by
    rw [div_le_div_iff₀ h2j hN0, one_mul]
    rw [div_le_iff₀ hk0] at hpow
    linarith
  have hstay : (s : ℝ) * (3 * (1 / 2 : ℝ) ^ j) ≤ 3 * k := by
    rw [hhalf]
    have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    have h1 : (s : ℝ) * (3 * (1 / 2 ^ j)) ≤ s * (3 * (k / N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (by norm_num)) hs0
    have h2 : (s : ℝ) * (3 * (k / N)) ≤ 3 * k := by
      have : (s : ℝ) * (3 * (k / N)) = 3 * k * (s / N) := by
        field_simp
      rw [this]
      have hsn : (s : ℝ) / N ≤ 1 := (div_le_one hN0).mpr hsN
      nlinarith
    linarith
  have hswitch : (k : ℝ) * j ≤ k * Real.logb 2 ((N : ℝ) / k) + k := by nlinarith
  linarith

/-- [proved-derived] **The adaptive code over a ladder**: if the rung `j = ⌈log₂(N/k)⌉` codes a passage within the
fixed share's charge of the comparator path, and the mixture pays the rung `−log₂ π_j`, the mixture codes it within
`k log₂(N/k) + 4k − log₂ π_j` of the comparator path. -/
theorem adaptive_code_le {N k s : ℕ} (hk : 1 ≤ k) (hkN : 2 * k ≤ N) (hs : k + s = N)
    {Ladapt Lrung Lpath logπ : ℝ}
    (hrung : Lrung ≤ Lpath + ((k : ℝ) * ⌈Real.logb 2 ((N : ℝ) / k)⌉₊ +
      s * (3 * (1 / 2 : ℝ) ^ ⌈Real.logb 2 ((N : ℝ) / k)⌉₊)))
    (hmix : Ladapt ≤ Lrung - logπ) :
    Ladapt ≤ Lpath + (k * Real.logb 2 ((N : ℝ) / k) + 4 * k) - logπ := by
  have := switch_and_stay_charge hk hkN hs
  linarith

end Ladder

end Holonics.Compression.ReceiverRelease

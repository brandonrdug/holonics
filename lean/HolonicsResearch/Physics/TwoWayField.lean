import Mathlib

/-!
# The field on a contact is its two one-way transports: the even part a constitution, the odd part a connection

The Einstein record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§4, §5.2, §5.4 and §14.6) carries the field of a contact as the undivided pair of its two one-way transports. Its §11
and §14.12 name the Lean statements #410 owes. This file proves six of them.

[proved-standard; formal-checked] What is proved.

1. **The two-way flow's parts** (§4): for positive one-way counts `F_ab`, `F_ba`, with `S = (F_ab + F_ba)/2` and
   `J = (F_ab − F_ba)/2`, the ratio `β = J/S` lies inside the unit interval (`abs_beta_lt_one`), the one-way ratio is
   its Doppler factor `(1 + β)/(1 − β) = F_ab/F_ba` (`doppler_ratio`), and in the log chart
   `ln F_ab = s + a`, `ln F_ba = s − a` with `β = tanh a` (`log_split`, `log_split_rev`, `beta_eq_tanh`). Turning the
   contact round keeps the even part and reverses the odd part (`even_swap`, `beta_swap`, `logEven_swap`,
   `logOdd_swap`), and the odd part adds along a path whose ratios multiply (`logOdd_adds`).
2. **The current is divergence-free at rest** (`current_divergence_free`): for a step with rows summing to one and a
   law it leaves at rest, the net current out of every configuration is zero.
3. **Grouped configurations** (§14.12; `grouped_flux_symm`, `grouped_ratio`): for a step with one rate each way on
   configurations and any grouping of them, the flux between two groups is the same both ways, so the groups'
   transition shares at rest satisfy `W_a · P_ab = W_b · P_ba`: `P_ab/P_ba = W_b/W_a`.
4. **A transport that composes round every triangle is a coboundary** (§5.2; `composes_iff_coboundary`), with the
   two conditions of 1944 as consequences (`composes_self`, `composes_inv`); **one slipped contact opens the triangles
   through it and no others** (`slip_self`, `slip_inv`, `slip_triangle_closed`, `slip_triangle_open`,
   `slip_triangle_open_iff`): the triangle's defect is a conjugate of the slip.
5. **A friction is a range** (§5.4, §14.6): a circle that keeps `γ = 1/(1 + d)` of its amplitude a step passes a unit
   `k` sites back at `γ^k` (`carry_closed_form`), reaches `(1 + d)/d` sites (`reach_hasSum`), rests under a unit drive
   at the power `(1 + d)²/(d(2 + d))` (`resting_power_hasSum`), the two in the ratio `(1 + d)/(2 + d)`, between a half
   and one (`power_over_reach`, `power_over_reach_bounds`); with no friction the power after `n` steps is `n`, with no
   resting value (`no_resting_value`). Its kernel `γ^|t|` solves the screened chain equation with
   `μ² = (1 − γ)²/γ = d²/(1 + d)` away from the source (`screened_mass`, `screened_chain`), and at the source it holds
   the strength `(1 − γ²)/γ` (`screened_source`).
6. **The determinant of a Hermitian form is kept by the moves of determinant one** (§11; `det_conj_form`,
   `det_kept`, `form_stays_hermitian`), and on a pair the determinant is the interval of a three and one
   (`hermitian_det_interval`).

Existing owners, cited and not repeated: `Physics/Spacetime/Boost` holds the Doppler chart of a boost (`betaOf`,
`abs_betaOf_lt_one`, `doppler_betaOf`), of which statement 1 is the reading on a contact's counts;
`Aeon/Production/Kolmogorov` holds the criterion that makes a family of two-way ratios one law's; `HNN/CarryGate` holds
the carry gate whose friction statement 5 reads (`leak_zero_group` is the reach at `d = 1/4`).

Limits. Statement 3 is the counting identity at rest on a finite set of configurations; it derives no dynamics for the
groups. Statement 4 is group-valued transport on a set of cells with every pair a contact; a complex with fewer contacts
needs its cycle space, which `Aeon/Production/Kolmogorov` holds in the abelian chart. Statement 5 is one linear circle
under a unit drive of independent terms; the fluctuation–dissipation relation in general is the literature's. The four
contexts on a cycle are in `Physics/ContextCycle`.

The computational object is the helical pair interaction: the pair of one-way transports is the contact, its even part
the contact material, its odd part the slip's connection. Of the winding guide's six general objects this touches the
pair (the two-way field), cell holonomy (the triangle's defect) and the tube (the carry's kernel along a span); the
helix, faces and placement and tower thread stay attached.

Consumers: #410's boxes for the two-way flow's parts, the grouped rates, the triangle's coboundary, the friction's
reach, the resting power and the determinant on Hermitian forms; atlas `store.finite-quality`,
`lorentz.doppler-ratio-chart`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.TwoWayField

/-! ## 1. The two one-way transports of a contact -/

section Pair

/-- [definition] The even part of a contact's two one-way counts: `S = (F_ab + F_ba)/2`. -/
noncomputable def even (F G : ℝ) : ℝ := (F + G) / 2

/-- [definition] The odd part: the net current `J = (F_ab − F_ba)/2`. -/
noncomputable def odd (F G : ℝ) : ℝ := (F - G) / 2

/-- [definition] The ratio of the odd part to the even part, `β = J/S`. -/
noncomputable def beta (F G : ℝ) : ℝ := odd F G / even F G

/-- [definition] The even part in the log chart, `s = ½ ln(F_ab F_ba)`. -/
noncomputable def logEven (F G : ℝ) : ℝ := 1 / 2 * Real.log (F * G)

/-- [definition] The odd part in the log chart, the rapidity `a = ½ ln(F_ab / F_ba)`. -/
noncomputable def logOdd (F G : ℝ) : ℝ := 1 / 2 * Real.log (F / G)

/-- [proved-standard] Turning the contact round keeps the even part. -/
theorem even_swap (F G : ℝ) : even G F = even F G := by
  unfold even; ring

/-- [proved-standard] Turning the contact round reverses the odd part. -/
theorem odd_swap (F G : ℝ) : odd G F = -odd F G := by
  unfold odd; ring

/-- [proved-standard] **Reversal is transposition**: turning the contact round reverses `β`. -/
theorem beta_swap (F G : ℝ) : beta G F = -beta F G := by
  unfold beta
  rw [even_swap, odd_swap, neg_div]

/-- [proved-standard] **Positive counts keep `β` inside the unit interval**: the cone is the positivity of the two
counts. -/
theorem abs_beta_lt_one {F G : ℝ} (hF : 0 < F) (hG : 0 < G) : |beta F G| < 1 := by
  unfold beta even odd
  have hS : 0 < (F + G) / 2 := by positivity
  rw [abs_div, abs_of_pos hS, div_lt_one hS, abs_lt]
  constructor <;> linarith

/-- [proved-standard] **The one-way ratio is a Doppler factor**: `(1 + β)/(1 − β) = F_ab/F_ba`. -/
theorem doppler_ratio {F G : ℝ} (hF : 0 < F) (hG : 0 < G) :
    (1 + beta F G) / (1 - beta F G) = F / G := by
  unfold beta even odd
  have hFG : F + G ≠ 0 := by positivity
  have hG' : G ≠ 0 := hG.ne'
  have h1 : (1 : ℝ) + (F - G) / 2 / ((F + G) / 2) = 2 * F / (F + G) := by
    field_simp; ring
  have h2 : (1 : ℝ) - (F - G) / 2 / ((F + G) / 2) = 2 * G / (F + G) := by
    field_simp; ring
  rw [h1, h2]
  field_simp

/-- [proved-standard] The log chart splits a one-way count into its even and odd parts: `ln F_ab = s + a`. -/
theorem log_split {F G : ℝ} (hF : 0 < F) (hG : 0 < G) :
    Real.log F = logEven F G + logOdd F G := by
  unfold logEven logOdd
  rw [Real.log_mul hF.ne' hG.ne', Real.log_div hF.ne' hG.ne']; ring

/-- [proved-standard] The reverse count has the same even part and the opposite odd part: `ln F_ba = s − a`. -/
theorem log_split_rev {F G : ℝ} (hF : 0 < F) (hG : 0 < G) :
    Real.log G = logEven F G - logOdd F G := by
  unfold logEven logOdd
  rw [Real.log_mul hF.ne' hG.ne', Real.log_div hF.ne' hG.ne']; ring

/-- [proved-standard] The log chart's even part is kept by turning the contact round. -/
theorem logEven_swap (F G : ℝ) : logEven G F = logEven F G := by
  unfold logEven; rw [mul_comm G F]

/-- [proved-standard] The rapidity reverses when the contact is turned round. -/
theorem logOdd_swap {F G : ℝ} (hF : 0 < F) (hG : 0 < G) : logOdd G F = -logOdd F G := by
  unfold logOdd
  rw [Real.log_div hG.ne' hF.ne', Real.log_div hF.ne' hG.ne']; ring

/-- [proved-standard] **`β = tanh a`**: the ratio of the odd to the even part is the hyperbolic tangent of the
rapidity, so `a` is a rapidity and `(1 + β)/(1 − β)` its Doppler factor. -/
theorem beta_eq_tanh {F G : ℝ} (hF : 0 < F) (hG : 0 < G) : beta F G = Real.tanh (logOdd F G) := by
  have hr : 0 < F / G := div_pos hF hG
  have hexp : Real.exp (logOdd F G) ^ 2 = F / G := by
    unfold logOdd
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (1 / 2 * Real.log (F / G)) = Real.log (F / G) := by push_cast; ring
    rw [this, Real.exp_log hr]
  have hpos : 0 < Real.exp (logOdd F G) := Real.exp_pos _
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg]
  set e := Real.exp (logOdd F G) with he
  have he0 : e ≠ 0 := hpos.ne'
  have hG' : G ≠ 0 := hG.ne'
  have hFG : F + G ≠ 0 := by positivity
  have h1 : (e - e⁻¹) / 2 / ((e + e⁻¹) / 2) = (e ^ 2 - 1) / (e ^ 2 + 1) := by
    have : e ^ 2 + 1 ≠ 0 := by positivity
    field_simp
  rw [h1, hexp]
  unfold beta even odd
  field_simp

/-- [proved-standard] **The rapidity adds along a path**: where the one-way ratios multiply, the odd parts add. -/
theorem logOdd_adds {F₁ G₁ F₂ G₂ F₃ G₃ : ℝ} (h₁ : 0 < F₁ / G₁) (h₂ : 0 < F₂ / G₂)
    (h : F₃ / G₃ = F₁ / G₁ * (F₂ / G₂)) : logOdd F₃ G₃ = logOdd F₁ G₁ + logOdd F₂ G₂ := by
  unfold logOdd
  rw [h, Real.log_mul h₁.ne' h₂.ne']; ring

end Pair

/-! ## 2. The current at rest -/

section Rest

variable {S : Type*} [Fintype S]

/-- [proved-standard] **The current is divergence-free at rest**: for a step `P` whose rows sum to one and a law `π` it
leaves at rest, the one-way counts `F_ab = π_a P_ab` have net current zero out of every configuration. -/
theorem current_divergence_free (P : S → S → ℝ) (π : S → ℝ) (hrow : ∀ a, ∑ b, P a b = 1)
    (hrest : ∀ a, ∑ b, π b * P b a = π a) (a : S) :
    ∑ b, (π a * P a b - π b * P b a) = 0 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hrow a, hrest a]; ring

end Rest

/-! ## 3. Grouped configurations -/

section Grouped

variable {Ω Γ : Type*} [Fintype Ω] [DecidableEq Γ]

/-- [definition] The flux between two groups of configurations: the sum of the configurations' rates. -/
def groupFlux (k : Ω → Ω → ℝ) (g : Ω → Γ) (a b : Γ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => g i = a), ∑ j ∈ Finset.univ.filter (fun j => g j = b), k i j

/-- [definition] The count of configurations in a group. -/
def groupCount (g : Ω → Γ) (a : Γ) : ℕ := (Finset.univ.filter (fun i => g i = a)).card

/-- [proved-standard] **One rate each way gives one flux each way between any two groups.** -/
theorem grouped_flux_symm (k : Ω → Ω → ℝ) (hk : ∀ i j, k i j = k j i) (g : Ω → Γ) (a b : Γ) :
    groupFlux k g a b = groupFlux k g b a := by
  unfold groupFlux
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hk i j

/-- [proved-standard] **`P_ab/P_ba = W_b/W_a` at rest**: with every configuration of a group equally likely, the share
of a group's weight that steps to another is its flux over its count, and the two shares stand in the inverse ratio of
the counts. -/
theorem grouped_ratio (k : Ω → Ω → ℝ) (hk : ∀ i j, k i j = k j i) (g : Ω → Γ) (a b : Γ)
    (ha : 0 < groupCount g a) (hb : 0 < groupCount g b) :
    (groupCount g a : ℝ) * (groupFlux k g a b / groupCount g a) =
      (groupCount g b : ℝ) * (groupFlux k g b a / groupCount g b) := by
  have ha' : (groupCount g a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (groupCount g b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  rw [mul_div_cancel₀ _ ha', mul_div_cancel₀ _ hb', grouped_flux_symm k hk g a b]

end Grouped

/-! ## 4. A transport that composes round every triangle is a coboundary -/

section Transport

variable {X G : Type*} [Group G]

/-- [proved-standard] A transport that composes carries a cell to itself by the identity. -/
theorem composes_self (g : X → X → G) (h : ∀ a b c, g a b * g b c = g a c) (a : X) : g a a = 1 := by
  have := h a a a
  exact mul_eq_left.mp this

/-- [proved-standard] A transport that composes reverses by inversion. -/
theorem composes_inv (g : X → X → G) (h : ∀ a b c, g a b * g b c = g a c) (a b : X) :
    g b a = (g a b)⁻¹ := by
  have := h a b a
  rw [composes_self g h a] at this
  exact eq_inv_of_mul_eq_one_right this

/-- [proved-standard] **Far parallelism is the flat case**: a group-valued transport composes round every triangle
exactly when it is the coboundary of a frame at every cell, `g(a, b) = h(a)⁻¹ h(b)`, the frame recovered from one base
cell as `h(a) = g(o, a)`. -/
theorem composes_iff_coboundary (g : X → X → G) :
    (∀ a b c, g a b * g b c = g a c) ↔ ∃ h : X → G, ∀ a b, g a b = (h a)⁻¹ * h b := by
  constructor
  · intro hg
    rcases isEmpty_or_nonempty X with hX | ⟨⟨o⟩⟩
    · exact ⟨fun _ => 1, fun a => (hX.false a).elim⟩
    · refine ⟨fun a => g o a, fun a b => ?_⟩
      rw [← composes_inv g hg o a, hg a o b]
  · rintro ⟨h, hg⟩ a b c
    rw [hg a b, hg b c, hg a c]; group

variable [DecidableEq X]

/-- [definition] **A flat transport with one contact slipped**: the transport of the frames `h`, with the contact
`(u, v)` multiplied by `k` one way and by `k⁻¹` the other. -/
def slip (h : X → G) (u v : X) (k : G) (a b : X) : G :=
  if a = u ∧ b = v then (h u)⁻¹ * h v * k
  else if a = v ∧ b = u then k⁻¹ * ((h v)⁻¹ * h u)
  else (h a)⁻¹ * h b

/-- [proved-standard] The slipped transport still carries a cell to itself by the identity. -/
theorem slip_self (h : X → G) {u v : X} (huv : u ≠ v) (k : G) (a : X) : slip h u v k a a = 1 := by
  unfold slip
  have h1 : ¬(a = u ∧ a = v) := fun ⟨h1, h2⟩ => huv (h1 ▸ h2)
  have h2 : ¬(a = v ∧ a = u) := fun ⟨h1, h2⟩ => huv (h2 ▸ h1)
  rw [if_neg h1, if_neg h2, inv_mul_cancel]

/-- [proved-standard] The slipped transport still reverses by inversion: it keeps both conditions of 1944. -/
theorem slip_inv (h : X → G) {u v : X} (huv : u ≠ v) (k : G) (a b : X) :
    slip h u v k b a = (slip h u v k a b)⁻¹ := by
  unfold slip
  by_cases h1 : a = u ∧ b = v
  · obtain ⟨rfl, rfl⟩ := h1
    have h2 : ¬(b = a ∧ a = b) := fun ⟨h1, _⟩ => huv h1.symm
    rw [if_neg h2, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩]; group
  · by_cases h2 : a = v ∧ b = u
    · obtain ⟨rfl, rfl⟩ := h2
      have h3 : ¬(a = b ∧ b = a) := fun ⟨h1, _⟩ => huv h1.symm
      rw [if_pos ⟨rfl, rfl⟩, if_neg h3, if_pos ⟨rfl, rfl⟩]; group
    · have h3 : ¬(b = u ∧ a = v) := fun ⟨hb, ha⟩ => h2 ⟨ha, hb⟩
      have h4 : ¬(b = v ∧ a = u) := fun ⟨hb, ha⟩ => h1 ⟨ha, hb⟩
      rw [if_neg h3, if_neg h4, if_neg h1, if_neg h2]; group

/-- [proved-standard] **A triangle with no side on the slipped contact still closes.** -/
theorem slip_triangle_closed (h : X → G) (u v : X) (k : G) (a b c : X)
    (hab : ¬(a = u ∧ b = v) ∧ ¬(a = v ∧ b = u)) (hbc : ¬(b = u ∧ c = v) ∧ ¬(b = v ∧ c = u))
    (hca : ¬(c = u ∧ a = v) ∧ ¬(c = v ∧ a = u)) :
    slip h u v k a b * slip h u v k b c * slip h u v k c a = 1 := by
  unfold slip
  rw [if_neg hab.1, if_neg hab.2, if_neg hbc.1, if_neg hbc.2, if_neg hca.1, if_neg hca.2]; group

/-- [proved-standard] **A triangle through the slipped contact opens by a conjugate of the slip.** -/
theorem slip_triangle_open (h : X → G) {u v : X} (k : G) {c : X} (hcu : c ≠ u)
    (hcv : c ≠ v) :
    slip h u v k u v * slip h u v k v c * slip h u v k c u =
      (h u)⁻¹ * (h v * k * (h v)⁻¹) * h u := by
  unfold slip
  have h1 : ¬(v = u ∧ c = v) := fun ⟨_, h2⟩ => hcv h2
  have h2 : ¬(v = v ∧ c = u) := fun ⟨_, h2⟩ => hcu h2
  have h3 : ¬(c = u ∧ u = v) := fun ⟨h1, _⟩ => hcu h1
  have h4 : ¬(c = v ∧ u = u) := fun ⟨h1, _⟩ => hcv h1
  rw [if_pos ⟨rfl, rfl⟩, if_neg h1, if_neg h2, if_neg h3, if_neg h4]; group

/-- [proved-standard] **The triangle's defect is the content**: a triangle through the slipped contact closes exactly
when the slip is the identity. -/
theorem slip_triangle_open_iff (h : X → G) {u v : X} (k : G) {c : X} (hcu : c ≠ u)
    (hcv : c ≠ v) :
    slip h u v k u v * slip h u v k v c * slip h u v k c u = 1 ↔ k = 1 := by
  rw [slip_triangle_open h k hcu hcv]
  constructor
  · intro hk
    have h1 : h v * k * (h v)⁻¹ = 1 := by
      have := congrArg (fun x => h u * x * (h u)⁻¹) hk
      simpa [mul_assoc] using this
    have h2 := congrArg (fun x => (h v)⁻¹ * x * h v) h1
    simpa [mul_assoc] using h2
  · rintro rfl
    group

end Transport

/-! ## 5. A friction is a range, and a store holds by upkeep -/

section Friction

/-- [definition] The share of its amplitude a circle of friction `d` keeps a step, `γ = 1/(1 + d)`. -/
noncomputable def keep (d : ℝ) : ℝ := 1 / (1 + d)

/-- [proved-standard] A positive friction keeps a share strictly between zero and one. -/
theorem keep_pos_lt_one {d : ℝ} (hd : 0 < d) : 0 < keep d ∧ keep d < 1 := by
  unfold keep
  constructor
  · positivity
  · rw [div_lt_one (by linarith)]; linarith

/-- [proved-standard] **A carry passes a unit `k` sites back at `γ^k`**: the recurrence `Q(t) = b(t) + γ Q(t − 1)`
begun at `Q(0) = b(0)` has the closed form `Q(n) = Σ_(k ≤ n) γ^k b(n − k)`. -/
theorem carry_closed_form (γ : ℝ) (b Q : ℕ → ℝ) (h0 : Q 0 = b 0)
    (hstep : ∀ n, Q (n + 1) = b (n + 1) + γ * Q n) (n : ℕ) :
    Q n = ∑ k ∈ Finset.range (n + 1), γ ^ k * b (n - k) := by
  induction n with
  | zero => simp [h0]
  | succ n ih =>
    rw [hstep n, ih, Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.succ_sub_succ_eq_sub]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring

/-- [proved-standard] **A friction's reach**: the amplitudes `γ^k` a unit leaves along the sites behind it sum to
`(1 + d)/d`. -/
theorem reach_hasSum {d : ℝ} (hd : 0 < d) : HasSum (fun k : ℕ => keep d ^ k) ((1 + d) / d) := by
  obtain ⟨h0, h1⟩ := keep_pos_lt_one hd
  have h := hasSum_geometric_of_lt_one h0.le h1
  have hval : (1 - keep d)⁻¹ = (1 + d) / d := by
    unfold keep
    have h1d : (1 : ℝ) + d ≠ 0 := by positivity
    have hd' : d ≠ 0 := hd.ne'
    have hkey : 1 - 1 / (1 + d) = d / (1 + d) := by
      field_simp
      ring
    rw [hkey, inv_div]
  rwa [hval] at h

/-- [proved-standard] **A leaking circle's resting power**: under a unit drive of independent terms the powers
`γ^(2k)` sum to `(1 + d)²/(d(2 + d))`. -/
theorem resting_power_hasSum {d : ℝ} (hd : 0 < d) :
    HasSum (fun k : ℕ => (keep d ^ k) ^ 2) ((1 + d) ^ 2 / (d * (2 + d))) := by
  obtain ⟨h0, h1⟩ := keep_pos_lt_one hd
  have hsq0 : 0 ≤ keep d ^ 2 := by positivity
  have hsq1 : keep d ^ 2 < 1 := by nlinarith
  have h := hasSum_geometric_of_lt_one hsq0 hsq1
  have hval : (1 - keep d ^ 2)⁻¹ = (1 + d) ^ 2 / (d * (2 + d)) := by
    unfold keep
    have h1d : (1 : ℝ) + d ≠ 0 := by positivity
    have hkey : 1 - (1 / (1 + d)) ^ 2 = d * (2 + d) / (1 + d) ^ 2 := by
      field_simp
      ring
    rw [hkey, inv_div]
  rw [hval] at h
  have hfun : (fun k : ℕ => (keep d ^ k) ^ 2) = fun k => (keep d ^ 2) ^ k := by
    funext k
    ring
  rw [hfun]
  exact h

/-- [proved-standard] **What a store holds and how long it holds it are one figure**: the resting power over the reach
is `(1 + d)/(2 + d)`. -/
theorem power_over_reach {d : ℝ} (hd : 0 < d) :
    (1 + d) ^ 2 / (d * (2 + d)) / ((1 + d) / d) = (1 + d) / (2 + d) := by
  have : (1 : ℝ) + d ≠ 0 := by positivity
  have hd' : d ≠ 0 := hd.ne'
  have h2 : (2 : ℝ) + d ≠ 0 := by positivity
  field_simp

/-- [proved-standard] The ratio stands between a half and one, and at small friction it is near a half. -/
theorem power_over_reach_bounds {d : ℝ} (hd : 0 < d) :
    1 / 2 < (1 + d) / (2 + d) ∧ (1 + d) / (2 + d) < 1 ∧ (1 + d) / (2 + d) - 1 / 2 < d / 4 := by
  have h2 : (0 : ℝ) < 2 + d := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [div_lt_div_iff₀ (by norm_num) h2]; linarith
  · rw [div_lt_one h2]; linarith
  · rw [sub_lt_iff_lt_add, div_lt_iff₀ h2]; nlinarith

/-- [proved-standard] **With no friction there is no resting value**: at `d = 0` the power after `n` steps is `n`. -/
theorem no_resting_value (n : ℕ) : ∑ k ∈ Finset.range n, (keep 0 ^ k) ^ 2 = n := by
  simp [keep]

/-- [definition] The kernel of a carry along a span of sites, `γ^|t|`. -/
noncomputable def kernel (d : ℝ) (t : ℤ) : ℝ := keep d ^ t.natAbs

/-- [proved-standard] The kernel reads the same both ways along the span. -/
theorem kernel_symm (d : ℝ) (t : ℤ) : kernel d (-t) = kernel d t := by
  unfold kernel; rw [Int.natAbs_neg]

/-- [proved-standard] **The friction's mass**: `μ² = (1 − γ)²/γ = d²/(1 + d)`. -/
theorem screened_mass {d : ℝ} (hd : 0 < d) : (1 - keep d) ^ 2 / keep d = d ^ 2 / (1 + d) := by
  unfold keep
  have : (1 : ℝ) + d ≠ 0 := by positivity
  field_simp
  ring

/-- [proved-standard] **The screened chain equation** away from the source: `K(t + 1) + K(t − 1) − 2K(t) = μ² K(t)`
with `μ² = d²/(1 + d)`. -/
theorem screened_chain {d : ℝ} (hd : 0 < d) {t : ℤ} (ht : t ≠ 0) :
    kernel d (t + 1) + kernel d (t - 1) - 2 * kernel d t = d ^ 2 / (1 + d) * kernel d t := by
  obtain ⟨h0, _⟩ := keep_pos_lt_one hd
  have key : ∀ m : ℕ, keep d ^ (m + 2) + keep d ^ m - 2 * keep d ^ (m + 1) =
      d ^ 2 / (1 + d) * keep d ^ (m + 1) := by
    intro m
    rw [← screened_mass hd]
    have hk : keep d ≠ 0 := h0.ne'
    field_simp
    ring
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg t
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := Nat.exists_eq_succ_of_ne_zero (by exact_mod_cast ht)
    have e1 : ((m + 1 : ℕ) : ℤ) + 1 = ((m + 2 : ℕ) : ℤ) := by push_cast; ring
    have e2 : ((m + 1 : ℕ) : ℤ) - 1 = ((m : ℕ) : ℤ) := by push_cast; ring
    unfold kernel
    rw [e1, e2, Int.natAbs_natCast, Int.natAbs_natCast, Int.natAbs_natCast]
    exact key m
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by intro h; apply ht; rw [h]; simp)
    have e1 : -((m + 1 : ℕ) : ℤ) + 1 = -((m : ℕ) : ℤ) := by push_cast; ring
    have e2 : -((m + 1 : ℕ) : ℤ) - 1 = -((m + 2 : ℕ) : ℤ) := by push_cast; ring
    unfold kernel
    rw [e1, e2, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_neg, Int.natAbs_natCast,
      Int.natAbs_natCast, Int.natAbs_natCast]
    have := key m
    linarith

/-- [proved-standard] **At the source** the kernel holds the strength `(1 − γ²)/γ`:
`K(1) + K(−1) − 2K(0) = μ² K(0) − (1 − γ²)/γ`. -/
theorem screened_source {d : ℝ} (hd : 0 < d) :
    kernel d 1 + kernel d (-1) - 2 * kernel d 0 =
      d ^ 2 / (1 + d) * kernel d 0 - (1 - keep d ^ 2) / keep d := by
  obtain ⟨h0, _⟩ := keep_pos_lt_one hd
  rw [← screened_mass hd]
  unfold kernel
  have hk : keep d ≠ 0 := h0.ne'
  simp only [Int.natAbs_one, Int.natAbs_neg, Int.natAbs_zero, pow_one, pow_zero]
  field_simp
  ring

end Friction

/-! ## 6. The determinant of a Hermitian form under a move -/

section Forms

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-standard] A move `A` acts on a form `X` as `Aᴴ X A`, and the determinant scales by `|det A|²`. -/
theorem det_conj_form (A X : Matrix n n ℂ) :
    (Aᴴ * X * A).det = star A.det * X.det * A.det := by
  rw [det_mul, det_mul, det_conjTranspose]

/-- [proved-standard] **The determinant of a form is kept by the moves of determinant one.** -/
theorem det_kept (A X : Matrix n n ℂ) (hA : A.det = 1) : (Aᴴ * X * A).det = X.det := by
  rw [det_conj_form, hA]; simp

omit [DecidableEq n] in
/-- [proved-standard] A Hermitian form stays Hermitian under every move. -/
theorem form_stays_hermitian (A X : Matrix n n ℂ) (hX : X.IsHermitian) : (Aᴴ * X * A).IsHermitian :=
  isHermitian_conjTranspose_mul_mul A hX

/-- [proved-standard] **On a pair the determinant is the interval of a three and one**: the Hermitian form with
diagonal `t ± z` and off-diagonal `x ∓ i y` has determinant `t² − x² − y² − z²`. -/
theorem hermitian_det_interval (t x y z : ℝ) :
    (!![(t + z : ℂ), x - Complex.I * y; x + Complex.I * y, t - z]).det =
      ((t ^ 2 - x ^ 2 - y ^ 2 - z ^ 2 : ℝ) : ℂ) := by
  rw [det_fin_two_of]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

end Forms

end Holonics.Physics.TwoWayField

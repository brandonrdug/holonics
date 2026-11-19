import Mathlib

/-!
# A base-two face: the price of a letter founded at the least bias, and the loud face's return

[proved-derived; formal-checked] Two of #410's statements on the readout's face at temperature one. A class `a` of
logit `z_a` holds the share `p(a) = 2^(z_a) / Σ_b 2^(z_b)` (`share`, over the face's `mass`) and its code is
`−log₂ p(a)` (`code`), as `TowerFace` reads a face (masses `2^(z_a − z_max)`, `face_code`). Every release at `2^(−16)`
is the identity in this smooth chart; §3 states what the grain does.

**§1. A letter founded at the least class bias** (the opening's room record of November 12,
`research/records/2026-11-12_A_LAPS_CARD_TIME_STANDS_IN_THE_OPENINGS_EMPTY_ROOM_…`, §4 item 4 and §7; atlas
`tower.field-growth-by-letters`; `Constitution::lettered`). `F` fresh classes join `A` standing ones with their rows of
the encoding at zero and their class bias at `c_min = min_(b<A) c_b` (`cMin`), so at a face `z(a) = ⟨E(a), y⟩ + c_a` a
fresh class reads `c_min` (`fresh_logit`) and the grown face's logits are the standing ones beside `F` copies of `c_min`
(`grown`). Over any standing logits `z` and any fresh logit `c`:

1. **The mass** (`mass_grown`): the grown face's mass is `Σ_a 2^(z_a) + F·2^c`.
2. **The price** (`price_eq`): every standing class's code rises by `log₂(1 + F·2^c / Σ_(a<A) 2^(z_a))` (`price`), the
   fresh classes' mass at the least bias over the face's standing sum; it is at least zero and at most that ratio over
   `ln 2` (`price_nonneg`, `price_le`).
3. **The fresh classes' joint share** (`freshShare_eq`, `one_sub_freshShare`): `q = F·2^c / (Σ_a 2^(z_a) + F·2^c)`, and
   `1 − q = 2^(−price)`.
4. **Each standing share moves by at most the joint mass**: the share after is the share before times `1 − q`, which is
   `2^(−price)` (`share_grown`, `share_grown_eq_price`); in absolute form it falls by `p(t)·q`, between `0` and `q`
   (`share_drop`, `share_drop_le`); in relative form it falls by `q` exactly (`relative_drop`). The standing classes
   lose `q` between them (`standing_loss`), so the two faces stand `2q` apart in the sum of absolute differences, the
   fresh classes counted at zero before (`l1_eq`).
5. **The bound a face reads** (`freshShare_le_of_le`, `freshShare_le_of_cMin`, `price_le_of_cMin`): where every standing
   logit is at least `m`, `q ≤ F·2^c / (A·2^m + F·2^c)`; at a face whose standing logits are at least the fresh logit,
   `q ≤ F / (A + F)` and the price is at most `log₂(1 + F/A)`. A standing logit `⟨E(a), y⟩ + c_a` is at least `c_min`
   where its plain face `⟨E(a), y⟩` is at least zero (`logit_ge_cMin`); elsewhere the price stands as item 2 gives it,
   with no bound in `F` and `A` alone.

**§2. The loud face's return is the adjoint of its forward** (#826; atlas `tower.face-loud-sharpness`;
`Constitution::loud_beta`, `loud_return`, `tied_sharp`, `Declaration::loud`). At an open site the face is
`z(a) = β v_a + c_a` (`loudFace`), `v_a` the plain face, with `β = 1 + Σ_ℓ κ_ℓ λ_ℓ + b` (`sharpness`; the engine's
`2^16 + release(Σ κ_ℓ λ_ℓ, 16) + b` on `2^(−16)`), `λ_ℓ = log₂ s_ℓ` (`loudness`), `s_ℓ` lane `ℓ`'s power, the root mean
square of its `W` coordinates (`scale`, as `ratio_to_power` reads it), and `r̂_i = x_i / s_ℓ` its chart (`chart`). The
power is read in the units the chart divides by (the engine's integer scale): a change of unit adds a constant to every
`λ_ℓ` (item 10), which moves `∂z/∂κ_ℓ` and neither `∂z/∂b` nor the radial part.

6. **The code's derivative along any motion of the logits** (`hasDerivAt_code`): `Σ_a (p(a) − [a = t]) ż_a`, the
   covector `p − q` with no factor `ln 2` in base two.
7. **The face's derivatives** (`hasDerivAt_face_b`, `hasDerivAt_face_kappa`, `hasDerivAt_face_loudness`):
   `∂z(a)/∂b = v_a`, `∂z(a)/∂κ_ℓ = v_a λ_ℓ = v_a log₂ s_ℓ`, `∂z(a)/∂λ_ℓ = v_a κ_ℓ`.
8. **The code's**, with `δβ = Σ_a (p(a) − [a = t]) v_a` (`dBeta`, the engine's `Σ_a δz_a v_a`): `δb = δβ`,
   `δκ_ℓ = δβ λ_ℓ`, `δλ_ℓ = δβ κ_ℓ` (`hasDerivAt_code_b`, `hasDerivAt_code_kappa`, `hasDerivAt_code_loudness`).
9. **The radial part** (`hasDerivAt_loudness`, `hasDerivAt_face_radial`, `hasDerivAt_code_radial`):
   `∂λ_ℓ/∂x_i = r̂_i / (W s_ℓ ln 2)` on lane `ℓ`, so with the plain faces `v` held the code's derivative along a motion
   `ẋ` of the lanes is `Σ_ℓ Σ_i δx_(ℓ,i) ẋ_(ℓ,i)` with `δx_(ℓ,i) = δλ_ℓ r̂_i / (W s_ℓ ln 2)` (`radial`), the engine's
   `radial`.
10. **The ray carries the loudness alone** (`chart_smul`, `loudness_smul`, `radial_eq_smul`): scaling a lane by `c > 0`
    leaves its chart and adds `log₂ c` to its loudness, and the radial covector is a multiple of the lane itself. The
    chart's own adjoint (`lane_adjoint`) keeps the part off the ray; item 9 is the part along it.

**§3. At the grain** (`grain_flat`, `grain_not_smooth`, `central_difference_near`). A release is a step, so the box's
"the derivative of the code at the grain" is false as written: the grain's `κ ↦ round(κ λ)`, the release of `β`'s
`κ`-term, has derivative zero at `κ = 0` (the founding) for every `λ`, and for `λ ≠ 0` the smooth derivative `λ` is not
its derivative. What holds is item 8 read at the grain's representative, and a central difference of step `h` grains
of that term stands within `1/(2h)` of `λ`, the kind of agreement #826's central differences read.

Not claimed. A paced head's blank clock `κ_h = 1 + Σ_a p(a) c_h[a]` reads its own face, so a fresh class moves it too: a
second route by which a founding moves a standing face, not modelled here. Item 9 holds the plain faces `v`, so the
chart's own route (the lift `R r̂ + b_R` into `v`) is not in it; the releases of the realization beyond §3's term are
not modelled; the Rust owners and the host's 219 probes are not tied to these statements.

The computational object is the helical pair interaction: a face is a receiver's reading of the pair contacts' current,
and the loud face reads its site's own power as the pump's inverse temperature (atlas
`parametron.pump-inverse-temperature`). Of the winding guide's six general objects this touches the faces and placement
(a face's shares, its sharpness, the covector at a site); the helix, pair, cell holonomy, tube and tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.LetterPriceAndLoudReturn

open Filter Topology

variable {α : Type*} [Fintype α]

/-! ## 0. The base-two face -/

/-- [definition] The face's mass, `Σ_a 2^(z_a)`. -/
noncomputable def mass (z : α → ℝ) : ℝ := ∑ a, (2 : ℝ) ^ z a

/-- [definition] A class's share at temperature one in base two, `p(a) = 2^(z_a) / Σ_b 2^(z_b)`. -/
noncomputable def share (z : α → ℝ) (a : α) : ℝ := (2 : ℝ) ^ z a / mass z

/-- [definition] A class's code, `−log₂ p(a)`. -/
noncomputable def code (z : α → ℝ) (a : α) : ℝ := -Real.logb 2 (share z a)

theorem rpow_two_pos (x : ℝ) : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos two_pos x

theorem mass_pos [Nonempty α] (z : α → ℝ) : 0 < mass z :=
  Finset.sum_pos (fun a _ => rpow_two_pos (z a)) Finset.univ_nonempty

theorem share_pos [Nonempty α] (z : α → ℝ) (a : α) : 0 < share z a :=
  div_pos (rpow_two_pos _) (mass_pos z)

theorem share_le_one (z : α → ℝ) (a : α) : share z a ≤ 1 := by
  have : Nonempty α := ⟨a⟩
  rw [share, div_le_one (mass_pos z)]
  exact Finset.single_le_sum (fun b _ => (rpow_two_pos (z b)).le) (Finset.mem_univ a)

theorem sum_share [Nonempty α] (z : α → ℝ) : ∑ a, share z a = 1 := by
  rw [show ∑ a, share z a = mass z / mass z by simp only [share, mass, Finset.sum_div]]
  exact div_self (mass_pos z).ne'

/-- The code is the logarithm of the mass less the logit. -/
theorem code_eq (z : α → ℝ) (a : α) : code z a = Real.logb 2 (mass z) - z a := by
  have : Nonempty α := ⟨a⟩
  rw [code, share, Real.logb_div (rpow_two_pos _).ne' (mass_pos z).ne', Real.logb_rpow two_pos (by norm_num)]
  ring

/-! ## 1. A letter founded at the least class bias -/

/-- [definition] The least class bias the constitution holds, `c_min = min_(b<A) c_b`. -/
noncomputable def cMin [Nonempty α] (cb : α → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty cb

theorem cMin_le [Nonempty α] (cb : α → ℝ) (a : α) : cMin cb ≤ cb a :=
  Finset.inf'_le _ (Finset.mem_univ a)

/-- A fresh class's rows stand at zero, so its logit `⟨E(f), y⟩ + c_f` is its class bias. -/
theorem fresh_logit {D : Type*} [Fintype D] (y : D → ℝ) (c : ℝ) : ∑ i, (0 : D → ℝ) i * y i + c = c := by
  simp

/-- A standing logit whose plain face is at least zero is at least the least class bias. -/
theorem logit_ge_cMin [Nonempty α] (v cb : α → ℝ) (hv : ∀ a, 0 ≤ v a) (a : α) : cMin cb ≤ v a + cb a := by
  have := cMin_le cb a
  linarith [hv a]

/-- [definition] The grown face's logits: the standing ones beside `F` fresh classes at `c`. -/
def grown (z : α → ℝ) (F : ℕ) (c : ℝ) : α ⊕ Fin F → ℝ := Sum.elim z fun _ => c

/-- [definition] The price, `log₂(1 + F·2^c / Σ_a 2^(z_a))`. -/
noncomputable def price (z : α → ℝ) (F : ℕ) (c : ℝ) : ℝ := Real.logb 2 (1 + F * (2 : ℝ) ^ c / mass z)

/-- [definition] The fresh classes' joint share on the grown face. -/
noncomputable def freshShare (z : α → ℝ) (F : ℕ) (c : ℝ) : ℝ := ∑ f : Fin F, share (grown z F c) (Sum.inr f)

theorem freshMass_nonneg (F : ℕ) (c : ℝ) : 0 ≤ (F : ℝ) * (2 : ℝ) ^ c :=
  mul_nonneg (Nat.cast_nonneg F) (rpow_two_pos c).le

/-- [proved-derived; formal-checked] The grown face's mass is the standing mass and `F·2^c`. -/
theorem mass_grown (z : α → ℝ) (F : ℕ) (c : ℝ) : mass (grown z F c) = mass z + F * (2 : ℝ) ^ c := by
  simp [mass, grown, Fintype.sum_sum_type]

theorem share_grown_inl (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    share (grown z F c) (Sum.inl t) = (2 : ℝ) ^ z t / (mass z + F * (2 : ℝ) ^ c) := by
  rw [share, mass_grown]
  rfl

/-- [proved-derived; formal-checked] **The price**: every standing class's code rises by
`log₂(1 + F·2^c / Σ_a 2^(z_a))`. -/
theorem price_eq [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    code (grown z F c) (Sum.inl t) - code z t = price z F c := by
  have hS := mass_pos z
  have hSM : 0 < mass z + F * (2 : ℝ) ^ c := by linarith [freshMass_nonneg F c]
  have ha := rpow_two_pos (z t)
  rw [code, code, share_grown_inl, share, price, Real.logb_div ha.ne' hSM.ne', Real.logb_div ha.ne' hS.ne',
    show 1 + F * (2 : ℝ) ^ c / mass z = (mass z + F * (2 : ℝ) ^ c) / mass z by rw [add_div, div_self hS.ne'],
    Real.logb_div hSM.ne' hS.ne']
  ring

theorem price_nonneg [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) : 0 ≤ price z F c :=
  Real.logb_nonneg one_lt_two (le_add_of_nonneg_right (div_nonneg (freshMass_nonneg F c) (mass_pos z).le))

/-- The price is at most the fresh mass over the standing mass, over `ln 2`. -/
theorem price_le [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) :
    price z F c ≤ F * (2 : ℝ) ^ c / mass z / Real.log 2 := by
  have hx : 0 ≤ F * (2 : ℝ) ^ c / mass z := div_nonneg (freshMass_nonneg F c) (mass_pos z).le
  rw [price, Real.logb]
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + F * 2 ^ c / mass z by linarith)
  linarith

/-- [proved-derived; formal-checked] The fresh classes' joint share is `F·2^c / (Σ_a 2^(z_a) + F·2^c)`. -/
theorem freshShare_eq (z : α → ℝ) (F : ℕ) (c : ℝ) :
    freshShare z F c = F * (2 : ℝ) ^ c / (mass z + F * (2 : ℝ) ^ c) := by
  have h : ∀ f : Fin F, share (grown z F c) (Sum.inr f) = (2 : ℝ) ^ c / (mass z + F * (2 : ℝ) ^ c) := fun f => by
    rw [share, mass_grown]
    rfl
  simp only [freshShare, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem freshShare_nonneg (z : α → ℝ) (F : ℕ) (c : ℝ) : 0 ≤ freshShare z F c :=
  Finset.sum_nonneg fun _ _ => div_nonneg (rpow_two_pos _).le (Finset.sum_nonneg fun _ _ => (rpow_two_pos _).le)

theorem rpow_neg_price [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) :
    (2 : ℝ) ^ (-price z F c) = mass z / (mass z + F * (2 : ℝ) ^ c) := by
  have hS := mass_pos z
  have hx : 0 < 1 + F * (2 : ℝ) ^ c / mass z := by
    have := div_nonneg (freshMass_nonneg F c) hS.le
    linarith
  rw [Real.rpow_neg zero_le_two, price, Real.rpow_logb two_pos (by norm_num) hx]
  field_simp

/-- `1 − q = 2^(−price)`. -/
theorem one_sub_freshShare [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) :
    1 - freshShare z F c = (2 : ℝ) ^ (-price z F c) := by
  have hSM : 0 < mass z + F * (2 : ℝ) ^ c := by linarith [freshMass_nonneg F c, mass_pos z]
  rw [rpow_neg_price, freshShare_eq]
  field_simp
  ring

/-- [proved-derived; formal-checked] A standing share after the founding is its share before times `1 − q`. -/
theorem share_grown [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    share (grown z F c) (Sum.inl t) = share z t * (1 - freshShare z F c) := by
  have hS := mass_pos z
  have hSM : 0 < mass z + F * (2 : ℝ) ^ c := by linarith [freshMass_nonneg F c]
  rw [share_grown_inl, share, freshShare_eq]
  field_simp
  ring

/-- A standing share after the founding is its share before times `2^(−price)`. -/
theorem share_grown_eq_price [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    share (grown z F c) (Sum.inl t) = share z t * (2 : ℝ) ^ (-price z F c) := by
  rw [share_grown, one_sub_freshShare]

/-- A standing share falls by `p(t)·q`. -/
theorem share_drop [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    share z t - share (grown z F c) (Sum.inl t) = share z t * freshShare z F c := by
  rw [share_grown]
  ring

/-- [proved-derived; formal-checked] **The absolute form**: each standing share falls by at least zero and at most the
fresh classes' joint mass. -/
theorem share_drop_le [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    0 ≤ share z t - share (grown z F c) (Sum.inl t) ∧
      share z t - share (grown z F c) (Sum.inl t) ≤ freshShare z F c := by
  have hq := freshShare_nonneg z F c
  rw [share_drop]
  exact ⟨mul_nonneg (share_pos z t).le hq, mul_le_of_le_one_left hq (share_le_one z t)⟩

/-- [proved-derived; formal-checked] **The relative form**: each standing share falls by the fraction `q`. -/
theorem relative_drop [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (t : α) :
    (share z t - share (grown z F c) (Sum.inl t)) / share z t = freshShare z F c := by
  rw [share_drop, mul_div_cancel_left₀ _ (share_pos z t).ne']

/-- The standing classes lose `q` between them. -/
theorem standing_loss [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) :
    ∑ t, (share z t - share (grown z F c) (Sum.inl t)) = freshShare z F c := by
  simp only [share_drop]
  rw [← Finset.sum_mul, sum_share, one_mul]

/-- The two faces stand `2q` apart in the sum of absolute differences, the fresh classes at zero before. -/
theorem l1_eq [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) :
    ∑ b, |share (grown z F c) b - Sum.elim (share z) (fun _ => 0) b| = 2 * freshShare z F c := by
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, sub_zero]
  have h1 : ∀ t, |share (grown z F c) (Sum.inl t) - share z t|
      = share z t - share (grown z F c) (Sum.inl t) := fun t => by
    rw [abs_sub_comm]
    exact abs_of_nonneg (share_drop_le z F c t).1
  have h2 : ∀ f : Fin F, |share (grown z F c) (Sum.inr f)| = share (grown z F c) (Sum.inr f) :=
    fun f => abs_of_nonneg (share_pos _ _).le
  have h3 : ∑ f : Fin F, share (grown z F c) (Sum.inr f) = freshShare z F c := rfl
  simp only [h1, h2, standing_loss, h3]
  ring

theorem mass_ge (z : α → ℝ) (m : ℝ) (hm : ∀ a, m ≤ z a) : Fintype.card α * (2 : ℝ) ^ m ≤ mass z := by
  rw [mass, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
  exact Finset.sum_le_sum fun a _ => Real.rpow_le_rpow_of_exponent_le one_le_two (hm a)

/-- [proved-derived; formal-checked] **The bound a face reads**: where every standing logit is at least `m`,
`q ≤ F·2^c / (A·2^m + F·2^c)`. -/
theorem freshShare_le_of_le [Nonempty α] (z : α → ℝ) (F : ℕ) (c m : ℝ) (hm : ∀ a, m ≤ z a) :
    freshShare z F c ≤ F * (2 : ℝ) ^ c / (Fintype.card α * (2 : ℝ) ^ m + F * (2 : ℝ) ^ c) := by
  have hA : (0 : ℝ) < Fintype.card α * (2 : ℝ) ^ m :=
    mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (rpow_two_pos m)
  have hM := freshMass_nonneg F c
  have hge := mass_ge z m hm
  rw [freshShare_eq, div_le_div_iff₀ (by linarith) (by linarith)]
  exact mul_le_mul_of_nonneg_left (by linarith) hM

/-- At a face whose standing logits are at least the fresh logit, `q ≤ F / (A + F)`. -/
theorem freshShare_le_of_cMin [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (hc : ∀ a, c ≤ z a) :
    freshShare z F c ≤ F / (Fintype.card α + F) := by
  refine (freshShare_le_of_le z F c c hc).trans_eq ?_
  rw [show (Fintype.card α : ℝ) * 2 ^ c + F * 2 ^ c = (Fintype.card α + F) * 2 ^ c by ring,
    mul_div_mul_right _ _ (rpow_two_pos c).ne']

/-- At a face whose standing logits are at least the fresh logit, the price is at most `log₂(1 + F/A)`. -/
theorem price_le_of_cMin [Nonempty α] (z : α → ℝ) (F : ℕ) (c : ℝ) (hc : ∀ a, c ≤ z a) :
    price z F c ≤ Real.logb 2 (1 + F / Fintype.card α) := by
  have hS := mass_pos z
  have hA : (0 : ℝ) < Fintype.card α := Nat.cast_pos.mpr Fintype.card_pos
  have hge := mass_ge z c hc
  have hle : F * (2 : ℝ) ^ c / mass z ≤ F / Fintype.card α := by
    rw [div_le_div_iff₀ hS hA]
    calc (F : ℝ) * 2 ^ c * Fintype.card α = F * (Fintype.card α * 2 ^ c) := by ring
      _ ≤ F * mass z := mul_le_mul_of_nonneg_left hge (Nat.cast_nonneg F)
  have h0 : 0 < 1 + F * (2 : ℝ) ^ c / mass z := by
    have := div_nonneg (freshMass_nonneg F c) hS.le
    linarith
  exact Real.logb_le_logb_of_le one_lt_two h0 (by linarith)

/-! ## 2. The loud face's return -/

section Loud

variable {ι : Type*} [Fintype ι] [DecidableEq α]

/-- [definition] The sharpness a site's loudness sets, `β = 1 + Σ_ℓ κ_ℓ λ_ℓ + b`. -/
def sharpness (κ lam : ι → ℝ) (b : ℝ) : ℝ := 1 + ∑ l, κ l * lam l + b

/-- [definition] The loud face, `z(a) = β v_a + c_a`. -/
def loudFace (β : ℝ) (v c : α → ℝ) : α → ℝ := fun a => β * v a + c a

/-- [definition] The code's covector on the sharpness, `δβ = Σ_a (p(a) − [a = t]) v_a`. -/
noncomputable def dBeta (z v : α → ℝ) (t : α) : ℝ := ∑ a, (share z a - if a = t then 1 else 0) * v a

/-- [proved-standard; formal-checked] **The code's derivative along any motion of the logits**:
`Σ_a (p(a) − [a = t]) ż_a`. -/
theorem hasDerivAt_code (Z : ℝ → α → ℝ) (Z' : α → ℝ) (s₀ : ℝ) (t : α)
    (hZ : ∀ a, HasDerivAt (fun s => Z s a) (Z' a) s₀) :
    HasDerivAt (fun s => code (Z s) t) (∑ a, (share (Z s₀) a - if a = t then 1 else 0) * Z' a) s₀ := by
  have : Nonempty α := ⟨t⟩
  have hfun : (fun s => code (Z s) t) = fun s => Real.log (∑ a, (2 : ℝ) ^ Z s a) / Real.log 2 - Z s t :=
    funext fun s => by rw [code_eq]; rfl
  rw [hfun]
  have hm : HasDerivAt (fun s => ∑ a, (2 : ℝ) ^ Z s a) (∑ a, Real.log 2 * Z' a * (2 : ℝ) ^ Z s₀ a) s₀ :=
    HasDerivAt.fun_sum fun a _ => (hZ a).const_rpow two_pos
  have hl := ((hm.log (mass_pos (Z s₀)).ne').div_const (Real.log 2)).sub (hZ t)
  refine hl.congr_deriv ?_
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hS : (∑ a, (2 : ℝ) ^ Z s₀ a) ≠ 0 := (mass_pos (Z s₀)).ne'
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, share, mass]
  congr 1
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

theorem sharpness_line_kappa [DecidableEq ι] (κ lam : ι → ℝ) (b s : ℝ) (l : ι) :
    sharpness (κ + s • Pi.single l 1) lam b = sharpness κ lam b + s * lam l := by
  simp only [sharpness, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

theorem sharpness_line_loudness [DecidableEq ι] (κ lam : ι → ℝ) (b s : ℝ) (l : ι) :
    sharpness κ (lam + s • Pi.single l 1) b = sharpness κ lam b + s * κ l := by
  simp only [sharpness, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

omit [Fintype α] [DecidableEq α] in
/-- [proved-derived; formal-checked] `∂z(a)/∂b = v_a`. -/
theorem hasDerivAt_face_b (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (a : α) :
    HasDerivAt (fun s => loudFace (sharpness κ lam (b + s)) v c a) (v a) 0 := by
  have h : (fun s => loudFace (sharpness κ lam (b + s)) v c a)
      = fun s => loudFace (sharpness κ lam b) v c a + s * v a := by
    funext s
    simp only [loudFace, sharpness]
    ring
  rw [h]
  exact (hasDerivAt_mul_const (v a)).const_add _

omit [Fintype α] [DecidableEq α] in
/-- [proved-derived; formal-checked] `∂z(a)/∂κ_ℓ = v_a λ_ℓ`, which is `v_a log₂ s_ℓ` at `λ = loudness`. -/
theorem hasDerivAt_face_kappa [DecidableEq ι] (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (l : ι) (a : α) :
    HasDerivAt (fun s : ℝ => loudFace (sharpness (κ + s • Pi.single l 1) lam b) v c a) (v a * lam l) 0 := by
  have h : (fun s : ℝ => loudFace (sharpness (κ + s • Pi.single l 1) lam b) v c a)
      = fun s => loudFace (sharpness κ lam b) v c a + s * (v a * lam l) := by
    funext s
    simp only [loudFace, sharpness_line_kappa]
    ring
  rw [h]
  exact (hasDerivAt_mul_const (v a * lam l)).const_add _

omit [Fintype α] [DecidableEq α] in
/-- `∂z(a)/∂λ_ℓ = v_a κ_ℓ`. -/
theorem hasDerivAt_face_loudness [DecidableEq ι] (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (l : ι) (a : α) :
    HasDerivAt (fun s : ℝ => loudFace (sharpness κ (lam + s • Pi.single l 1) b) v c a) (v a * κ l) 0 := by
  have h : (fun s : ℝ => loudFace (sharpness κ (lam + s • Pi.single l 1) b) v c a)
      = fun s => loudFace (sharpness κ lam b) v c a + s * (v a * κ l) := by
    funext s
    simp only [loudFace, sharpness_line_loudness]
    ring
  rw [h]
  exact (hasDerivAt_mul_const (v a * κ l)).const_add _

/-- [proved-derived; formal-checked] **The code's covector of `b`** is `δβ`. -/
theorem hasDerivAt_code_b (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (t : α) :
    HasDerivAt (fun s => code (loudFace (sharpness κ lam (b + s)) v c) t)
      (dBeta (loudFace (sharpness κ lam b) v c) v t) 0 :=
  (hasDerivAt_code (fun s => loudFace (sharpness κ lam (b + s)) v c) v 0 t
    fun a => hasDerivAt_face_b κ lam b v c a).congr_deriv (by simp only [add_zero, dBeta])

/-- [proved-derived; formal-checked] **The code's covector of `κ_ℓ`** is `δβ λ_ℓ`. -/
theorem hasDerivAt_code_kappa [DecidableEq ι] (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (l : ι) (t : α) :
    HasDerivAt (fun s : ℝ => code (loudFace (sharpness (κ + s • Pi.single l 1) lam b) v c) t)
      (dBeta (loudFace (sharpness κ lam b) v c) v t * lam l) 0 := by
  refine (hasDerivAt_code (fun s : ℝ => loudFace (sharpness (κ + s • Pi.single l 1) lam b) v c)
    (fun a => v a * lam l) 0 t fun a => hasDerivAt_face_kappa κ lam b v c l a).congr_deriv ?_
  simp only [zero_smul, add_zero, dBeta, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The code's covector of `λ_ℓ` is `δβ κ_ℓ`. -/
theorem hasDerivAt_code_loudness [DecidableEq ι] (κ lam : ι → ℝ) (b : ℝ) (v c : α → ℝ) (l : ι) (t : α) :
    HasDerivAt (fun s : ℝ => code (loudFace (sharpness κ (lam + s • Pi.single l 1) b) v c) t)
      (dBeta (loudFace (sharpness κ lam b) v c) v t * κ l) 0 := by
  refine (hasDerivAt_code (fun s : ℝ => loudFace (sharpness κ (lam + s • Pi.single l 1) b) v c)
    (fun a => v a * κ l) 0 t fun a => hasDerivAt_face_loudness κ lam b v c l a).congr_deriv ?_
  simp only [zero_smul, add_zero, dBeta, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-! ### The lanes' powers -/

variable {W : ℕ}

/-- [definition] A lane's mean square, `(Σ_i x_i²) / W`. -/
noncomputable def power (u : Fin W → ℝ) : ℝ := (∑ i, u i ^ 2) / W

/-- [definition] A lane's power read as its root mean square `s`, the scale its chart divides by. -/
noncomputable def scale (u : Fin W → ℝ) : ℝ := Real.sqrt (power u)

/-- [definition] A lane's chart, `r̂_i = x_i / s`. -/
noncomputable def chart (u : Fin W → ℝ) (i : Fin W) : ℝ := u i / scale u

/-- [definition] A lane's loudness, `λ = log₂ s`. -/
noncomputable def loudness (u : Fin W → ℝ) : ℝ := Real.logb 2 (scale u)

/-- [definition] The radial covector, `δx_i = δλ r̂_i / (W s ln 2)`. -/
noncomputable def radial (dlam : ℝ) (u : Fin W → ℝ) (i : Fin W) : ℝ := dlam * chart u i / (W * scale u * Real.log 2)

/-- [proved-derived; formal-checked] **The loudness's derivative**: along a motion `ẋ` of a lane of positive power,
`dλ = Σ_i r̂_i ẋ_i / (W s ln 2)`. -/
theorem hasDerivAt_loudness (u du : Fin W → ℝ) (h : 0 < power u) :
    HasDerivAt (fun s : ℝ => loudness (u + s • du)) (∑ i, chart u i * du i / (W * scale u * Real.log 2)) 0 := by
  have hW : (W : ℝ) ≠ 0 := by
    intro hW
    simp [power, hW] at h
  have hfun : (fun s : ℝ => loudness (u + s • du))
      = fun s => Real.log ((∑ i, (u i + s * du i) ^ 2) / W) / (2 * Real.log 2) := by
    funext s
    simp only [loudness, scale, power, Real.logb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Real.log_sqrt (div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Nat.cast_nonneg W))]
    ring
  rw [hfun]
  have hsum : HasDerivAt (fun s : ℝ => ∑ i, (u i + s * du i) ^ 2) (∑ i, 2 * u i * du i) 0 := by
    refine (HasDerivAt.fun_sum fun i _ => ((hasDerivAt_mul_const (du i)).const_add (u i)).pow 2).congr_deriv ?_
    exact Finset.sum_congr rfl fun i _ => by simp
  have hP : (∑ i, (u i + 0 * du i) ^ 2) / (W : ℝ) ≠ 0 := by
    simp only [zero_mul, add_zero]
    exact h.ne'
  refine (((hsum.div_const (W : ℝ)).log hP).div_const (2 * Real.log 2)).congr_deriv ?_
  have hs : scale u ^ 2 = power u := Real.sq_sqrt h.le
  have hs0 : scale u ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
  have hP' : (∑ i, (u i + 0 * du i) ^ 2) / (W : ℝ) = scale u ^ 2 := by
    rw [hs]
    simp only [zero_mul, add_zero]
    rfl
  rw [hP', show ∑ i, 2 * u i * du i = 2 * ∑ i, u i * du i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring,
    show ∑ i, chart u i * du i / (W * scale u * Real.log 2) = (∑ i, u i * du i) / (W * scale u ^ 2 * Real.log 2) by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by simp only [chart]; field_simp]
  field_simp

omit [Fintype α] [DecidableEq α] in
/-- The face's derivative along a motion of the lanes, the plain faces held. -/
theorem hasDerivAt_face_radial (κ : ι → ℝ) (b : ℝ) (v c : α → ℝ) (x dx : ι → Fin W → ℝ)
    (h : ∀ l, 0 < power (x l)) (a : α) :
    HasDerivAt (fun s : ℝ => loudFace (sharpness κ (fun l => loudness (x l + s • dx l)) b) v c a)
      (v a * ∑ l, κ l * ∑ i, chart (x l) i * dx l i / (W * scale (x l) * Real.log 2)) 0 := by
  have hsum : HasDerivAt (fun s : ℝ => ∑ l, κ l * loudness (x l + s • dx l))
      (∑ l, κ l * ∑ i, chart (x l) i * dx l i / (W * scale (x l) * Real.log 2)) 0 :=
    HasDerivAt.fun_sum fun l _ => (hasDerivAt_loudness (x l) (dx l) (h l)).const_mul (κ l)
  exact ((((hsum.const_add 1).add_const b).mul_const (v a)).add_const (c a)).congr_deriv (mul_comm _ _)

/-- [proved-derived; formal-checked] **The radial part**: with the plain faces held, the code's derivative along a
motion `ẋ` of the lanes is `Σ_ℓ Σ_i δx_(ℓ,i) ẋ_(ℓ,i)`, `δx_(ℓ,i) = δλ_ℓ r̂_i / (W s_ℓ ln 2)`, `δλ_ℓ = δβ κ_ℓ`. -/
theorem hasDerivAt_code_radial (κ : ι → ℝ) (b : ℝ) (v c : α → ℝ) (t : α) (x dx : ι → Fin W → ℝ)
    (h : ∀ l, 0 < power (x l)) :
    HasDerivAt (fun s : ℝ => code (loudFace (sharpness κ (fun l => loudness (x l + s • dx l)) b) v c) t)
      (∑ l, ∑ i, radial (dBeta (loudFace (sharpness κ (fun l => loudness (x l)) b) v c) v t * κ l) (x l) i
        * dx l i) 0 := by
  set z₀ := loudFace (sharpness κ (fun l => loudness (x l)) b) v c
  set G : ι → ℝ := fun l => ∑ i, chart (x l) i * dx l i / (W * scale (x l) * Real.log 2)
  refine (hasDerivAt_code (fun s : ℝ => loudFace (sharpness κ (fun l => loudness (x l + s • dx l)) b) v c)
    (fun a => v a * ∑ l, κ l * G l) 0 t fun a => hasDerivAt_face_radial κ b v c x dx h a).congr_deriv ?_
  have e1 : ∀ S : ℝ, ∑ a, (share z₀ a - if a = t then 1 else 0) * (v a * S) = dBeta z₀ v t * S := by
    intro S
    rw [dBeta, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : ∀ l, ∑ i, radial (dBeta z₀ v t * κ l) (x l) i * dx l i = dBeta z₀ v t * (κ l * G l) := by
    intro l
    simp only [G, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by simp only [radial]; ring
  simp only [zero_smul, add_zero]
  rw [Finset.sum_congr rfl fun l _ => e2 l, ← Finset.mul_sum]
  exact e1 _

theorem power_smul (c : ℝ) (u : Fin W → ℝ) : power (c • u) = c ^ 2 * power u := by
  simp only [power, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  ring

theorem scale_smul {c : ℝ} (hc : 0 ≤ c) (u : Fin W → ℝ) : scale (c • u) = c * scale u := by
  rw [scale, power_smul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rfl

/-- **The ray leaves the chart**: scaling a lane by `c > 0` leaves its chart. -/
theorem chart_smul {c : ℝ} (hc : 0 < c) (u : Fin W → ℝ) : chart (c • u) = chart u := by
  funext i
  simp only [chart, scale_smul hc.le, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_mul_left _ _ hc.ne']

/-- **The ray moves the loudness**: scaling a lane of positive power by `c > 0` adds `log₂ c` to its loudness. -/
theorem loudness_smul {c : ℝ} (hc : 0 < c) (u : Fin W → ℝ) (h : 0 < power u) :
    loudness (c • u) = loudness u + Real.logb 2 c := by
  rw [loudness, scale_smul hc.le, Real.logb_mul hc.ne' (show scale u ≠ 0 from (Real.sqrt_pos.mpr h).ne'), loudness]
  ring

/-- The radial covector is a multiple of the lane itself: it lies along the ray. -/
theorem radial_eq_smul (dlam : ℝ) (u : Fin W → ℝ) :
    radial dlam u = (dlam / (W * scale u ^ 2 * Real.log 2)) • u := by
  funext i
  simp only [radial, chart, Pi.smul_apply, smul_eq_mul]
  ring

end Loud

/-! ## 3. At the grain -/

theorem round_eq_zero_of_abs_lt {x : ℝ} (hx : |x| < 1 / 2) : round x = 0 := by
  rw [round_eq_zero_iff]
  constructor <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]

/-- [proved-standard; formal-checked] **The grain is flat at the founding**: `κ ↦ round(κ λ)` has derivative zero at
`κ = 0`, for every `λ`. -/
theorem grain_flat (lam : ℝ) : HasDerivAt (fun κ : ℝ => (round (κ * lam) : ℝ)) 0 0 := by
  have hev : ∀ᶠ κ in 𝓝 (0 : ℝ), |κ * lam| < 1 / 2 := by
    have hc : ContinuousAt (fun κ : ℝ => |κ * lam|) 0 := by fun_prop
    exact hc.eventually_lt continuousAt_const (by norm_num)
  refine (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq ?_
  filter_upwards [hev] with κ hκ
  simp [round_eq_zero_of_abs_lt hκ]

/-- [proved-standard; formal-checked] **The counterexample**: for `λ ≠ 0` the smooth derivative `λ` is not the grain's
derivative at the founding. -/
theorem grain_not_smooth {lam : ℝ} (hlam : lam ≠ 0) :
    ¬ HasDerivAt (fun κ : ℝ => (round (κ * lam) : ℝ)) lam 0 :=
  fun h => hlam (h.unique (grain_flat lam))

/-- [proved-standard; formal-checked] **What a central difference reads**: at any `κ`, a central difference of the grain
term over a step `h > 0` stands within `1/(2h)` of the smooth derivative `λ`. -/
theorem central_difference_near (κ lam h : ℝ) (hh : 0 < h) :
    |((round ((κ + h) * lam) : ℝ) - round ((κ - h) * lam)) / (2 * h) - lam| ≤ 1 / (2 * h) := by
  have h1 := abs_sub_round ((κ + h) * lam)
  have h2 := abs_sub_round ((κ - h) * lam)
  have key : ((round ((κ + h) * lam) : ℝ) - round ((κ - h) * lam)) / (2 * h) - lam
      = (((round ((κ + h) * lam) : ℝ) - (κ + h) * lam) - ((round ((κ - h) * lam) : ℝ) - (κ - h) * lam))
        / (2 * h) := by
    field_simp
    ring
  rw [key, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * h)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [abs_sub_comm] at h1 h2
  calc |((round ((κ + h) * lam) : ℝ) - (κ + h) * lam) - ((round ((κ - h) * lam) : ℝ) - (κ - h) * lam)|
      ≤ |(round ((κ + h) * lam) : ℝ) - (κ + h) * lam| + |(round ((κ - h) * lam) : ℝ) - (κ - h) * lam| :=
        abs_sub _ _
    _ ≤ 1 := by linarith

end Holonics.HNN.LetterPriceAndLoudReturn

import HolonicsResearch.Mathematics.OnePlaneRing
import HolonicsResearch.Geometry.ScrewTorsion
import Mathlib.Analysis.Complex.Isometry

/-!
# No bank of uncoupled planes holds a ring where the base turns by more than a half-turn

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§7(b)) reads a diagonal level of the tower as a bank of uncoupled planes, each moved by its own
symbol-keyed maps, and owes to #410 the bound: such a bank holds a prime ring `ℤ/q` as faces that
move with the digits only where the base is `±1`, so never ring 7, 13, 37, 41 or 101 in base ten.

[proved-derived; formal-checked] What is proved.

1. **The bank by colours** (`uncoupled_bank`, `no_uncoupled_bank_ten`, `ten_turns_too_far`). Let a
   family of planes `ℂ^ι` carry the residues of a prime ring as distinct points, with the digits `0`
   and `1` acting on each plane by a real-affine map of that plane alone. Then `b ≡ ±1 (mod q)`. Each
   plane's coordinate is moved by real-affine digits, so by `OnePlaneRing.plane_modes` a colour
   `k ≠ 0` present in it is carried by `b⁻¹` to `±k`; when `b ≢ ±1` no plane has a colour off `0`,
   every plane is constant, and the points are not distinct.
2. **The group's side** (`unitPart`, `translations`, `mem_translations`, `quotient_translations`,
   `index_translations`, `abelian_normal_eq_translations`). The digit group `ℤ/q ⋊ ⟨b⟩`
   (`OnePlaneRing.affineGroup`) has the translations as its only nontrivial abelian normal subgroup,
   because the action is faithful, and the quotient by them is the cyclic group `⟨b⟩` of order
   `ord_q(b)`.
3. **The dihedral bound** (`HasTurnCore`, `HasTurnCore.of_injective`, `HasTurnCore.of_surjective`,
   `HasTurnCore.pi`, `isometry_turnCore`, `three_le_orderOf_iff`, `affine_not_turnCore`,
   `not_section_of_planes`). A group has a turn core when an abelian normal subgroup holds every
   square. The plane's linear isometries `O(2)` have one, the turns: two reflections compose to a
   turn and turns commute (`Geometry/ScrewTorsion.plane_reflections_compose`,
   `plane_turns_commute`). Turn cores pass to subgroups, quotients and products, so every section
   of a product of subgroups of `O(2)` has one. `ℤ/q ⋊ ⟨b⟩` with `b² ≠ 1`, that is
   `ord_q(b) ≥ 3`, has none, so it is never such a section.

Not proved here: the record's step from a bank of planes whose digits permute each plane's reachable
states to a section of a product of finite subgroups of `O(2)` (an averaged inner product per
plane). Item 1 replaces it by the colours, for real-affine digits; item 3 is the group statement it
feeds.

Consumers: the atlas row `radix.uncoupled-bank-dihedral`.
-/

open Complex ZMod
open scoped ComplexConjugate

namespace Holonics.Mathematics.UncoupledBank

open Holonics.Mathematics.OnePlaneRing

section Bank

variable {q : ℕ} [Fact q.Prime]

theorem two_ne_zero_of_ne_two (hq : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  rcases (Nat.dvd_prime Nat.prime_two).mp h' with h1 | h1
  · exact (Fact.out : q.Prime).one_lt.ne' h1
  · exact hq h1

/-- [proved-derived; formal-checked] **One plane of the bank.** A plane whose points `p(x)` (not
necessarily distinct) are moved by real-affine digits `0` and `1` repeats with period `1`, so is
constant, unless `b ≡ ±1 (mod q)`. -/
theorem bank_plane_const (b : (ZMod q)ˣ) (hb : (b : ZMod q) ≠ 1 ∧ (b : ZMod q) ≠ -1)
    (p : ZMod q → ℂ)
    (hA : ∀ e : ZMod q, e = 0 ∨ e = 1 →
      ∃ α β γ : ℂ, ∀ x, p ((b : ZMod q) * x + e) = α * p x + β * conj (p x) + γ)
    (x : ZMod q) : p (x + 1) = p x := by
  have hq2 : q ≠ 2 := by
    rintro rfl
    apply hb.1
    have hne : (b : ZMod 2) ≠ 0 := b.ne_zero
    generalize (b : ZMod 2) = y at hne ⊢
    fin_cases y
    · exact absurd rfl hne
    · rfl
  obtain ⟨_, _, hmodes⟩ := plane_modes b p hA
  refine period p 1 (fun k hk => ?_) x
  by_contra hk1
  rw [mul_one] at hk1
  have hkk : k ≠ -k := by
    intro h
    have : (2 : ZMod q) * k = 0 := by rw [two_mul]; nth_rewrite 2 [h]; exact add_neg_cancel k
    rcases mul_eq_zero.mp this with h2 | h2
    · exact two_ne_zero_of_ne_two hq2 h2
    · exact hk1 h2
  obtain ⟨_, hck⟩ := hmodes k hk1 hkk hk
  have hbc : (b : ZMod q) * b⁻¹.val = 1 := b.mul_inv
  rcases hck with h | h
  · have hc : b⁻¹.val = 1 := mul_right_cancel₀ hk1 (by rw [h, one_mul])
    apply hb.1
    rw [hc, mul_one] at hbc
    exact hbc
  · have hc : b⁻¹.val = -1 := mul_right_cancel₀ hk1 (by rw [h, neg_one_mul])
    apply hb.2
    rw [hc, mul_neg_one] at hbc
    exact neg_eq_iff_eq_neg.mp hbc

/-- [proved-derived; formal-checked] **No uncoupled bank holds the ring unless `b ≡ ±1`.** If the
planes `ℂ^ι` carry the prime ring `ℤ/q` as distinct points and each digit `0`, `1` acts on each plane
by a real-affine map of that plane alone, then `b ≡ 1` or `b ≡ −1 (mod q)`. -/
theorem uncoupled_bank (b : (ZMod q)ˣ) {ι : Type*} (p : ZMod q → ι → ℂ)
    (hp : Function.Injective p)
    (hA : ∀ i, ∀ e : ZMod q, e = 0 ∨ e = 1 →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, ∀ x, p ((b : ZMod q) * x + e) i = A (p x i)) :
    (b : ZMod q) = 1 ∨ (b : ZMod q) = -1 := by
  by_contra hb
  push Not at hb
  have hstep : ∀ x, p (x + 1) = p x := by
    intro x
    funext i
    refine bank_plane_const b hb (fun x => p x i) (fun e he => ?_) x
    obtain ⟨A, hA'⟩ := hA i e he
    obtain ⟨α, β, γ, hαβγ⟩ := affine_form A
    exact ⟨α, β, γ, fun x => by rw [hA', hαβγ]⟩
  have hconst : ∀ n : ℕ, p (n : ZMod q) = p 0 := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]
    | succ n ih => rw [Nat.cast_succ, hstep, ih]
  have h10 := hp (hconst 1)
  rw [Nat.cast_one] at h10
  exact one_ne_zero h10

/-- [proved-derived; formal-checked] **Base ten** (§7(b)): a prime ring coprime to ten on which
`10 ≢ ±1` is held by no bank of uncoupled planes. -/
theorem no_uncoupled_bank_ten (hcop : Nat.Coprime 10 q) (h1 : (10 : ZMod q) ≠ 1)
    (hm1 : (10 : ZMod q) ≠ -1) {ι : Type*} (p : ZMod q → ι → ℂ) (hp : Function.Injective p)
    (hA : ∀ i, ∀ e : ZMod q, e = 0 ∨ e = 1 →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, ∀ x, p (10 * x + e) i = A (p x i)) : False := by
  have hcoe : ((ZMod.unitOfCoprime 10 hcop : (ZMod q)ˣ) : ZMod q) = 10 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
  rcases uncoupled_bank (ZMod.unitOfCoprime 10 hcop) p hp (by rw [hcoe]; exact hA) with h | h
  · exact h1 (hcoe ▸ h)
  · exact hm1 (hcoe ▸ h)

/-- [proved-standard; formal-checked] In base ten `10 ≢ ±1` on the rings 7, 13, 37, 41 and 101. -/
theorem ten_turns_too_far :
    ((10 : ZMod 7) ≠ 1 ∧ (10 : ZMod 7) ≠ -1) ∧ ((10 : ZMod 13) ≠ 1 ∧ (10 : ZMod 13) ≠ -1) ∧
    ((10 : ZMod 37) ≠ 1 ∧ (10 : ZMod 37) ≠ -1) ∧ ((10 : ZMod 41) ≠ 1 ∧ (10 : ZMod 41) ≠ -1) ∧
    ((10 : ZMod 101) ≠ 1 ∧ (10 : ZMod 101) ≠ -1) := by
  decide

end Bank

section Group

variable {q : ℕ} [Fact q.Prime]

theorem mem_affineGroup (b : (ZMod q)ˣ) (σ : Equiv.Perm (ZMod q)) :
    σ ∈ affineGroup b ↔ ∃ u ∈ Subgroup.zpowers b, ∃ t, σ = affinePerm u t := Iff.rfl

/-- The unit of a move `x ↦ u x + t` of the digit group. -/
noncomputable def unitOf (b : (ZMod q)ˣ) (σ : affineGroup b) : (ZMod q)ˣ :=
  Classical.choose ((mem_affineGroup b σ.val).mp σ.2)

theorem unitOf_mem (b : (ZMod q)ˣ) (σ : affineGroup b) : unitOf b σ ∈ Subgroup.zpowers b :=
  (Classical.choose_spec ((mem_affineGroup b σ.val).mp σ.2)).1

theorem exists_affinePerm (b : (ZMod q)ˣ) (σ : affineGroup b) :
    ∃ t, σ.val = affinePerm (unitOf b σ) t :=
  (Classical.choose_spec ((mem_affineGroup b σ.val).mp σ.2)).2

theorem unitOf_eq (b : (ZMod q)ˣ) (σ : affineGroup b) {u : (ZMod q)ˣ} {t : ZMod q}
    (h : σ.val = affinePerm u t) : unitOf b σ = u := by
  obtain ⟨t', ht'⟩ := exists_affinePerm b σ
  exact congrArg Prod.fst (@affinePerm_injective q (unitOf b σ, t') (u, t) (ht'.symm.trans h))

/-- The unit of a move, as a hom: `(u, t) ↦ u`. -/
noncomputable def unitPart (b : (ZMod q)ˣ) : affineGroup b →* (ZMod q)ˣ where
  toFun := unitOf b
  map_one' := unitOf_eq b 1 affinePerm_one_zero.symm
  map_mul' σ τ := by
    obtain ⟨t, ht⟩ := exists_affinePerm b σ
    obtain ⟨t', ht'⟩ := exists_affinePerm b τ
    exact unitOf_eq b (σ * τ) (by rw [Subgroup.coe_mul, ht, ht', affinePerm_mul])

theorem unitPart_eq (b : (ZMod q)ˣ) (σ : affineGroup b) {u : (ZMod q)ˣ} {t : ZMod q}
    (h : σ.val = affinePerm u t) : unitPart b σ = u :=
  unitOf_eq b σ h

/-- The translations `x ↦ x + t` of the digit group. -/
noncomputable def translations (b : (ZMod q)ˣ) : Subgroup (affineGroup b) := (unitPart b).ker

instance (b : (ZMod q)ˣ) : (translations b).Normal := MonoidHom.normal_ker _

theorem mem_translations (b : (ZMod q)ˣ) (σ : affineGroup b) :
    σ ∈ translations b ↔ ∃ t, σ.val = affinePerm 1 t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := exists_affinePerm b σ
    have h1 : unitOf b σ = 1 := MonoidHom.mem_ker.mp h
    exact ⟨t, by rw [ht, h1]⟩
  · rintro ⟨t, ht⟩
    exact MonoidHom.mem_ker.mpr (unitPart_eq b σ ht)

/-- [proved-standard; formal-checked] **The quotient by the translations is `⟨b⟩`**, cyclic of
order `ord_q(b)`. -/
theorem quotient_translations (b : (ZMod q)ˣ) :
    Nonempty (affineGroup b ⧸ translations b ≃* Subgroup.zpowers b) := by
  have hrange : (unitPart b).range = Subgroup.zpowers b := by
    apply le_antisymm
    · rintro _ ⟨σ, rfl⟩
      exact unitOf_mem b σ
    · intro u hu
      refine ⟨⟨affinePerm u 0, u, hu, 0, rfl⟩, unitPart_eq b _ rfl⟩
  exact ⟨(QuotientGroup.quotientKerEquivRange (unitPart b)).trans
    (MulEquiv.subgroupCongr hrange)⟩

/-- [proved-standard; formal-checked] The translations have index `ord_q(b)`. -/
theorem index_translations (b : (ZMod q)ˣ) : (translations b).index = orderOf b := by
  obtain ⟨e⟩ := quotient_translations b
  rw [Subgroup.index, Nat.card_congr e.toEquiv, Nat.card_zpowers]

theorem translation_pow (t : ZMod q) (n : ℕ) :
    (affinePerm (1 : (ZMod q)ˣ) t) ^ n = affinePerm 1 ((n : ZMod q) * t) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, affinePerm_one_zero]
  | succ n ih =>
    rw [pow_succ, ih, affinePerm_mul, mul_one, Units.val_one, one_mul, Nat.cast_succ]
    ring_nf

/-- [proved-derived; formal-checked] **The only nontrivial abelian normal subgroup is the
translations.** A move `x ↦ u x + t` with `u ≠ 1` does not commute with its conjugate by the
translation by `1`, since that would need `(u − 1)² = 0`; and a nontrivial group of translations of
the prime ring is all of them. -/
theorem abelian_normal_eq_translations (b : (ZMod q)ˣ) (A : Subgroup (affineGroup b))
    (hA : A.Normal) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hne : A ≠ ⊥) :
    A = translations b := by
  have hsub : ∀ σ ∈ A, σ ∈ translations b := by
    intro σ hσ
    obtain ⟨t, ht⟩ := exists_affinePerm b σ
    set u := unitOf b σ
    let τ : affineGroup b := ⟨affinePerm 1 1, 1, Subgroup.one_mem _, 1, rfl⟩
    have hconj := hA.conj_mem σ hσ τ
    have hcomm := congrArg Subtype.val (hc σ hσ _ hconj)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht, τ, affinePerm_inv, affinePerm_mul,
      inv_one, Units.val_one, one_mul, mul_one] at hcomm
    have h2 := congrArg Prod.snd (@affinePerm_injective q (_, _) (_, _) hcomm)
    simp only at h2
    have hu : ((u : ZMod q) - 1) * ((u : ZMod q) - 1) = 0 := by linear_combination -h2
    have hu1 : u = 1 := Units.ext (sub_eq_zero.mp (mul_self_eq_zero.mp hu))
    exact MonoidHom.mem_ker.mpr hu1
  apply le_antisymm (fun σ hσ => hsub σ hσ)
  intro σ hσ
  obtain ⟨ρ, hρ, hρ1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  obtain ⟨s, hs⟩ := (mem_translations b ρ).mp (hsub ρ hρ)
  obtain ⟨t, ht⟩ := (mem_translations b σ).mp hσ
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hρ1
    exact Subtype.ext (hs.trans affinePerm_one_zero)
  have : σ = ρ ^ (t * s⁻¹).val := by
    apply Subtype.ext
    rw [ht, Subgroup.coe_pow, hs, translation_pow, ZMod.natCast_zmod_val, mul_assoc,
      inv_mul_cancel₀ hs0, mul_one]
  rw [this]
  exact A.pow_mem hρ _

end Group

section TurnCore

/-- A group has a **turn core** when an abelian normal subgroup holds every square: the turns of a
plane, where two reflections compose to a turn. -/
def HasTurnCore (G : Type*) [Group G] : Prop :=
  ∃ A : Subgroup G, A.Normal ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧ ∀ g : G, g * g ∈ A

/-- [proved-standard; formal-checked] A turn core passes to subgroups. -/
theorem HasTurnCore.of_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : HasTurnCore H) : HasTurnCore G := by
  obtain ⟨A, hA, hc, hsq⟩ := h
  refine ⟨A.comap f, hA.comap f, fun x hx y hy => hf ?_, fun g => ?_⟩
  · rw [map_mul, map_mul]
    exact hc _ hx _ hy
  · rw [Subgroup.mem_comap, map_mul]
    exact hsq (f g)

/-- [proved-standard; formal-checked] A turn core passes to quotients. -/
theorem HasTurnCore.of_surjective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (h : HasTurnCore G) : HasTurnCore H := by
  obtain ⟨A, hA, hc, hsq⟩ := h
  refine ⟨A.map f, hA.map f hf, ?_, fun g => ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hc x hx y hy]
  · obtain ⟨g', rfl⟩ := hf g
    exact ⟨g' * g', hsq g', map_mul f g' g'⟩

/-- [proved-standard; formal-checked] A turn core passes to products. -/
theorem HasTurnCore.pi {ι : Type*} {H : ι → Type*} [∀ i, Group (H i)]
    (h : ∀ i, HasTurnCore (H i)) : HasTurnCore (∀ i, H i) := by
  choose A hA hc hsq using h
  refine ⟨Subgroup.pi Set.univ A, ⟨fun n hn g => ?_⟩, fun x hx y hy => ?_, fun g => ?_⟩
  · rw [Subgroup.mem_pi] at hn ⊢
    intro i _
    exact (hA i).conj_mem _ (hn i trivial) (g i)
  · rw [Subgroup.mem_pi] at hx hy
    funext i
    exact hc i _ (hx i trivial) _ (hy i trivial)
  · rw [Subgroup.mem_pi]
    intro i _
    exact hsq i (g i)

/-- [proved-derived; formal-checked] **The plane's isometries have a turn core:** the turns
`z ↦ a z`, `|a| = 1`. They commute; a reflection `z ↦ c z̄` conjugates a turn by `a` to the turn
by `ā`; and a reflection's square is the identity, the composite of two reflections being a turn
(`Geometry/ScrewTorsion.plane_reflections_compose`, `plane_turns_commute`). -/
theorem isometry_turnCore : HasTurnCore (ℂ ≃ₗᵢ[ℝ] ℂ) := by
  have hcc : ∀ c : Circle, (c : ℂ) * conj (c : ℂ) = 1 := fun c => by
    rw [← Circle.coe_inv_eq_conj, ← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  have hrefl : ∀ c : Circle, conjLIE.trans (rotation c) * conjLIE.trans (rotation c) = 1 := by
    intro c
    ext1 z
    simp only [LinearIsometryEquiv.coe_mul, LinearIsometryEquiv.coe_one, Function.comp_apply,
      LinearIsometryEquiv.trans_apply, rotation_apply, conjLIE_apply, id_eq]
    have := Holonics.Geometry.Motion.plane_reflections_compose (c : ℂ) (c : ℂ) z
    simp only [Complex.star_def] at this
    rw [this, hcc, one_mul]
  refine ⟨rotation.range, ⟨fun n hn g => ?_⟩, ?_, fun g => ?_⟩
  · obtain ⟨a, rfl⟩ := hn
    rcases linear_isometry_complex g with ⟨c, rfl | rfl⟩
    · refine ⟨a, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, mul_comm c a, mul_assoc, mul_inv_cancel, mul_one]
    · refine ⟨a⁻¹, ?_⟩
      rw [inv_eq_of_mul_eq_one_right (hrefl c)]
      ext1 z
      simp only [LinearIsometryEquiv.coe_mul, Function.comp_apply,
        LinearIsometryEquiv.trans_apply, rotation_apply, conjLIE_apply, map_mul,
        Complex.conj_conj, Circle.coe_inv_eq_conj]
      linear_combination -(conj (a : ℂ) * z) * hcc c
  · rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  · rcases linear_isometry_complex g with ⟨c, rfl | rfl⟩
    · exact ⟨c * c, map_mul _ c c⟩
    · exact ⟨1, by rw [map_one, hrefl c]⟩

variable {q : ℕ} [Fact q.Prime]

/-- [proved-standard; formal-checked] `ord_q(b) ≥ 3` exactly when `b² ≠ 1`. -/
theorem three_le_orderOf_iff (b : (ZMod q)ˣ) : 3 ≤ orderOf b ↔ (b : ZMod q) ^ 2 ≠ 1 := by
  have h2 : (b : ZMod q) ^ 2 = 1 ↔ b ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_one, Units.val_inj]
  rw [Ne, h2, ← orderOf_dvd_iff_pow_eq_one]
  have hpos := orderOf_pos b
  constructor
  · intro h3 hd
    have := Nat.le_of_dvd two_pos hd
    omega
  · intro hnd
    by_contra hlt
    have : orderOf b = 1 ∨ orderOf b = 2 := by omega
    rcases this with h | h <;> rw [h] at hnd <;> norm_num at hnd

/-- [proved-derived; formal-checked] **The digit group has no turn core when `b² ≠ 1`**: the
square of the scaling `x ↦ b x` would lie in an abelian normal subgroup with its conjugate by the
translation by `1`, and the two commute only if `(1 − b²)² = 0`. -/
theorem affine_not_turnCore (b : (ZMod q)ˣ) (hb : (b : ZMod q) ^ 2 ≠ 1) :
    ¬ HasTurnCore (affineGroup b) := by
  rintro ⟨A, hA, hc, hsq⟩
  let g : affineGroup b := ⟨affinePerm b 0, b, Subgroup.mem_zpowers b, 0, rfl⟩
  let τ : affineGroup b := ⟨affinePerm 1 1, 1, Subgroup.one_mem _, 1, rfl⟩
  have hs := hsq g
  have hconj := hA.conj_mem _ hs τ
  have hcomm := congrArg Subtype.val (hc _ hs _ hconj)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, g, τ, affinePerm_inv, affinePerm_mul,
    inv_one, Units.val_one, Units.val_mul, one_mul, mul_one, mul_zero, add_zero] at hcomm
  have h2 := congrArg Prod.snd (@affinePerm_injective q (_, _) (_, _) hcomm)
  simp only at h2
  have hsq0 : ((b : ZMod q) ^ 2 - 1) * ((b : ZMod q) ^ 2 - 1) = 0 := by linear_combination -h2
  exact hb (sub_eq_zero.mp (mul_self_eq_zero.mp hsq0))

/-- [proved-derived; formal-checked] **The dihedral bound** (§7(b)). With `b² ≠ 1` the digit group
`ℤ/q ⋊ ⟨b⟩` is no section of a product of subgroups of the plane's isometry group `O(2)`: no
subgroup `H` of `∏ O(2)` maps onto it. -/
theorem not_section_of_planes (b : (ZMod q)ˣ) (hb : (b : ZMod q) ^ 2 ≠ 1) {ι : Type*}
    (H : Subgroup (ι → (ℂ ≃ₗᵢ[ℝ] ℂ))) (f : H →* affineGroup b) (hf : Function.Surjective f) :
    False :=
  affine_not_turnCore b hb <| HasTurnCore.of_surjective f hf <|
    HasTurnCore.of_injective H.subtype H.subtype_injective <|
      HasTurnCore.pi fun _ => isometry_turnCore

end TurnCore

end Holonics.Mathematics.UncoupledBank

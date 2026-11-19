import HolonicsResearch.HNN.PumpedCarry
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic

/-!
# Uncoupled affine carry circles read a group through `Γ/Γ′`, passive pumped ones through `Γ/Γ″`

The engine's carry is a bank of circles (index `ι`), each a complex charge stepped once a symbol.
The built step is ℂ-affine, `q ↦ αq + v` (a turn, a scale and a drive); the proposed step is
`q ↦ αq + βq̄ + v` (`PumpedCarry.step` with a drive), passive when `‖α‖ + ‖β‖ ≤ 1`. "The bank
holds the group" is stated without a representation: a map `f : Γ → ι → ℂ` (the bank's state
when the word read so far has the value `γ`) such that right multiplication by each `g` is one
step of the bank's kind on every circle, the same step whatever `γ` was.

Sources. An outside reader's reply of November 19 (its lemma "every finite subgroup of
`Aff(1, ℂ)^C` is abelian" and its `D₃` separator, a host control); `HNN/PumpedCarry` (atlas
`parametron.pumped-step-kinds`); atlas `key.commutator-is-and` (`Compression/FaithfulModes`: a
word over commuting moves reads only its counts). What this file adds to the reader's lemma: the
hypothesis is the states' dependence on the group element alone (no representation is assumed),
the affine steps themselves need not commute (with a drive they do not), and the pumped bank has
its own ceiling one commutator further.

[proved-derived; formal-checked] What is proved.

1. **The affine ceiling** (`shift_eq_zero`, `affineTracks_comm`, `affineTracks_commutator`,
   `affineTracks_injective_comm`): in a torsion group, an affine bank has
   `f (γ g h) = f (γ h g)` and leaves every element of `commutator Γ` unread, with no condition
   on the turns; an affine bank that tells the elements apart forces the group to commute.
2. **`S₃`** (`threeCycle_eq_commutator`, `affineTracks_perm_three`): the three-cycle is a
   commutator of two swaps, so an affine bank of any size holds of `S₃` only the sign.
3. **A contracting symbol erases the group, and a contracting pair erases a bracket**
   (`step_sub`, `contracting_erases`, `returning_pair_erases`): if one element of finite order
   acts by a pumped step with `‖α‖ + ‖β‖ < 1` on every circle, with any drive, all states are
   one state; and if an opening step followed by a closing step returns two states, with the
   product of the two sizes below one, the two states are one.
4. **The passive pumped ceiling** (`re_conj_mul`, `im_conj_step_mul_step`, `exists_centre`,
   `commutator_mem_preserving`, `undriven_derived`, `pumpedTracks_derived`): over a finite
   group the mean of the states is a centre every step fixes; about it each step keeps the
   distances and scales the area form `Im (x̄y)` by its gauge `|α|² − |β|²`; so every commutator
   keeps every product `ψ̄(γ)ψ(γ')`, every element of `Γ′` acts on a circle's states as one
   scalar, and every element of `⁅Γ′, Γ′⁆` is unread.
5. **Perfect groups** (`pumpedTracks_perfect`, `alternatingGroup_five_perfect`,
   `pumpedTracks_alternating_five`): if `commutator Γ = ⊤` a passive pumped bank holds nothing;
   `A₅` is perfect, so no passive pumped bank of any size holds anything of `A₅`.
6. **One pumped circle holds `D₃`** (`dihedralState_injective_and_steps`,
   `dihedralState_pumpedTracks`, `not_affineTracks_injective_dihedral`): the states
   `r i ↦ ωⁱ·i`, `sr i ↦ ωⁱ·(−i)` are six distinct points, `r j` acts by the turn `(ωʲ, 0)` and
   `sr j` by the reflection `(0, ωʲ)`, each of unit size and with no drive; no affine bank of any
   size tells the elements of `D₃` apart. This is the separation of the two kinds of carry.
7. **Generators suffice** (`affineTracks_of_generators`): affine steps for a generating set of a
   torsion group give affine steps for every element.

Limits. Nothing here counts what a stack of brackets costs: a returning pair of unit steps, or a
contraction answered by an expansion, holds one, and its depth is then paid in the register's
places (`Foundation/SectionGauge`: division with remainder is the pop). The statements are about
a set of states that holds the group for words of every length;
they say nothing of a trained carry at a fixed length, where a contracting carry also codes the
recent symbols. The pumped ceiling is stated for passive steps (the engine's chart); without
passivity it needs the averaging argument that puts a finite subgroup of `GL₂(ℝ)` in a rotation
group, which is not given here. Finer than `Γ″`, only cyclic and dihedral quotients are held
(from the classification of finite subgroups of `O(2)`, not proved here). Circles coupled to
each other are outside the statements (a unitary step on two circles holds the binary
icosahedral group, which is perfect: a training reading, not proved here).

Computational object: the helical pair interaction. Of the winding guide's six general objects
this module touches the helix (a circle's turn), the pair (a reflection is the pair's dyad
`z ↦ z̄`) and the tower thread (the carry along a passage); faces and placement, the cell
holonomy and the tube stay attached.

Consumers: the atlas row `parametron.carry-bank-group-ceiling`, and the engine's carry control
(`tools/pumped_carry_control.py`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.CarryGroupTracking

open Complex ComplexConjugate
open scoped commutatorElement
open Holonics.HNN.PumpedCarry (step norm_step_le gauge)

variable {Γ ι : Type*}

/-! ## 1. What it means for a bank to hold a group -/

/-- [definition] Every right multiplication is one ℂ-affine step on every circle. -/
def AffineTracks [Mul Γ] (f : Γ → ι → ℂ) : Prop :=
  ∀ g : Γ, ∃ α v : ι → ℂ, ∀ γ c, f (γ * g) c = α c * f γ c + v c

/-- [definition] Every right multiplication is one passive pumped step with a drive. -/
def PumpedTracks [Mul Γ] (f : Γ → ι → ℂ) : Prop :=
  ∀ g : Γ, ∃ α β v : ι → ℂ, (∀ c, ‖α c‖ + ‖β c‖ ≤ 1) ∧
    ∀ γ c, f (γ * g) c = step (α c) (β c) (f γ c) + v c

/-- [definition] The elements whose right multiplication leaves every state as it was. -/
def unread {X : Type*} [Group Γ] (f : Γ → X) : Subgroup Γ where
  carrier := {k | ∀ γ, f (γ * k) = f γ}
  mul_mem' := by
    intro a b ha hb γ
    rw [← mul_assoc, hb, ha]
  one_mem' := by
    intro γ
    change f (γ * 1) = f γ
    rw [mul_one]
  inv_mem' := by
    intro a ha γ
    have := ha (γ * a⁻¹)
    rw [inv_mul_cancel_right] at this
    exact this.symm

/-- [definition] Membership in `unread f`, unfolded. -/
theorem mem_unread {X : Type*} [Group Γ] (f : Γ → X) (k : Γ) :
    k ∈ unread f ↔ ∀ γ, f (γ * k) = f γ := Iff.rfl

/-! ## 2. The affine bank -/

/-- [proved-derived; formal-checked] A shift by `t` under a torsion element is no shift: if
`φ (δ k) = φ δ + t` for every `δ` and `k` has finite order, then `t = 0`. -/
theorem shift_eq_zero [Group Γ] {φ : Γ → ℂ} {k : Γ} {t : ℂ} (hk : IsOfFinOrder k)
    (h : ∀ δ, φ (δ * k) = φ δ + t) : t = 0 := by
  have hn : ∀ n : ℕ, ∀ δ, φ (δ * k ^ n) = φ δ + n * t := by
    intro n
    induction n with
    | zero => intro δ; simp
    | succ n ih =>
      intro δ
      rw [pow_succ, ← mul_assoc, h, ih]
      push_cast
      ring
  have h1 := hn (orderOf k) 1
  rw [pow_orderOf_eq_one, mul_one] at h1
  have hpos : (orderOf k : ℂ) ≠ 0 := by exact_mod_cast hk.orderOf_pos.ne'
  have h2 : (orderOf k : ℂ) * t = 0 := by linear_combination -h1
  exact (mul_eq_zero.mp h2).resolve_left hpos

/-- [proved-derived; formal-checked] **An affine bank reads a torsion group only through its
abelianization:** `f (γ g h) = f (γ h g)`. No condition on the turns `α` is needed. -/
theorem affineTracks_comm [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g) {f : Γ → ι → ℂ}
    (hf : AffineTracks f) (γ g h : Γ) : f (γ * g * h) = f (γ * h * g) := by
  funext c
  obtain ⟨αg, vg, hg⟩ := hf g
  obtain ⟨αh, vh, hh⟩ := hf h
  have key0 : ∀ ε, f (ε * h * g) c =
      f (ε * g * h) c + (αg c * vh c + vg c - αh c * vg c - vh c) := by
    intro ε
    rw [hg (ε * h), hh ε, hh (ε * g), hg ε]
    ring
  have key : ∀ δ, f (δ * ((g * h)⁻¹ * (h * g))) c =
      f δ c + (αg c * vh c + vg c - αh c * vg c - vh c) := by
    intro δ
    have := key0 (δ * (g * h)⁻¹)
    have e1 : δ * (g * h)⁻¹ * h * g = δ * ((g * h)⁻¹ * (h * g)) := by group
    have e2 : δ * (g * h)⁻¹ * g * h = δ := by group
    rw [e1, e2] at this
    exact this
  have ht := shift_eq_zero (φ := fun δ => f δ c) (htor _) key
  rw [key0 γ, ht, add_zero]

/-- [proved-derived; formal-checked] **An affine bank leaves every commutator unread:** for
`k ∈ commutator Γ`, `f (γ k) = f γ`. -/
theorem affineTracks_commutator [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g) {f : Γ → ι → ℂ}
    (hf : AffineTracks f) : ∀ k ∈ commutator Γ, ∀ γ, f (γ * k) = f γ := by
  have hle : commutator Γ ≤ unread f := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _ γ
    have := affineTracks_comm htor hf (γ * a * b) a⁻¹ b⁻¹
    have e1 : γ * ⁅a, b⁆ = γ * a * b * a⁻¹ * b⁻¹ := by rw [commutatorElement_def]; group
    have e2 : γ * a * b * b⁻¹ * a⁻¹ = γ := by group
    rw [e1, this, e2]
  intro k hk
  exact hle hk

/-- [proved-derived; formal-checked] **An affine bank that tells every element apart forces the
group to commute.** -/
theorem affineTracks_injective_comm [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g)
    {f : Γ → ι → ℂ} (hf : AffineTracks f) (hinj : Function.Injective f) (g h : Γ) :
    g * h = h * g := by
  have := hinj (affineTracks_comm htor hf 1 g h)
  simpa using this

/-- [proved-standard; formal-checked] The three-cycle of `S₃` is the commutator of two swaps. -/
theorem threeCycle_eq_commutator :
    (c[(0 : Fin 3), 1, 2] : Equiv.Perm (Fin 3)) =
      ⁅(Equiv.swap 0 1 : Equiv.Perm (Fin 3)), (Equiv.swap 0 2 : Equiv.Perm (Fin 3))⁆ := by
  decide

/-- [proved-derived; formal-checked] **An affine bank of any size holds of `S₃` only the sign:**
the three-cycle leaves every state as it was. -/
theorem affineTracks_perm_three {f : Equiv.Perm (Fin 3) → ι → ℂ} (hf : AffineTracks f)
    (γ : Equiv.Perm (Fin 3)) : f (γ * c[(0 : Fin 3), 1, 2]) = f γ := by
  apply affineTracks_commutator (fun g => isOfFinOrder_of_finite g) hf
  rw [threeCycle_eq_commutator, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-! ## 3. A contracting symbol erases the group -/

/-- [proved-derived; formal-checked] The pumped step is additive. -/
theorem step_sub (α β x y : ℂ) : step α β x - step α β y = step α β (x - y) := by
  simp only [step, map_sub]
  ring

/-- [proved-derived; formal-checked] **A contracting symbol erases the group:** if one element
`g` of finite order acts by a pumped step with `‖α‖ + ‖β‖ < 1` on every circle (with any drive),
every state is the same. -/
theorem contracting_erases [Group Γ] {f : Γ → ι → ℂ} {g : Γ} (hg : IsOfFinOrder g)
    (α β v : ι → ℂ) (hρ : ∀ c, ‖α c‖ + ‖β c‖ < 1)
    (hstep : ∀ γ c, f (γ * g) c = step (α c) (β c) (f γ c) + v c) (γ γ' : Γ) : f γ = f γ' := by
  funext c
  set ρ := ‖α c‖ + ‖β c‖ with hρdef
  have hρ0 : 0 ≤ ρ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hk : ∀ k : ℕ, ‖f (γ * g ^ k) c - f (γ' * g ^ k) c‖ ≤ ρ ^ k * ‖f γ c - f γ' c‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ← mul_assoc, hstep, hstep, add_sub_add_right_eq_sub, step_sub]
      calc ‖step (α c) (β c) (f (γ * g ^ k) c - f (γ' * g ^ k) c)‖
          ≤ ρ * ‖f (γ * g ^ k) c - f (γ' * g ^ k) c‖ := norm_step_le _ _ _
        _ ≤ ρ * (ρ ^ k * ‖f γ c - f γ' c‖) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * ‖f γ c - f γ' c‖ := by ring
  have h1 := hk (orderOf g)
  rw [pow_orderOf_eq_one, mul_one, mul_one] at h1
  have hlt : ρ ^ orderOf g < 1 := pow_lt_one₀ hρ0 (hρ c) hg.orderOf_pos.ne'
  have hn : ‖f γ c - f γ' c‖ = 0 := by
    have := norm_nonneg (f γ c - f γ' c)
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- [proved-derived; formal-checked] **A returning pair needs sizes whose product is at least
one:** if an opening step followed by a closing step returns each of two states to itself, and
the product of the two steps' sizes `(‖α'‖ + ‖β'‖)(‖α‖ + ‖β‖)` is below one, the two states are
one state. A bracket pair of two contracting steps holds nothing, whatever the drives. -/
theorem returning_pair_erases {α β v α' β' v' : ℂ}
    (hρ : (‖α'‖ + ‖β'‖) * (‖α‖ + ‖β‖) < 1) {x y : ℂ}
    (hx : step α' β' (step α β x + v) + v' = x) (hy : step α' β' (step α β y + v) + v' = y) :
    x = y := by
  by_contra hne
  have hd : x - y = step α' β' (step α β (x - y)) := by
    have h1 : step α β x + v - (step α β y + v) = step α β (x - y) := by
      rw [← step_sub]
      ring
    calc x - y = (step α' β' (step α β x + v) + v') - (step α' β' (step α β y + v) + v') := by
          rw [hx, hy]
      _ = step α' β' ((step α β x + v) - (step α β y + v)) := by
          rw [← step_sub]
          ring
      _ = step α' β' (step α β (x - y)) := by rw [h1]
  have hpos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have h2 : ‖x - y‖ ≤ (‖α'‖ + ‖β'‖) * ((‖α‖ + ‖β‖) * ‖x - y‖) := by
    calc ‖x - y‖ = ‖step α' β' (step α β (x - y))‖ := congrArg norm hd
      _ ≤ (‖α'‖ + ‖β'‖) * ‖step α β (x - y)‖ := norm_step_le _ _ _
      _ ≤ (‖α'‖ + ‖β'‖) * ((‖α‖ + ‖β‖) * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (norm_step_le _ _ _)
            (add_nonneg (norm_nonneg _) (norm_nonneg _))
  have h3 := mul_lt_mul_of_pos_right hρ hpos
  nlinarith

/-! ## 4. The passive pumped bank -/

/-- [proved-derived; formal-checked] Polarization: the real part of `x̄y` is read from three
norms. -/
theorem re_conj_mul (x y : ℂ) :
    (conj x * y).re = (‖x‖ ^ 2 + ‖y‖ ^ 2 - ‖x - y‖ ^ 2) / 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- [proved-derived; formal-checked] **A step scales the area form `Im (x̄y)` by its gauge**
`|α|² − |β|²`. -/
theorem im_conj_step_mul_step (α β x y : ℂ) :
    (conj (step α β x) * step α β y).im = gauge α β * (conj x * y).im := by
  unfold PumpedCarry.gauge
  simp only [step, map_add, map_mul, Complex.conj_conj, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- [proved-derived; formal-checked] **The centre:** over a finite group, a bank of driven pumped
steps has a centre `m` (the mean of the states) that every step fixes, so the states less `m` obey
the undriven steps. -/
theorem exists_centre [Group Γ] [Fintype Γ] {φ a b v : Γ → ℂ}
    (hstep : ∀ γ g, φ (γ * g) = step (a g) (b g) (φ γ) + v g) :
    ∃ m : ℂ, ∀ γ g, φ (γ * g) - m = step (a g) (b g) (φ γ - m) := by
  have hN : (Fintype.card Γ : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨(1 : Γ)⟩).ne'
  refine ⟨(∑ γ, φ γ) / Fintype.card Γ, ?_⟩
  intro γ g
  have hsum : ∑ x, φ (x * g) = ∑ x, φ x :=
    Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)
  have hS : ∑ x, φ x = a g * ∑ x, φ x + b g * conj (∑ x, φ x) + Fintype.card Γ * v g := by
    calc ∑ x, φ x = ∑ x, φ (x * g) := hsum.symm
      _ = _ := by
        simp only [hstep, step, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        rw [map_sum, Finset.mul_sum, Finset.mul_sum]
  have hm : step (a g) (b g) ((∑ x, φ x) / Fintype.card Γ) + v g = (∑ x, φ x) / Fintype.card Γ := by
    rw [step, map_div₀, Complex.conj_natCast]
    field_simp
    linear_combination -hS
  rw [hstep, ← step_sub]
  linear_combination hm

/-- [definition] The elements whose right multiplication keeps every product `ψ̄(γ)ψ(γ')`. -/
def preserving [Group Γ] (ψ : Γ → ℂ) : Subgroup Γ where
  carrier := {k | ∀ γ γ', conj (ψ (γ * k)) * ψ (γ' * k) = conj (ψ γ) * ψ γ'}
  mul_mem' := by
    intro a b ha hb γ γ'
    have h1 := hb (γ * a) (γ' * a)
    rw [← mul_assoc, ← mul_assoc, h1, ha]
  one_mem' := by
    intro γ γ'
    simp only [mul_one]
  inv_mem' := by
    intro a ha γ γ'
    have := ha (γ * a⁻¹) (γ' * a⁻¹)
    rw [inv_mul_cancel_right, inv_mul_cancel_right] at this
    exact this.symm

/-- [proved-derived; formal-checked] **An undriven passive pumped bank on one circle keeps every
product `ψ̄(γ)ψ(γ')` under every commutator.** -/
theorem commutator_mem_preserving [Group Γ] {ψ a b : Γ → ℂ} (hpass : ∀ g, ‖a g‖ + ‖b g‖ ≤ 1)
    (hstep : ∀ γ g, ψ (γ * g) = step (a g) (b g) (ψ γ)) (x y : Γ) :
    ⁅x, y⁆ ∈ preserving ψ := by
  have hle : ∀ g γ γ', ‖ψ (γ * g) - ψ (γ' * g)‖ ≤ ‖ψ γ - ψ γ'‖ := by
    intro g γ γ'
    rw [hstep, hstep, step_sub]
    exact (norm_step_le _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hpass g))
  have hdist : ∀ g γ γ', ‖ψ (γ * g) - ψ (γ' * g)‖ = ‖ψ γ - ψ γ'‖ := by
    intro g γ γ'
    refine le_antisymm (hle g γ γ') ?_
    have := hle g⁻¹ (γ * g) (γ' * g)
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  have hle' : ∀ g γ, ‖ψ (γ * g)‖ ≤ ‖ψ γ‖ := by
    intro g γ
    rw [hstep]
    exact (norm_step_le _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hpass g))
  have hnorm : ∀ g γ, ‖ψ (γ * g)‖ = ‖ψ γ‖ := by
    intro g γ
    refine le_antisymm (hle' g γ) ?_
    have := hle' g⁻¹ (γ * g)
    rwa [mul_inv_cancel_right] at this
  have hre : ∀ g γ γ', (conj (ψ (γ * g)) * ψ (γ' * g)).re = (conj (ψ γ) * ψ γ').re := by
    intro g γ γ'
    rw [re_conj_mul, re_conj_mul, hnorm, hnorm, hdist]
  have him : ∀ g γ γ', (conj (ψ (γ * g)) * ψ (γ' * g)).im =
      gauge (a g) (b g) * (conj (ψ γ) * ψ γ').im := by
    intro g γ γ'
    rw [hstep, hstep, im_conj_step_mul_step]
  change ∀ γ γ', conj (ψ (γ * ⁅x, y⁆)) * ψ (γ' * ⁅x, y⁆) = conj (ψ γ) * ψ γ'
  by_cases hA : ∀ γ γ', (conj (ψ γ) * ψ γ').im = 0
  · intro γ γ'
    exact Complex.ext (hre _ γ γ') (by rw [hA, hA])
  · push Not at hA
    obtain ⟨γ₀, γ₁, h01⟩ := hA
    obtain ⟨d, hd⟩ : ∃ d : Γ → ℝ, ∀ g, gauge (a g) (b g) = d g := ⟨_, fun _ => rfl⟩
    simp only [hd] at him
    have dmul : ∀ g h, d (g * h) = d g * d h := by
      intro g h
      have e1 := him (g * h) γ₀ γ₁
      have e2 := him h (γ₀ * g) (γ₁ * g)
      rw [him g γ₀ γ₁] at e2
      rw [← mul_assoc, ← mul_assoc] at e1
      have : d (g * h) * (conj (ψ γ₀) * ψ γ₁).im = (d g * d h) * (conj (ψ γ₀) * ψ γ₁).im := by
        rw [← e1, e2]
        ring
      exact mul_right_cancel₀ h01 this
    have d1 : d 1 = 1 := by
      have e := him 1 γ₀ γ₁
      simp only [mul_one] at e
      have : d 1 * (conj (ψ γ₀) * ψ γ₁).im = 1 * (conj (ψ γ₀) * ψ γ₁).im := by
        rw [← e, one_mul]
      exact mul_right_cancel₀ h01 this
    have dinv : ∀ g, d g * d g⁻¹ = 1 := by
      intro g
      rw [← dmul, mul_inv_cancel, d1]
    have dc : d ⁅x, y⁆ = 1 := by
      rw [commutatorElement_def, dmul, dmul, dmul]
      calc d x * d y * d x⁻¹ * d y⁻¹ = (d x * d x⁻¹) * (d y * d y⁻¹) := by ring
        _ = 1 := by rw [dinv, dinv, one_mul]
    intro γ γ'
    refine Complex.ext (hre _ γ γ') ?_
    have := him ⁅x, y⁆ γ γ'
    rw [this, dc, one_mul]

/-- [proved-derived; formal-checked] **An undriven passive pumped circle leaves every element of
`⁅Γ′, Γ′⁆` unread:** `ψ (γ ⁅k, k'⁆) = ψ γ` for `k k' ∈ commutator Γ`. -/
theorem undriven_derived [Group Γ] {ψ a b : Γ → ℂ} (hpass : ∀ g, ‖a g‖ + ‖b g‖ ≤ 1)
    (hstep : ∀ γ g, ψ (γ * g) = step (a g) (b g) (ψ γ)) {k k' : Γ}
    (hk : k ∈ commutator Γ) (hk' : k' ∈ commutator Γ) (γ : Γ) :
    ψ (γ * ⁅k, k'⁆) = ψ γ := by
  have hle : commutator Γ ≤ preserving ψ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    exact commutator_mem_preserving hpass hstep x y
  have hnorm : ∀ g γ, ‖ψ (γ * g)‖ = ‖ψ γ‖ := by
    have hle' : ∀ g γ, ‖ψ (γ * g)‖ ≤ ‖ψ γ‖ := by
      intro g γ
      rw [hstep]
      exact (norm_step_le _ _ _).trans (mul_le_of_le_one_left (norm_nonneg _) (hpass g))
    intro g γ
    refine le_antisymm (hle' g γ) ?_
    have := hle' g⁻¹ (γ * g)
    rwa [mul_inv_cancel_right] at this
  have hR : ∀ γ, ‖ψ γ‖ = ‖ψ 1‖ := fun γ => by rw [← hnorm γ 1, one_mul]
  by_cases h0 : ψ 1 = 0
  · have hz : ∀ γ, ψ γ = 0 := fun γ => norm_eq_zero.mp (by rw [hR, h0, norm_zero])
    rw [hz, hz]
  · have hu : ∀ z ∈ preserving ψ, ∀ γ, ψ (γ * z) = conj (ψ 1) / conj (ψ z) * ψ γ := by
      intro z hz γ
      have hne : conj (ψ z) ≠ 0 := by
        rw [map_ne_zero]
        intro h
        apply h0
        rw [← norm_eq_zero, ← hR z, h, norm_zero]
      have := hz 1 γ
      rw [one_mul] at this
      rw [div_mul_eq_mul_div, eq_div_iff hne]
      linear_combination this
    have hswap : ∀ z ∈ preserving ψ, ∀ w ∈ preserving ψ, ∀ ε, ψ (ε * z * w) = ψ (ε * w * z) := by
      intro z hz w hw ε
      rw [hu w hw (ε * z), hu z hz ε, hu z hz (ε * w), hu w hw ε]
      ring
    have hki : k⁻¹ ∈ preserving ψ := (preserving ψ).inv_mem (hle hk)
    have hki' : k'⁻¹ ∈ preserving ψ := (preserving ψ).inv_mem (hle hk')
    have e1 : γ * ⁅k, k'⁆ = γ * k * k' * k⁻¹ * k'⁻¹ := by rw [commutatorElement_def]; group
    have e2 : γ * k * k' * k'⁻¹ * k⁻¹ = γ := by group
    rw [e1, hswap _ hki _ hki', e2]

/-- [proved-derived; formal-checked] **A passive pumped bank of uncoupled circles reads a
finite group only through `Γ/Γ″`:** for `k ∈ ⁅Γ′, Γ′⁆` (the second derived subgroup),
`f (γ k) = f γ`. -/
theorem pumpedTracks_derived [Group Γ] [Fintype Γ] {f : Γ → ι → ℂ} (hf : PumpedTracks f) :
    ∀ k ∈ ⁅commutator Γ, commutator Γ⁆, ∀ γ, f (γ * k) = f γ := by
  choose A B V hAB hst using hf
  have hle : ⁅commutator Γ, commutator Γ⁆ ≤ unread f := by
    rw [Subgroup.commutator_le]
    intro k hk k' hk' γ
    funext c
    obtain ⟨m, hm⟩ := exists_centre (φ := fun γ => f γ c) (a := fun g => A g c)
      (b := fun g => B g c) (v := fun g => V g c) (fun γ g => hst g γ c)
    have := undriven_derived (ψ := fun γ => f γ c - m) (a := fun g => A g c)
      (b := fun g => B g c) (fun g => hAB g c) (fun γ g => hm γ g) hk hk' γ
    simpa using this
  intro k hk
  exact hle hk

/-- [proved-derived; formal-checked] **On a perfect group:** if `commutator Γ = ⊤`, a passive
pumped bank holds nothing: every state is the state at `1`. -/
theorem pumpedTracks_perfect [Group Γ] [Fintype Γ] {f : Γ → ι → ℂ} (hf : PumpedTracks f)
    (hperf : commutator Γ = ⊤) (γ : Γ) : f γ = f 1 := by
  have htop : ⁅commutator Γ, commutator Γ⁆ = ⊤ := by rw [hperf, ← commutator_def, hperf]
  have := pumpedTracks_derived hf γ (by rw [htop]; exact Subgroup.mem_top _) 1
  rwa [one_mul] at this

/-! ## 5. One pumped circle holds the dihedral group of the triangle -/

/-- [definition] The primitive cube root of unity `ω = e^{2πi/3}`. -/
def ω : ℂ := exp (2 * Real.pi * I / (3 : ℕ))

/-- [proved-standard; formal-checked] `ω` is a primitive cube root of unity. -/
theorem ω_prim : IsPrimitiveRoot ω 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

/-- [proved-standard; formal-checked] `‖ω‖ = 1`. -/
theorem norm_ω : ‖ω‖ = 1 := by
  have h : ‖ω‖ ^ 3 = 1 := by rw [← norm_pow, ω_prim.pow_eq_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

/-- [definition] The turn of a residue `i` mod 3: `e i = ω ^ i.val`. -/
def e (i : ZMod 3) : ℂ := ω ^ i.val

/-- [proved-standard; formal-checked] Powers of `ω` read their exponent mod 3. -/
theorem pow_mod_three (n : ℕ) : ω ^ (n % 3) = ω ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, ω_prim.pow_eq_one, one_pow, mul_one]

/-- [proved-standard; formal-checked] `e` turns addition mod 3 into multiplication. -/
theorem e_add (i j : ZMod 3) : e (i + j) = e i * e j := by
  rw [e, e, e, ZMod.val_add, pow_mod_three, pow_add]

/-- [proved-standard; formal-checked] Each `e i` is a unit turn. -/
theorem norm_e (i : ZMod 3) : ‖e i‖ = 1 := by
  rw [e, norm_pow, norm_ω, one_pow]

/-- [proved-standard; formal-checked] `e (j − i) = e j · conj (e i)`. -/
theorem e_sub (i j : ZMod 3) : e (j - i) = e j * conj (e i) := by
  have h : e j = e (j - i) * e i := by rw [← e_add, sub_add_cancel]
  have hn : e i * conj (e i) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e, one_pow, Complex.ofReal_one]
  rw [h, mul_assoc, hn, mul_one]

/-- [proved-standard; formal-checked] `e k = 1` only at `k = 0`. -/
theorem e_eq_one {k : ZMod 3} (h : e k = 1) : k = 0 := by
  rw [e, ω_prim.pow_eq_one_iff_dvd] at h
  have hlt := ZMod.val_lt k
  have h0 : k.val = 0 := by omega
  exact (ZMod.val_eq_zero k).mp h0

/-- [proved-standard; formal-checked] No `e k` is `−1`. -/
theorem e_ne_neg_one (k : ZMod 3) : e k ≠ -1 := by
  intro h
  have h2 : ω ^ (2 * k.val) = 1 := by rw [pow_mul', ← e, h]; norm_num
  rw [ω_prim.pow_eq_one_iff_dvd] at h2
  have hlt := ZMod.val_lt k
  have h0 : k.val = 0 := by omega
  rw [e, h0, pow_zero] at h
  norm_num at h

/-- [definition] The states of one circle on `D₃`: `r i ↦ e i · i` and `sr i ↦ e i · (−i)`. -/
def dihedralState : DihedralGroup 3 → Unit → ℂ
  | .r i, _ => e i * I
  | .sr i, _ => e i * (-I)

/-- [proved-derived; formal-checked] **One pumped circle holds `D₃`:** the states
`dihedralState` tell the six elements apart, and right multiplication by each element is one
undriven pumped step of unit size (`‖α‖ + ‖β‖ = 1`): a turn `(e j, 0)` for `r j`, a reflection
`(0, e j)` for `sr j`. -/
theorem dihedralState_injective_and_steps :
    Function.Injective dihedralState ∧
      ∀ g : DihedralGroup 3, ∃ α β : Unit → ℂ, (∀ c, ‖α c‖ + ‖β c‖ = 1) ∧
        ∀ γ c, dihedralState (γ * g) c = step (α c) (β c) (dihedralState γ c) := by
  refine ⟨?_, ?_⟩
  · have key : ∀ i j : ZMod 3, e i = e j → i = j := by
      intro i j h
      have h' : e (i - j) = 1 := by
        rw [e_sub, h, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e, one_pow,
          Complex.ofReal_one]
      exact sub_eq_zero.mp (e_eq_one h')
    have key' : ∀ i j : ZMod 3, e i ≠ -e j := by
      intro i j h
      apply e_ne_neg_one (i - j)
      rw [e_sub, h, neg_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_e, one_pow,
        Complex.ofReal_one]
    intro x y hxy
    have h := congrFun hxy ()
    cases x <;> cases y <;> simp only [dihedralState] at h
    · rw [key _ _ (mul_right_cancel₀ Complex.I_ne_zero h)]
    · exact absurd (mul_right_cancel₀ Complex.I_ne_zero (by rw [h]; ring)) (key' _ _)
    · exact absurd (mul_right_cancel₀ Complex.I_ne_zero (by rw [← h]; ring)) (key' _ _)
    · rw [key _ _ (mul_right_cancel₀ (neg_ne_zero.mpr Complex.I_ne_zero) h)]
  · intro g
    cases g with
    | r j =>
      refine ⟨fun _ => e j, fun _ => 0, fun _ => by rw [norm_e, norm_zero, add_zero], ?_⟩
      intro γ c
      cases γ with
      | r i =>
        simp only [DihedralGroup.r_mul_r, dihedralState, step, e_add]
        simp
        ring
      | sr i =>
        simp only [DihedralGroup.sr_mul_r, dihedralState, step, e_add]
        simp
        ring
    | sr j =>
      refine ⟨fun _ => 0, fun _ => e j, fun _ => by rw [norm_e, norm_zero, zero_add], ?_⟩
      intro γ c
      cases γ with
      | r i =>
        simp only [DihedralGroup.r_mul_sr, dihedralState, step, e_sub, map_mul, Complex.conj_I]
        ring
      | sr i =>
        simp only [DihedralGroup.sr_mul_sr, dihedralState, step, e_sub, map_mul, map_neg,
          Complex.conj_I]
        ring

/-- [proved-derived; formal-checked] The states `dihedralState` are held by passive pumped
steps. -/
theorem dihedralState_pumpedTracks : PumpedTracks dihedralState := by
  intro g
  obtain ⟨α, β, h1, h2⟩ := dihedralState_injective_and_steps.2 g
  exact ⟨α, β, fun _ => 0, fun c => (h1 c).le, fun γ c => by rw [h2, add_zero]⟩

/-- [counterexample; formal-checked] **The separation:** no affine bank of any size tells the six
elements of `D₃` apart, while one pumped circle does (`dihedralState_injective_and_steps`). -/
theorem not_affineTracks_injective_dihedral {f : DihedralGroup 3 → ι → ℂ}
    (hf : AffineTracks f) : ¬ Function.Injective f := by
  intro hinj
  have h := affineTracks_injective_comm (fun g => isOfFinOrder_of_finite g) hf hinj
    (DihedralGroup.r 1) (DihedralGroup.sr 0)
  revert h
  decide

/-! ## 6. A perfect group: `A₅` -/

/-- [proved-standard; formal-checked] **`A₅` is perfect:** its commutator subgroup is normal, so
by simplicity it is `⊥` or `⊤`, and two three-cycles that do not commute rule out `⊥`. -/
theorem alternatingGroup_five_perfect : commutator (alternatingGroup (Fin 5)) = ⊤ := by
  have hN : (commutator (alternatingGroup (Fin 5))).Normal := by
    rw [commutator_def]
    infer_instance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal _ hN with h | h
  · exfalso
    let a : alternatingGroup (Fin 5) :=
      ⟨c[(0 : Fin 5), 1, 2], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    let b : alternatingGroup (Fin 5) :=
      ⟨c[(0 : Fin 5), 1, 3], Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩
    have hmem : ⁅a, b⁆ ∈ commutator (alternatingGroup (Fin 5)) := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot] at hmem
    revert hmem
    decide
  · exact h

/-- [proved-derived; formal-checked] **A passive pumped bank of any size holds nothing of `A₅`:**
every state is the state at `1`. -/
theorem pumpedTracks_alternating_five {f : alternatingGroup (Fin 5) → ι → ℂ}
    (hf : PumpedTracks f) (γ : alternatingGroup (Fin 5)) : f γ = f 1 :=
  pumpedTracks_perfect hf alternatingGroup_five_perfect γ

/-! ## 7. Steps on generators suffice -/

/-- [proved-derived; formal-checked] **Affine steps on a generating set give affine steps for
every element** of a torsion group: steps compose, and an inverse is a power. -/
theorem affineTracks_of_generators [Group Γ] (htor : ∀ g : Γ, IsOfFinOrder g)
    {f : Γ → ι → ℂ} (S : Set Γ) (hS : Subgroup.closure S = ⊤)
    (hgen : ∀ g ∈ S, ∃ α v : ι → ℂ, ∀ γ c, f (γ * g) c = α c * f γ c + v c) :
    AffineTracks f := by
  have hmul : ∀ g h : Γ, (∃ α v : ι → ℂ, ∀ γ c, f (γ * g) c = α c * f γ c + v c) →
      (∃ α v : ι → ℂ, ∀ γ c, f (γ * h) c = α c * f γ c + v c) →
      ∃ α v : ι → ℂ, ∀ γ c, f (γ * (g * h)) c = α c * f γ c + v c := by
    rintro g h ⟨αg, vg, hg⟩ ⟨αh, vh, hh⟩
    refine ⟨fun c => αh c * αg c, fun c => αh c * vg c + vh c, fun γ c => ?_⟩
    rw [← mul_assoc, hh, hg]
    ring
  have hone : ∃ α v : ι → ℂ, ∀ γ c, f (γ * 1) c = α c * f γ c + v c :=
    ⟨fun _ => 1, fun _ => 0, fun γ c => by rw [mul_one, one_mul, add_zero]⟩
  have hpow : ∀ g : Γ, (∃ α v : ι → ℂ, ∀ γ c, f (γ * g) c = α c * f γ c + v c) →
      ∀ n : ℕ, ∃ α v : ι → ℂ, ∀ γ c, f (γ * g ^ n) c = α c * f γ c + v c := by
    intro g hg n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ _ ih hg
  intro g
  have hg : g ∈ Subgroup.closure S := by rw [hS]; exact Subgroup.mem_top g
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ α v : ι → ℂ, ∀ γ c, f (γ * g) c = α c * f γ c + v c)
    (fun x hx => hgen x hx) hone (fun x y _ _ hx hy => hmul x y hx hy) ?_ hg
  intro x _ hx
  have hn : orderOf x ≠ 0 := (htor x).orderOf_pos.ne'
  have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [pow_sub_one_mul hn, pow_orderOf_eq_one]
  rw [hinv]
  exact hpow x hx _

end Holonics.HNN.CarryGroupTracking

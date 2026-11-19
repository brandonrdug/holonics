import Mathlib
import HolonicsResearch.Geometry.Farey

/-!
# The modular group is a free product: `PSL(2, ℤ) ≅ ℤ/2 ∗ ℤ/3`

Source: #410's box "Monodromy as a group of moves: `PSL(2, ℤ) ≅ ℤ/2 ∗ ℤ/3` joined to `Geometry/Farey`", its first
clause. `Geometry/Farey` reads a continued fraction as a word in `GL₂(ℤ)` and names the group the modular one; the
Stern–Brocot moves `L = [[1, 0], [1, 1]]` and `R = [[1, 1], [0, 1]]` stand there as two unimodular matrices
(`sbL`, `sbR`). This file proves what that group is as a group of moves: every move of `PSL(2, ℤ)` is one reduced
word in a half-turn and a third of a turn, and no reduced word is trivial.

[proved-standard; formal-checked] What is proved.

1. **The two moves** (§1). The half-turn `S = [[0, −1], [1, 0]]` (`z ↦ −1/z`, Mathlib's `ModularGroup.S`) and the
   third of a turn `U = S T = [[0, −1], [1, 1]]` (`z ↦ −1/(z + 1)`; this file's choice of the two conventions) have
   `S² = −1` and `U³ = −1` in `SL(2, ℤ)` (`S_sq`, `U_cube`), and `U² = T⁻¹ S` (`U_sq`). In
   `PSL(2, ℤ) = SL(2, ℤ)/{±1}` (Mathlib's `Matrix.ProjectiveSpecialLinearGroup`) their classes `s`, `u` have orders
   two and three (`orderOf_s`, `orderOf_u`), and the centre of `SL(2, ℤ)` is `±1` (`center_eq_one_or_neg_one`).
2. **The action on the upper half plane** (§2). The Möbius action of `SL(2, ℤ)` on `ℍ` kills the centre
   (`center_smul`, `center_le_ker`) and so descends to `PSL(2, ℤ)` (`pslToPerm`, `pslAction`, with
   `proj_smul`). The half-turn sends the real part `x` of `z` to `−x/|z|²` (`re_S_smul`), so it exchanges the two
   open halves `Re z > 0` and `Re z < 0`; `U` and `U²` send the right half into the left (`re_U_smul_neg`,
   `re_U_sq_smul_neg`).
3. **Ping-pong** (§3). With `ℤ/2 ↦ s` and `ℤ/3 ↦ u` (`factorHom`, through `zmodHom`), the right half for `s` and the
   left half for `u` (`pingPongSet`) meet Mathlib's ping-pong lemma `Monoid.CoprodI.lift_injective_of_ping_pong`
   (`pingPong`, `card_factor`), so the map out of the free product is injective (`toPSL_injective`). It is onto
   because `T = S⁻¹(S T)` and `S`, `T` generate `SL(2, ℤ)` (`toPSL_surjective`, from Mathlib's
   `SpecialLinearGroup.SL2Z_generators`). Hence `freeProductEquiv : CoprodI Factor ≃* PSL(2, ℤ)`.
4. **The binary form** (§4). The indexed free product over `Fin 2` is Mathlib's binary `Monoid.Coprod` of its two
   factors (`coprodEquiv`; Mathlib lists this as a TODO in `GroupTheory/Coprod/Basic`), so
   `psl2zEquiv : Multiplicative (ZMod 2) ∗ Multiplicative (ZMod 3) ≃* PSL(2, ℤ)`, sending the two units to `s` and
   `u` (`psl2zEquiv_inl`, `psl2zEquiv_inr`).
5. **The join to `Geometry/Farey`** (§5). As moves of determinant one, `R = T = −S U` and `L = S T⁻¹ S⁻¹ = −S U²`
   (`sbRMove_eq_T`, `sbLMove_eq`, `sbRMove_eq_neg_S_mul_U`, `sbLMove_eq_neg_S_mul_U_sq`). So in `PSL(2, ℤ)` the right
   move is the word `s u` and the left move the word `s u²` (`proj_sbRMove`, `proj_sbLMove`): a Stern–Brocot path,
   a positive word in `L` and `R`, is the reduced word `s u^(e₁) s u^(e₂) ⋯` with every `eᵢ ∈ {1, 2}`, so the
   uniqueness of a ratio's path (`Compression/SternBrocotCode.node_injective`) is read here as the freeness of the
   product, at the grain of the positive words.
6. **The `(2, 3, ∞)` signature** (§6). `S U = −T`, so `s u = [T]` (`s_mul_u`), and `s u` has infinite order
   (`orderOf_s_mul_u`): the three moves `s`, `u`, `(s u)⁻¹`, whose product is one, have orders `2`, `3`, `∞`, the
   signature of the `(½, ⅓, 0)` triangle beside `Geometry/TriangleGroupHolon`'s finite triangle groups.
7. **Legendre's `Γ(2)`** (§7). The level-two subgroup (Mathlib's `CongruenceSubgroup.Gamma 2`, the moves congruent
   to one modulo two) holds `−1` (`neg_one_mem_Gamma_two`) and has index six (`index_Gamma_two`): reduction modulo
   two is onto `SL(2, 𝔽₂)`, whose six moves are the residues of `1, S, T, S T, T S, S T S`
   (`range_reduceTwo`, `mem_residueRepresentatives`, `card_residueRepresentatives`).

Limits. The box's later clauses are not proved here: the Schwarz map of the `(½, ⅓, 0)` triangle and the
identification of its monodromy with this group, `Γ(2)` as the monodromy of Legendre's family and its freeness on
`[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]` modulo `±1` (only its index and its sign are proved), and
`K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)`. The
action of `PSL(2, ℤ)` on `ℍ` is a local instance of this file (`pslAction`), not a global one. The ping-pong is
played on the two open halves of `ℍ` by real part, not on the irrationals of the real line. That the positive words
in `L` and `R` form a free monoid is not derived from `psl2zEquiv` here (it stands as path uniqueness in
`Compression/SternBrocotCode`); and the reduced-word normal form is used through Mathlib's ping-pong lemma, not
restated as a statement about `Monoid.CoprodI.Word`.

The computational object is the helical pair interaction: the moves of a contact's pair. The half-turn `s` is the
swing's half-turn in the projective chart (`z ↦ −1/z`, whose square is the whole turn `−1`), `u` is a third of a
turn, and `T = s u` the carry `z ↦ z + 1`; a word in `s` and `u` is a route, and its reduced form is its address.
Of the winding guide's six general objects this touches the helix (the turn `u`, whose cube is the whole turn, and
the carry `T`) and the pair (the half-turn `s` and the moves of determinant one), with faces and placement read on the
two halves of `ℍ` that the ping-pong separates; cell holonomy, the tube and the tower thread stay attached.

Consumers: #410's box on monodromy as a group of moves; `Geometry/Farey` (`sbL`, `sbR`, `cfProd`'s group);
`Compression/SternBrocotCode` (the Stern–Brocot path); `Geometry/TriangleGroupHolon` (the triangle signatures).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.ModularFreeProduct

open Matrix Matrix.SpecialLinearGroup ModularGroup UpperHalfPlane
open scoped MatrixGroups Pointwise

/-! ## 1. The two moves -/

/-- [definition] The third of a turn `U = S T = [[0, −1], [1, 1]]`, the Möbius move `z ↦ −1/(z + 1)`. -/
def U : SL(2, ℤ) := S * T

/-- [proved-standard] `U`'s matrix. -/
theorem coe_U : (U : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- [proved-standard] The half-turn's square is the whole turn: `S² = −1` in `SL(2, ℤ)`. -/
theorem S_sq : S ^ 2 = -1 := by decide

/-- [proved-standard] Three thirds of a turn are the whole turn: `U³ = −1` in `SL(2, ℤ)`. -/
theorem U_cube : U ^ 3 = -1 := by decide

/-- [proved-standard] Two thirds of a turn: `U² = T⁻¹ S`, the Möbius move `z ↦ −1 − 1/z`. -/
theorem U_sq : U ^ 2 = T⁻¹ * S := by decide

/-- [definition] The quotient of the moves of determinant one by their centre, onto Mathlib's `PSL(2, ℤ)`. -/
def proj : SL(2, ℤ) →* PSL(2, ℤ) := QuotientGroup.mk' _

/-- [definition] The half-turn `s = [S]` of `PSL(2, ℤ)`. -/
def s : PSL(2, ℤ) := proj S

/-- [definition] The third of a turn `u = [S T]` of `PSL(2, ℤ)`. -/
def u : PSL(2, ℤ) := proj U

/-- [proved-standard] The whole turn `−1` is central. -/
theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
  Subgroup.mem_center_iff.mpr fun g => by simp

/-- [proved-standard] A move is trivial in `PSL(2, ℤ)` exactly when it is central. -/
theorem proj_eq_one_iff (g : SL(2, ℤ)) : proj g = 1 ↔ g ∈ Subgroup.center SL(2, ℤ) :=
  QuotientGroup.eq_one_iff g

/-- [proved-standard] `s² = 1`. -/
theorem s_sq : s ^ 2 = 1 := by
  rw [s, ← map_pow, S_sq, proj_eq_one_iff]; exact neg_one_mem_center

/-- [proved-standard] `u³ = 1`. -/
theorem u_cube : u ^ 3 = 1 := by
  rw [u, ← map_pow, U_cube, proj_eq_one_iff]; exact neg_one_mem_center

/-- [proved-standard] `s ≠ 1`: `S` does not commute with `T`. -/
theorem s_ne_one : s ≠ 1 := by
  rw [s, Ne, proj_eq_one_iff, Subgroup.mem_center_iff]
  intro h
  have := h T
  revert this
  decide

/-- [proved-standard] `u ≠ 1`: `S T` does not commute with `T`. -/
theorem u_ne_one : u ≠ 1 := by
  rw [u, Ne, proj_eq_one_iff, Subgroup.mem_center_iff]
  intro h
  have := h T
  revert this
  decide

/-- [proved-standard] The half-turn has order two in `PSL(2, ℤ)`. -/
theorem orderOf_s : orderOf s = 2 := orderOf_eq_prime s_sq s_ne_one

/-- [proved-standard] The third of a turn has order three in `PSL(2, ℤ)`. -/
theorem orderOf_u : orderOf u = 3 := orderOf_eq_prime u_cube u_ne_one

/-! ## 2. The action on the upper half plane -/

/-- [proved-standard] The centre of `SL(2, ℤ)` is `±1`. -/
theorem center_eq_one_or_neg_one {g : SL(2, ℤ)} (hg : g ∈ Subgroup.center SL(2, ℤ)) :
    g = 1 ∨ g = -1 := by
  obtain ⟨r, hr, hgr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr' : r * r = 1 := by simpa [sq] using hr
  rcases mul_self_eq_one_iff.mp hr' with rfl | rfl
  · left; ext i j; simp [← hgr]
  · right; ext i j; simp [← hgr]

/-- [proved-standard] A central move fixes every point of the upper half plane. -/
theorem center_smul {g : SL(2, ℤ)} (hg : g ∈ Subgroup.center SL(2, ℤ)) (z : ℍ) :
    g • z = z := by
  rcases center_eq_one_or_neg_one hg with rfl | rfl
  · exact one_smul _ z
  · rw [SL_neg_smul, one_smul]

/-- [definition] The Möbius action of `SL(2, ℤ)` on `ℍ` as permutations. -/
def slToPerm : SL(2, ℤ) →* Equiv.Perm ℍ := MulAction.toPermHom SL(2, ℤ) ℍ

/-- [proved-standard] The centre acts trivially, so the action descends to `PSL(2, ℤ)`. -/
theorem center_le_ker : Subgroup.center SL(2, ℤ) ≤ slToPerm.ker := by
  intro g hg
  rw [MonoidHom.mem_ker]
  exact Equiv.ext fun z => center_smul hg z

/-- [definition] The descended action of `PSL(2, ℤ)` on `ℍ` as permutations. -/
def pslToPerm : PSL(2, ℤ) →* Equiv.Perm ℍ :=
  QuotientGroup.lift _ slToPerm center_le_ker

/-- [definition] `PSL(2, ℤ)` acting on `ℍ` (a local instance of this file). -/
@[instance_reducible] def pslAction : MulAction PSL(2, ℤ) ℍ := MulAction.compHom ℍ pslToPerm

attribute [local instance] pslAction

/-- [proved-standard] A class acts as any of its moves. -/
theorem proj_smul (g : SL(2, ℤ)) (z : ℍ) : proj g • z = g • z := rfl

/-- [proved-standard] The half-turn sends the real part `x` of `z` to `−x/|z|²`. -/
theorem re_S_smul (z : ℍ) : (S • z).re = -z.re / Complex.normSq (z : ℂ) := by
  rw [modular_S_smul]
  show ((-(z : ℂ))⁻¹).re = _
  rw [Complex.inv_re, Complex.normSq_neg, Complex.neg_re]
  rfl

/-- [proved-standard] A point of `ℍ` has positive squared modulus. -/
theorem normSq_pos (z : ℍ) : 0 < Complex.normSq (z : ℂ) :=
  Complex.normSq_pos.mpr z.ne_zero

/-- [proved-standard] The half-turn carries the left half of `ℍ` into the right half. -/
theorem re_S_smul_pos {z : ℍ} (hz : z.re < 0) : 0 < (S • z).re := by
  rw [re_S_smul]
  exact div_pos (by linarith) (normSq_pos z)

/-- [proved-standard] The half-turn carries the right half of `ℍ` into the left half. -/
theorem re_S_smul_neg {z : ℍ} (hz : 0 < z.re) : (S • z).re < 0 := by
  rw [re_S_smul]
  exact div_neg_of_neg_of_pos (by linarith) (normSq_pos z)

/-- [proved-standard] `U` carries the right half into the left half: `T` moves it right, `S` turns it over. -/
theorem re_U_smul_neg {z : ℍ} (hz : 0 < z.re) : (U • z).re < 0 := by
  rw [U, mul_smul]
  apply re_S_smul_neg
  rw [re_T_smul]; linarith

/-- [proved-standard] `U²` carries the right half into the left half: `S` turns it over, `T⁻¹` moves it further left. -/
theorem re_U_sq_smul_neg {z : ℍ} (hz : 0 < z.re) : ((U ^ 2) • z).re < 0 := by
  rw [U_sq, mul_smul]
  have h1 := re_S_smul_neg hz
  have h2 : (T⁻¹ • S • z).re = (S • z).re + ((-1 : ℤ) : ℝ) := by
    simpa using re_T_zpow_smul (S • z) (-1)
  rw [h2]
  push_cast
  linarith

/-! ## 3. The free product and its ping-pong -/

/-- [definition] The map of `ℤ/n` sending its unit to `g`, for `gⁿ = 1`. -/
def zmodHom {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift n ⟨zmultiplesHom (Additive G) (Additive.ofMul g), by
      show ((n : ℤ) • Additive.ofMul g) = 0
      rw [natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩)

/-- [proved-standard] The map sends the residue of `k` to `gᵏ`. -/
theorem zmodHom_ofAdd_natCast {G : Type*} [Group G] (n : ℕ) (g : G) (hg : g ^ n = 1)
    (k : ℕ) : zmodHom n g hg (Multiplicative.ofAdd (k : ZMod n)) = g ^ k := by
  simp only [zmodHom, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd]
  rw [← Int.cast_natCast (R := ZMod n) k, ZMod.lift_coe]
  show Additive.toMul ((k : ℤ) • Additive.ofMul g) = g ^ k
  rw [natCast_zsmul, ← ofMul_pow, toMul_ofMul]

/-- [definition] The two factors: `ℤ/2` at index `0` and `ℤ/3` at index `1`, written multiplicatively. -/
abbrev Factor (i : Fin 2) : Type := Multiplicative (ZMod (i.val + 2))

/-- [definition] The two moves, `s` at index `0` and `u` at index `1`. -/
def gen : Fin 2 → PSL(2, ℤ) := ![s, u]

/-- [proved-standard] Each move's order divides its factor's. -/
theorem gen_pow (i : Fin 2) : gen i ^ (i.val + 2) = 1 := by
  fin_cases i
  · exact s_sq
  · exact u_cube

/-- [definition] Each factor's map into `PSL(2, ℤ)`. -/
def factorHom (i : Fin 2) : Factor i →* PSL(2, ℤ) := zmodHom (i.val + 2) (gen i) (gen_pow i)

/-- [definition] The map out of the free product of the two factors. -/
def toPSL : Monoid.CoprodI Factor →* PSL(2, ℤ) := Monoid.CoprodI.lift factorHom

/-- [proved-standard] The nontrivial element of `ℤ/2` goes to `s`. -/
theorem factorHom_zero_of_ne_one (h : Factor 0) (hh : h ≠ 1) : factorHom 0 h = s := by
  have hk : ∀ k : ZMod 2, k ≠ 0 → k = 1 := by decide
  have h1 : Multiplicative.toAdd h = 1 := hk _ (by simpa using hh)
  have : h = Multiplicative.ofAdd ((1 : ℕ) : ZMod 2) :=
    Multiplicative.toAdd.injective (by simpa using h1)
  rw [this]
  exact (zmodHom_ofAdd_natCast 2 s s_sq 1).trans (pow_one s)

/-- [proved-standard] A nontrivial element of `ℤ/3` goes to `u` or `u²`. -/
theorem factorHom_one_of_ne_one (h : Factor 1) (hh : h ≠ 1) :
    factorHom 1 h = u ∨ factorHom 1 h = u ^ 2 := by
  have hk : ∀ k : ZMod 3, k ≠ 0 → k = 1 ∨ k = 2 := by decide
  rcases hk (Multiplicative.toAdd h) (by simpa using hh) with h1 | h1
  · left
    have : h = Multiplicative.ofAdd ((1 : ℕ) : ZMod 3) :=
      Multiplicative.toAdd.injective (by simpa using h1)
    rw [this]
    exact (zmodHom_ofAdd_natCast 3 u u_cube 1).trans (pow_one u)
  · right
    have : h = Multiplicative.ofAdd ((2 : ℕ) : ZMod 3) :=
      Multiplicative.toAdd.injective (by simpa using h1)
    rw [this]
    exact zmodHom_ofAdd_natCast 3 u u_cube 2

/-- [definition] The ping-pong sets: the right half of `ℍ` for `s`, the left half for `u`. -/
def pingPongSet : Fin 2 → Set ℍ := ![{z | 0 < z.re}, {z | z.re < 0}]

/-- [proved-standard] Both halves hold a point (`±1 + i`). -/
theorem pingPongSet_nonempty (i : Fin 2) : (pingPongSet i).Nonempty := by
  fin_cases i
  · refine ⟨⟨1 + Complex.I, by simp⟩, ?_⟩
    show (0 : ℝ) < (1 + Complex.I).re
    simp
  · refine ⟨⟨-1 + Complex.I, by simp⟩, ?_⟩
    show (-1 + Complex.I).re < 0
    simp

/-- [proved-standard] The two halves are disjoint. -/
theorem pingPongSet_disjoint : Pairwise (Function.onFun Disjoint pingPongSet) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact Set.disjoint_left.mpr fun z h1 h2 => lt_asymm (show 0 < z.re from h1) h2
  · exact Set.disjoint_left.mpr fun z h1 h2 => lt_asymm (show 0 < z.re from h2) h1
  · exact absurd rfl hij

/-- [proved-standard] `s` sends the left half into the right half. -/
theorem s_smul_left (z : ℍ) (hz : z.re < 0) : 0 < (s • z).re := by
  rw [s, proj_smul]; exact re_S_smul_pos hz

/-- [proved-standard] `u` sends the right half into the left half. -/
theorem u_smul_right (z : ℍ) (hz : 0 < z.re) : (u • z).re < 0 := by
  rw [u, proj_smul]; exact re_U_smul_neg hz

/-- [proved-standard] `u²` sends the right half into the left half. -/
theorem u_sq_smul_right (z : ℍ) (hz : 0 < z.re) : ((u ^ 2) • z).re < 0 := by
  rw [u, ← map_pow, proj_smul]; exact re_U_sq_smul_neg hz

/-- [proved-standard] The ping-pong condition for the factor `ℤ/2`. -/
theorem pingPong_s (h : Factor 0) (hh : h ≠ 1) :
    factorHom 0 h • pingPongSet 1 ⊆ pingPongSet 0 := by
  rw [factorHom_zero_of_ne_one h hh, Set.smul_set_subset_iff]
  intro z hz
  exact s_smul_left z hz

/-- [proved-standard] The ping-pong condition for the factor `ℤ/3`. -/
theorem pingPong_u (h : Factor 1) (hh : h ≠ 1) :
    factorHom 1 h • pingPongSet 0 ⊆ pingPongSet 1 := by
  rw [Set.smul_set_subset_iff]
  intro z hz
  rcases factorHom_one_of_ne_one h hh with he | he <;> rw [he]
  · exact u_smul_right z hz
  · exact u_sq_smul_right z hz

/-- [proved-standard] The ping-pong condition of `Monoid.CoprodI.lift_injective_of_ping_pong`, for both pairs of factors. -/
theorem pingPong :
    Pairwise fun i j => ∀ h : Factor i, h ≠ 1 → factorHom i h • pingPongSet j ⊆ pingPongSet i := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact pingPong_s
  · exact pingPong_u
  · exact absurd rfl hij

/-- [proved-standard] One factor has at least three elements, as the ping-pong lemma asks for two factors. -/
theorem card_factor : 3 ≤ Cardinal.mk (Fin 2) ∨ ∃ i, 3 ≤ Cardinal.mk (Factor i) := by
  right
  refine ⟨1, ?_⟩
  show (3 : Cardinal) ≤ Cardinal.mk (Multiplicative (ZMod 3))
  rw [Cardinal.mk_fintype]
  simp

/-- [proved-standard] **No reduced word in `s` and `u` is trivial**: the map out of the free product is injective (ping-pong). -/
theorem toPSL_injective : Function.Injective toPSL :=
  Monoid.CoprodI.lift_injective_of_ping_pong factorHom card_factor pingPongSet
    pingPongSet_nonempty pingPongSet_disjoint pingPong

/-- [proved-standard] `s` is in the image. -/
theorem s_mem_range : s ∈ toPSL.range :=
  ⟨Monoid.CoprodI.of (i := 0) (Multiplicative.ofAdd ((1 : ℕ) : ZMod 2)), by
    rw [toPSL, Monoid.CoprodI.lift_of]
    exact (zmodHom_ofAdd_natCast 2 s s_sq 1).trans (pow_one s)⟩

/-- [proved-standard] `u` is in the image. -/
theorem u_mem_range : u ∈ toPSL.range :=
  ⟨Monoid.CoprodI.of (i := 1) (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3)), by
    rw [toPSL, Monoid.CoprodI.lift_of]
    exact (zmodHom_ofAdd_natCast 3 u u_cube 1).trans (pow_one u)⟩

/-- [proved-standard] **Every class is a word in `s` and `u`**: `T = S⁻¹ (S T)`, and `S`, `T` generate `SL(2, ℤ)` (Mathlib's `SL2Z_generators`). -/
theorem toPSL_surjective : Function.Surjective toPSL := by
  have hS : S ∈ toPSL.range.comap proj := s_mem_range
  have hT : T ∈ toPSL.range.comap proj := by
    have : T = S⁻¹ * U := by rw [U, inv_mul_cancel_left]
    rw [Subgroup.mem_comap, this, map_mul, map_inv]
    exact mul_mem (inv_mem s_mem_range) u_mem_range
  have hle : Subgroup.closure {S, T} ≤ toPSL.range.comap proj :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hS, Set.singleton_subset_iff.mpr hT⟩)
  rw [SpecialLinearGroup.SL2Z_generators] at hle
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact hle (Subgroup.mem_top g)

/-- [proved-standard] **`PSL(2, ℤ)` is the free product of `ℤ/2` and `ℤ/3`** (indexed form). -/
def freeProductEquiv : Monoid.CoprodI Factor ≃* PSL(2, ℤ) :=
  MulEquiv.ofBijective toPSL ⟨toPSL_injective, toPSL_surjective⟩

/-! ## 4. The binary free product `ℤ/2 ∗ ℤ/3` -/

/-- [definition] The binary free product into the indexed one. -/
def coprodToCoprodI : Monoid.Coprod (Factor 0) (Factor 1) →* Monoid.CoprodI Factor :=
  Monoid.Coprod.lift (Monoid.CoprodI.of (i := 0)) (Monoid.CoprodI.of (i := 1))

/-- [definition] The indexed free product into the binary one. -/
def coprodIToCoprod : Monoid.CoprodI Factor →* Monoid.Coprod (Factor 0) (Factor 1) :=
  Monoid.CoprodI.lift fun i =>
    Fin.cases (motive := fun i => Factor i →* Monoid.Coprod (Factor 0) (Factor 1))
      Monoid.Coprod.inl
      (fun j => Fin.cases (motive := fun j : Fin 1 =>
          Factor j.succ →* Monoid.Coprod (Factor 0) (Factor 1))
        Monoid.Coprod.inr (fun k => k.elim0) j) i

/-- [proved-standard] One composite is the identity. -/
theorem coprodIToCoprod_comp_coprodToCoprodI :
    coprodIToCoprod.comp coprodToCoprodI = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext x
    simp [coprodIToCoprod, coprodToCoprodI, Monoid.CoprodI.lift_of]
  · ext x
    rfl

/-- [proved-standard] The other composite is the identity. -/
theorem coprodToCoprodI_comp_coprodIToCoprod :
    coprodToCoprodI.comp coprodIToCoprod = MonoidHom.id _ := by
  apply Monoid.CoprodI.ext_hom
  intro i
  fin_cases i
  · ext x
    simp [coprodIToCoprod, coprodToCoprodI, Monoid.CoprodI.lift_of]
  · ext x
    exact Monoid.Coprod.lift_apply_inr (M := Factor 0) (N := Factor 1)
      (Monoid.CoprodI.of (i := 0)) (Monoid.CoprodI.of (i := 1)) _

/-- [proved-standard] The binary and the indexed free products of the two factors are one group (a case of Mathlib's open TODO in `GroupTheory/Coprod/Basic`). -/
def coprodEquiv : Monoid.Coprod (Factor 0) (Factor 1) ≃* Monoid.CoprodI Factor :=
  MonoidHom.toMulEquiv coprodToCoprodI coprodIToCoprod
    coprodIToCoprod_comp_coprodToCoprodI coprodToCoprodI_comp_coprodIToCoprod

/-- [proved-standard] **`ℤ/2 ∗ ℤ/3 ≅ PSL(2, ℤ)`**, with Mathlib's binary free product `Monoid.Coprod`. -/
def psl2zEquiv :
    Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 3)) ≃* PSL(2, ℤ) :=
  coprodEquiv.trans freeProductEquiv

/-- [proved-standard] The unit of `ℤ/2` goes to the half-turn `s`. -/
theorem psl2zEquiv_inl :
    psl2zEquiv (Monoid.Coprod.inl (Multiplicative.ofAdd 1)) = s := by
  show toPSL (coprodToCoprodI (Monoid.Coprod.inl (Multiplicative.ofAdd ((1 : ℕ) : ZMod 2)))) = s
  rw [coprodToCoprodI, Monoid.Coprod.lift_apply_inl, toPSL, Monoid.CoprodI.lift_of]
  exact (zmodHom_ofAdd_natCast 2 s s_sq 1).trans (pow_one s)

/-- [proved-standard] The unit of `ℤ/3` goes to the third of a turn `u`. -/
theorem psl2zEquiv_inr :
    psl2zEquiv (Monoid.Coprod.inr (Multiplicative.ofAdd 1)) = u := by
  show toPSL (coprodToCoprodI (Monoid.Coprod.inr (Multiplicative.ofAdd ((1 : ℕ) : ZMod 3)))) = u
  rw [coprodToCoprodI, Monoid.Coprod.lift_apply_inr, toPSL, Monoid.CoprodI.lift_of]
  exact (zmodHom_ofAdd_natCast 3 u u_cube 1).trans (pow_one u)

/-! ## 5. The join to `Geometry/Farey`: the Stern–Brocot moves are words in `s` and `u` -/

/-- [definition] The Stern–Brocot right move `R` of `Geometry/Farey` as a move of determinant one. -/
def sbRMove : SL(2, ℤ) := ⟨Holonics.Geometry.Farey.sbR, Holonics.Geometry.Farey.theGeneratorsAreUnimodular.2⟩

/-- [definition] The Stern–Brocot left move `L` of `Geometry/Farey` as a move of determinant one. -/
def sbLMove : SL(2, ℤ) := ⟨Holonics.Geometry.Farey.sbL, Holonics.Geometry.Farey.theGeneratorsAreUnimodular.1⟩

/-- [proved-derived] `R` is Mathlib's `T`. -/
theorem sbRMove_eq_T : sbRMove = T := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

/-- [proved-derived] `L` is `T⁻¹` conjugated by the half-turn: `L = S T⁻¹ S⁻¹`. -/
theorem sbLMove_eq : sbLMove = S * T⁻¹ * S⁻¹ := by decide

/-- [proved-derived] `R = −S U`. -/
theorem sbRMove_eq_neg_S_mul_U : sbRMove = -(S * U) := by decide

/-- [proved-derived] `L = −S U²`. -/
theorem sbLMove_eq_neg_S_mul_U_sq : sbLMove = -(S * U ^ 2) := by decide

/-- [proved-standard] A move and its negative are one class. -/
theorem proj_neg (g : SL(2, ℤ)) : proj (-g) = proj g := by
  rw [show -g = (-1) * g by simp, map_mul, (proj_eq_one_iff _).mpr neg_one_mem_center, one_mul]

/-- [proved-derived] **The right move is the word `s u`.** -/
theorem proj_sbRMove : proj sbRMove = s * u := by
  rw [sbRMove_eq_neg_S_mul_U, proj_neg, map_mul]; rfl

/-- [proved-derived] **The left move is the word `s u²`.** -/
theorem proj_sbLMove : proj sbLMove = s * u ^ 2 := by
  rw [sbLMove_eq_neg_S_mul_U_sq, proj_neg, map_mul, map_pow]; rfl

/-! ## 6. The `(2, 3, ∞)` signature -/

/-- [proved-standard] `S U = −T`. -/
theorem S_mul_U : S * U = -T := by decide

/-- [proved-standard] `s u = [T]`. -/
theorem s_mul_u : s * u = proj T := by
  rw [s, u, ← map_mul, S_mul_U, proj_neg]

/-- [proved-standard] `Tⁿ` is central only at `n = 0`. -/
theorem T_pow_mem_center_iff (n : ℕ) : T ^ n ∈ Subgroup.center SL(2, ℤ) ↔ n = 0 := by
  constructor
  · intro h
    have h01 : ((T ^ (n : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = n := by
      rw [coe_T_zpow]; simp
    rw [zpow_natCast] at h01
    rcases center_eq_one_or_neg_one h with he | he <;> rw [he] at h01 <;> simp at h01 <;> omega
  · rintro rfl
    rw [pow_zero]
    exact Subgroup.one_mem _

/-- [proved-standard] **The third vertex of the `(2, 3, ∞)` triangle**: `s u = [T]` has infinite order, beside the orders two and three of `s` and `u`. -/
theorem orderOf_s_mul_u : orderOf (s * u) = 0 := by
  rw [orderOf_eq_zero_iff', s_mul_u]
  intro n hn h
  rw [← map_pow, proj_eq_one_iff, T_pow_mem_center_iff] at h
  omega

/-! ## 7. Legendre's level-two subgroup `Γ(2)` -/

/-- [definition] The reduction of a move of determinant one modulo two (Mathlib's `SLMOD(2)`). -/
abbrev reduceTwo : SL(2, ℤ) →* SL(2, ZMod 2) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2))

/-- [proved-standard] The whole turn `−1` lies in `Γ(2)`, so `Γ(2)` is read in `PSL(2, ℤ)` with its sign. -/
theorem neg_one_mem_Gamma_two : (-1 : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]; decide

/-- [definition] Six moves whose residues modulo two are the six moves of `SL(2, 𝔽₂)`. -/
def residueRepresentatives : Finset SL(2, ZMod 2) :=
  {reduceTwo 1, reduceTwo S, reduceTwo T, reduceTwo (S * T), reduceTwo (T * S), reduceTwo (S * T * S)}

set_option maxRecDepth 100000 in
/-- [proved-standard] Every move of determinant one over `𝔽₂` is one of the six residues. -/
theorem mem_residueRepresentatives (x : SL(2, ZMod 2)) : x ∈ residueRepresentatives := by
  revert x; decide

set_option maxRecDepth 100000 in
/-- [proved-standard] The six residues are distinct. -/
theorem card_residueRepresentatives : residueRepresentatives.card = 6 := by decide

/-- [proved-standard] Reduction modulo two is onto `SL(2, 𝔽₂)`, which has six moves. -/
theorem range_reduceTwo : (Set.range reduceTwo) = ↑residueRepresentatives := by
  ext x
  constructor
  · rintro -
    exact mem_residueRepresentatives x
  · intro hx
    simp only [residueRepresentatives, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩

/-- [proved-standard] **`Γ(2)` has index six in `SL(2, ℤ)`**: the quotient is `SL(2, 𝔽₂)`, the permutations of
the three nonzero points of `𝔽₂²`. -/
theorem index_Gamma_two : (CongruenceSubgroup.Gamma 2).index = 6 := by
  show (reduceTwo.ker).index = 6
  have h : (reduceTwo.range : Set SL(2, ZMod 2)) = ↑residueRepresentatives := by
    rw [MonoidHom.coe_range, range_reduceTwo]
  rw [Subgroup.index_ker, ← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    card_residueRepresentatives]

end Holonics.Geometry.ModularFreeProduct

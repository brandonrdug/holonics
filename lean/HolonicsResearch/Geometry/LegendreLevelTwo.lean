import HolonicsResearch.Geometry.ModularFreeProduct

/-!
# Legendre's level two is free on two carries: `Γ(2)/±1` is free on `[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]`

Source: #410's box "Monodromy as a group of moves", its clause "Legendre's `Γ(2)`": `Geometry/ModularFreeProduct`
proved that the level-two group holds `−1` and has index six, and left owed `Γ(2)` as Legendre's monodromy and its
freeness on `[[1, 2], [0, 1]]` and `[[1, 0], [2, 1]]` modulo `±1`. This file proves the freeness and the generation
(Sanov's theorem with its descent).

[proved-standard; formal-checked] What is proved.

1. **The two carries** (§1). `A = [[1, 2], [0, 1]]` (`z ↦ z + 2`) and `B = [[1, 0], [2, 1]]` (`z ↦ z/(2z + 1)`)
   lie in `Γ(2)` (`A_mem`, `B_mem`), and their powers are `Aⁿ = [[1, 2n], [0, 1]]`, `Bⁿ = [[1, 0], [2n, 1]]`
   (`coe_A_zpow`, `coe_B_zpow`).
2. **Ping-pong** (§2). On the integer plane, `Aⁿ` (`n ≠ 0`) sends the steep vectors `|x| < |y|` to the shallow ones
   `|y| < |x|`, and `Bⁿ` sends the shallow to the steep (`A_zpow_smul`, `B_zpow_smul`), so Mathlib's ping-pong lemma
   for free products makes the word map `F₂ → SL(2, ℤ)`, `a ↦ A`, `b ↦ B`, injective (`sanov_injective`, Sanov).
3. **No word is `−1`** (§3). Every word in `A` and `B` is `≡ [[1, 0], [0, 1]]` on the diagonal modulo four and even
   off it (`levelFour`, `sanov_mem_levelFour`), and `−1` is not (`neg_one_not_mem_levelFour`); so the word map stays
   injective into `PSL(2, ℤ)` (`sanov_psl_injective`).
4. **The descent** (§4). Every `g ∈ Γ(2)` is `±` a word in `A` and `B` (`exists_sanov_eq`): the lower-left entry `c`
   is even and the upper-left `a` odd, a power of `A` brings `a` within `|c|`, strictly by parity, a power of `B`
   brings `c` within the new `|a|`, again strictly, and `|c|` falls to `0`, where `g = ±Aᵐ` (`exists_near`,
   `parity_of_mem`, `isSignedWord_of_mem_aux`).
5. **The level-two group as a free group** (§5). `Γ(2) = ⟨A, B, −1⟩` read in `PSL(2, ℤ)`: the image of `Γ(2)` is
   the range of the word map (`map_Gamma_two_eq_range`), and `gammaTwoFree : F₂ ≃* Γ(2)/±1`.

Limits. That `Γ(2)` is the monodromy of Legendre's family `y² = x(x − 1)(x − λ)` (the periods' continuation round
`λ = 0` and `λ = 1`) is not proved here, nor the Schwarz map of the `(½, ⅓, 0)` triangle or `K(√λ)`; this file
gives the group that monodromy is claimed to be, as a free group on the two loops' moves `A` and `B`. The local
data that fix it (Riemann's scheme, the logarithm at the double exponent, and the rigidity that conjugates any
pair with those data to `(A, B⁻¹)`) stand in `Geometry/HypergeometricMonodromy`, with the periods' continuation
cited. The ping-pong
is played on the integer plane by the two open cones `|x| < |y|` and `|y| < |x|`, not on the real projective line.

The computational object is the helical pair interaction: `A` is the carry `z ↦ z + 2` round one puncture and `B`
its conjugate round the other, a word in them is a route, and freeness says that two routes with different reduced
words never close the same loop. Of the winding guide's six general objects this touches the helix (the carry),
the cell holonomy (the moves round the punctures) and faces and placement (the two cones); the pair, the tube and
the tower thread stay attached.

Consumers: the atlas row `lock.gamma-two-index` and the #410 box "Monodromy as a group of moves".

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix MatrixGroups

namespace Holonics.Geometry.LegendreLevelTwo

open Holonics.Geometry.ModularFreeProduct

/-! ## 1. The two carries -/

/-- [definition] `A = [[1, 2], [0, 1]]`, the carry `z ↦ z + 2`. -/
def A : SL(2, ℤ) := ⟨!![1, 2; 0, 1], by norm_num [Matrix.det_fin_two]⟩

/-- [definition] `B = [[1, 0], [2, 1]]`, the carry `z ↦ z/(2z + 1)`. -/
def B : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by norm_num [Matrix.det_fin_two]⟩

/-- [proved-standard; formal-checked] `A` as a matrix. -/
theorem coe_A : (A : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2; 0, 1] := rfl

/-- [proved-standard; formal-checked] `B` as a matrix. -/
theorem coe_B : (B : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2, 1] := rfl

/-- [proved-standard; formal-checked] `Aⁿ = [[1, 2n], [0, 1]]`. -/
theorem coe_A_zpow (n : ℤ) : ((A ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 2 * n; 0, 1] := by
  induction n using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> rfl
  | succ k ih =>
    rw [_root_.zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, coe_A]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  | pred k ih =>
    rw [_root_.zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_A]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- [proved-standard; formal-checked] `Bⁿ = [[1, 0], [2n, 1]]`. -/
theorem coe_B_zpow (n : ℤ) : ((B ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 2 * n, 1] := by
  induction n using Int.induction_on with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> rfl
  | succ k ih =>
    rw [_root_.zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, ih, coe_B]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  | pred k ih =>
    rw [_root_.zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, coe_B]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

/-- [proved-standard; formal-checked] `A ∈ Γ(2)`. -/
theorem A_mem : A ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]; decide

/-- [proved-standard; formal-checked] `B ∈ Γ(2)`. -/
theorem B_mem : B ∈ CongruenceSubgroup.Gamma 2 := by
  rw [CongruenceSubgroup.Gamma_mem]; decide

/-! ## 2. Ping-pong -/

/-- [definition] The word map `F₂ → SL(2, ℤ)`, `a ↦ A`, `b ↦ B`. -/
def sanov : FreeGroup (Fin 2) →* SL(2, ℤ) := FreeGroup.lift ![A, B]

/-- [definition] The two cones of the integer plane: shallow `|y| < |x|` for `A`, steep `|x| < |y|` for `B`. -/
def cone : Fin 2 → Set (Fin 2 → ℤ) := ![{v | |v 1| < |v 0|}, {v | |v 0| < |v 1|}]

/-- [proved-standard; formal-checked] `Aⁿ` (`n ≠ 0`) sends a steep vector to a shallow one. -/
theorem A_zpow_smul {n : ℤ} (hn : n ≠ 0) {v : Fin 2 → ℤ} (hv : |v 0| < |v 1|) :
    |(A ^ n • v) 1| < |(A ^ n • v) 0| := by
  have h0 : (A ^ n • v) 0 = v 0 + 2 * n * v 1 := by
    change (((A ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 = _
    rw [coe_A_zpow]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (A ^ n • v) 1 = v 1 := by
    change (((A ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1 = _
    rw [coe_A_zpow]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  have hn1 : 1 ≤ |n| := Int.one_le_abs hn
  have hk : |2 * n * v 1| = 2 * |n| * |v 1| := by rw [abs_mul, abs_mul]; norm_num
  have htri : |2 * n * v 1| ≤ |v 0 + 2 * n * v 1| + |v 0| := by
    have := abs_sub (v 0 + 2 * n * v 1) (v 0)
    rwa [add_sub_cancel_left] at this
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]

/-- [proved-standard; formal-checked] `Bⁿ` (`n ≠ 0`) sends a shallow vector to a steep one. -/
theorem B_zpow_smul {n : ℤ} (hn : n ≠ 0) {v : Fin 2 → ℤ} (hv : |v 1| < |v 0|) :
    |(B ^ n • v) 0| < |(B ^ n • v) 1| := by
  have h0 : (B ^ n • v) 0 = v 0 := by
    change (((B ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 0 = _
    rw [coe_B_zpow]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h1 : (B ^ n • v) 1 = 2 * n * v 0 + v 1 := by
    change (((B ^ n : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ v) 1 = _
    rw [coe_B_zpow]; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h0, h1]
  have hn1 : 1 ≤ |n| := Int.one_le_abs hn
  have hk : |2 * n * v 0| = 2 * |n| * |v 0| := by rw [abs_mul, abs_mul]; norm_num
  have htri : |2 * n * v 0| ≤ |2 * n * v 0 + v 1| + |v 1| := by
    have := abs_sub (2 * n * v 0 + v 1) (v 1)
    rwa [add_sub_cancel_right] at this
  nlinarith [abs_nonneg (v 0), abs_nonneg (v 1)]

/-- [proved-standard; formal-checked] **Sanov's theorem**: the word map in `A` and `B` is injective, so `A` and
`B` generate a free group of rank two. -/
theorem sanov_injective : Function.Injective sanov := by
  have hfac : sanov = (Monoid.CoprodI.lift fun i => FreeGroup.lift fun _ : Unit => ![A, B] i).comp
      (@freeGroupEquivCoprodI (Fin 2)).toMonoidHom := by
    ext i
    simp [sanov]
  rw [hfac, MonoidHom.coe_comp]
  refine Function.Injective.comp ?_ (MulEquiv.injective freeGroupEquivCoprodI)
  refine Monoid.CoprodI.lift_injective_of_ping_pong _ ?_ cone ?_ ?_ ?_
  · right
    refine ⟨0, ?_⟩
    rw [Cardinal.mk_congr FreeGroup.freeGroupUnitEquivInt, Cardinal.mk_int]
    exact_mod_cast (Cardinal.natCast_lt_aleph0 (n := 3)).le
  · intro i
    fin_cases i
    · exact ⟨![1, 0], show |(0 : ℤ)| < |(1 : ℤ)| by decide⟩
    · exact ⟨![0, 1], show |(0 : ℤ)| < |(1 : ℤ)| by decide⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change Disjoint {v : Fin 2 → ℤ | |v 1| < |v 0|} {v | |v 0| < |v 1|}
      rw [Set.disjoint_left]
      intro v h1 h2
      exact lt_asymm (show |v 1| < |v 0| from h1) (show |v 0| < |v 1| from h2)
    · change Disjoint {v : Fin 2 → ℤ | |v 0| < |v 1|} {v | |v 1| < |v 0|}
      rw [Set.disjoint_left]
      intro v h1 h2
      exact lt_asymm (show |v 0| < |v 1| from h1) (show |v 1| < |v 0| from h2)
    · exact absurd rfl hij
  · intro i j hij h hh
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, FreeGroup.of () ^ n = h :=
      ⟨FreeGroup.freeGroupUnitEquivInt h, FreeGroup.freeGroupUnitEquivInt.symm_apply_apply h⟩
    have hn : n ≠ 0 := by rintro rfl; exact hh (zpow_zero _)
    rw [map_zpow, FreeGroup.lift_apply_of]
    rintro _ ⟨v, hv, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change |v 0| < |v 1| at hv
      exact A_zpow_smul hn hv
    · change |v 1| < |v 0| at hv
      exact B_zpow_smul hn hv
    · exact absurd rfl hij

/-! ## 3. No word is `−1` -/

/-- [definition] The moves `≡ 1` on the diagonal modulo four and even off it. -/
def levelFour : Subgroup SL(2, ℤ) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ≡ 1 [ZMOD 4] ∧
    (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 ≡ 1 [ZMOD 4] ∧ 2 ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
    2 ∣ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0}
  one_mem' := by simp
  mul_mem' := by
    rintro g h ⟨g0, g1, g2, g3⟩ ⟨h0, h1, h2, h3⟩
    have d4 : ∀ x y : ℤ, 2 ∣ x → 2 ∣ y → x * y ≡ 0 [ZMOD 4] := by
      rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
      exact (Int.modEq_zero_iff_dvd).2 ⟨a * b, by ring⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using (g0.mul h0).add (d4 _ _ g2 h3)
    · simpa using (d4 _ _ g3 h2).add (g1.mul h1)
    · exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_left g2 _)
    · exact dvd_add (dvd_mul_of_dvd_left g3 _) (dvd_mul_of_dvd_right h3 _)
  inv_mem' := by
    rintro g ⟨g0, g1, g2, g3⟩
    simp only [Set.mem_ofPred_eq, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    exact ⟨g1, g0, (dvd_neg).2 g2, (dvd_neg).2 g3⟩

/-- [proved-standard; formal-checked] Every word in `A` and `B` lies in the level-four set. -/
theorem sanov_mem_levelFour (w : FreeGroup (Fin 2)) : sanov w ∈ levelFour := by
  induction w using FreeGroup.induction_on with
  | C1 => exact levelFour.one_mem
  | of i =>
    rw [sanov, FreeGroup.lift_apply_of]
    fin_cases i
    · exact ⟨by decide, by decide, by decide, by decide⟩
    · exact ⟨by decide, by decide, by decide, by decide⟩
  | inv_of i h => rw [map_inv]; exact levelFour.inv_mem h
  | mul x y hx hy => rw [map_mul]; exact levelFour.mul_mem hx hy

/-- [proved-standard; formal-checked] `−1` is not in the level-four set: its corner is `−1 ≢ 1` modulo four. -/
theorem neg_one_not_mem_levelFour : (-1 : SL(2, ℤ)) ∉ levelFour := by
  rintro ⟨h, -⟩
  have : ((-1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = -1 := by simp
  rw [this] at h
  exact absurd h (by decide)

/-- [proved-standard; formal-checked] **Free modulo `±1`**: the word map stays injective into `PSL(2, ℤ)`. -/
theorem sanov_psl_injective : Function.Injective (proj.comp sanov) := by
  rw [injective_iff_map_eq_one]
  intro w hw
  rw [MonoidHom.comp_apply, proj_eq_one_iff] at hw
  rcases center_eq_one_or_neg_one hw with h | h
  · exact sanov_injective (h.trans (map_one sanov).symm)
  · exact absurd (h ▸ sanov_mem_levelFour w) neg_one_not_mem_levelFour

/-! ## 4. The descent -/

/-- [proved-standard; formal-checked] Division with a signed remainder: some `a + 2kc` lies within `|c|`. -/
theorem exists_near (a c : ℤ) (hc : c ≠ 0) : ∃ k : ℤ, |a + 2 * k * c| ≤ |c| := by
  have hm : 2 * c ≠ 0 := mul_ne_zero two_ne_zero hc
  have hd := Int.mul_ediv_add_emod a (2 * c)
  have h0 := Int.emod_nonneg a hm
  have hlt := Int.emod_lt a hm
  have habs : ((2 * c).natAbs : ℤ) = 2 * |c| := by
    rw [Int.natCast_natAbs, abs_mul]; norm_num
  rw [habs] at hlt
  set r := a % (2 * c)
  set q := a / (2 * c)
  by_cases h1 : r ≤ |c|
  · refine ⟨-q, ?_⟩
    have : a + 2 * -q * c = r := by linear_combination -hd
    rw [this, abs_of_nonneg h0]
    exact h1
  · push Not at h1
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · refine ⟨-q + 1, ?_⟩
      have : a + 2 * (-q + 1) * c = r + 2 * c := by linear_combination -hd
      rw [this, abs_le]
      rw [abs_of_neg hneg] at h1 hlt ⊢
      constructor <;> linarith
    · refine ⟨-q - 1, ?_⟩
      have : a + 2 * (-q - 1) * c = r - 2 * c := by linear_combination -hd
      rw [this, abs_le]
      rw [abs_of_pos hpos] at h1 hlt ⊢
      constructor <;> linarith

/-- [proved-standard; formal-checked] On `Γ(2)` the diagonal is odd and the off-diagonal even. -/
theorem parity_of_mem {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma 2) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 % 2 = 1 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 % 2 = 0 ∧
      (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 % 2 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 % 2 = 1 := by
  rw [CongruenceSubgroup.Gamma_mem] at hg
  obtain ⟨h0, h1, h2, h3⟩ := hg
  have e1 : ∀ x : ℤ, ((x : ZMod 2) = 1) → x % 2 = 1 := by
    intro x hx
    have : ((x : ℤ) : ZMod 2) = ((1 : ℤ) : ZMod 2) := by rw [hx]; simp
    exact (ZMod.intCast_eq_intCast_iff x 1 2).1 this
  have e0 : ∀ x : ℤ, ((x : ZMod 2) = 0) → x % 2 = 0 := by
    intro x hx
    exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 hx)
  exact ⟨e1 _ h0, e0 _ h1, e0 _ h2, e1 _ h3⟩

/-- [proved-standard; formal-checked] A power of `A` moves the upper-left entry by `2kc` and keeps the lower-left. -/
theorem A_zpow_mul_apply (k : ℤ) (g : SL(2, ℤ)) :
    ((A ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + 2 * k * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
      ((A ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_A_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] A power of `B` keeps the upper-left entry and moves the lower-left by `2ka`. -/
theorem B_zpow_mul_apply (k : ℤ) (g : SL(2, ℤ)) :
    ((B ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
      ((B ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 + 2 * k * (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_B_zpow]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- [definition] `g` is `±` a word in `A` and `B`. -/
def IsSignedWord (g : SL(2, ℤ)) : Prop := ∃ w, sanov w = g ∨ sanov w = -g

/-- [proved-standard; formal-checked] The word `aᵏ` is `Aᵏ`. -/
theorem sanov_of_zero_zpow (k : ℤ) : sanov (FreeGroup.of 0 ^ k) = A ^ k := by
  rw [map_zpow, sanov, FreeGroup.lift_apply_of]; rfl

/-- [proved-standard; formal-checked] The word `bᵏ` is `Bᵏ`. -/
theorem sanov_of_one_zpow (k : ℤ) : sanov (FreeGroup.of 1 ^ k) = B ^ k := by
  rw [map_zpow, sanov, FreeGroup.lift_apply_of]; rfl

/-- [proved-standard; formal-checked] A signed word stays one under a left factor that is a word. -/
theorem isSignedWord_of_mul {x g : SL(2, ℤ)} {u : FreeGroup (Fin 2)} (hu : sanov u = x)
    (h : IsSignedWord (x * g)) : IsSignedWord g := by
  obtain ⟨w, hw | hw⟩ := h
  · exact ⟨u⁻¹ * w, Or.inl (by rw [map_mul, map_inv, hu, hw, inv_mul_cancel_left])⟩
  · exact ⟨u⁻¹ * w, Or.inr (by rw [map_mul, map_inv, hu, hw, mul_neg, inv_mul_cancel_left])⟩

/-- [proved-standard; formal-checked] Two integers of opposite parity have different sizes. -/
theorem abs_ne_of_parity {x y : ℤ} (hx : x % 2 = 1) (hy : y % 2 = 0) : |x| ≠ |y| := by
  intro h
  rcases abs_eq_abs.1 h with h | h <;> omega

/-- [proved-standard; formal-checked] **The descent**: every move of `Γ(2)` is `±` a word in `A` and `B`. -/
theorem isSignedWord_of_mem_aux :
    ∀ (N : ℕ) (g : SL(2, ℤ)), g ∈ CongruenceSubgroup.Gamma 2 →
      ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0).natAbs = N → IsSignedWord g := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro g hg hN
  obtain ⟨pa, pb, pc, pd⟩ := parity_of_mem hg
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0
  · -- the base: `g = ±Aᵐ`
    have hdet := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    obtain ⟨m, hm⟩ : ∃ m, (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 2 * m :=
      ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 / 2, by omega⟩
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨FreeGroup.of 0 ^ m, Or.inl ?_⟩
      rw [sanov_of_zero_zpow]
      ext i j
      rw [coe_A_zpow]
      fin_cases i <;> fin_cases j <;> simp [h1, h2, hm, hc]
    · refine ⟨FreeGroup.of 0 ^ (-m), Or.inr ?_⟩
      rw [sanov_of_zero_zpow]
      ext i j
      rw [coe_A_zpow, Matrix.SpecialLinearGroup.coe_neg]
      fin_cases i <;> fin_cases j <;> simp [h1, h2, hm, hc]
  · -- a power of `A` brings `a` within `|c|`, then a power of `B` brings `c` within the new `|a|`
    obtain ⟨k, hk⟩ := exists_near _ _ hc
    have hg1 : A ^ k * g ∈ CongruenceSubgroup.Gamma 2 :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ A_mem k) hg
    obtain ⟨e10, e11⟩ := A_zpow_mul_apply k g
    obtain ⟨qa, -, qc, -⟩ := parity_of_mem hg1
    set a1 := ((A ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    have hlt1 : |a1| < |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| := by
      have hle : |a1| ≤ |(g : Matrix (Fin 2) (Fin 2) ℤ) 1 0| := by rw [e10]; exact hk
      exact lt_of_le_of_ne hle (abs_ne_of_parity qa pc)
    have ha1 : a1 ≠ 0 := by intro h; rw [h] at qa; simp at qa
    obtain ⟨k', hk'⟩ := exists_near (((A ^ k * g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) a1 ha1
    have hg2 : B ^ k' * (A ^ k * g) ∈ CongruenceSubgroup.Gamma 2 :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem _ B_mem k') hg1
    obtain ⟨f00, f10⟩ := B_zpow_mul_apply k' (A ^ k * g)
    obtain ⟨-, -, rc, -⟩ := parity_of_mem hg2
    have hlt2 : |((B ^ k' * (A ^ k * g) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0| < |a1| := by
      have hle : |((B ^ k' * (A ^ k * g) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0| ≤ |a1| := by
        rw [f10]; exact hk'
      exact lt_of_le_of_ne hle (abs_ne_of_parity qa rc).symm
    have hlt : (((B ^ k' * (A ^ k * g) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0).natAbs < N := by
      rw [← hN]
      have := hlt2.trans hlt1
      rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at this
      exact_mod_cast this
    have h2 := ih _ hlt _ hg2 rfl
    exact isSignedWord_of_mul (sanov_of_zero_zpow k)
      (isSignedWord_of_mul (sanov_of_one_zpow k') h2)

/-- [proved-standard; formal-checked] **Every move of `Γ(2)` is `±` a word in `A` and `B`.** -/
theorem exists_sanov_eq {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma 2) :
    ∃ w, sanov w = g ∨ sanov w = -g :=
  isSignedWord_of_mem_aux _ g hg rfl

/-! ## 5. The level-two group as a free group -/

/-- [proved-standard; formal-checked] Every word in `A` and `B` lies in `Γ(2)`. -/
theorem sanov_mem_Gamma_two (w : FreeGroup (Fin 2)) : sanov w ∈ CongruenceSubgroup.Gamma 2 := by
  induction w using FreeGroup.induction_on with
  | C1 => exact Subgroup.one_mem _
  | of i =>
    rw [sanov, FreeGroup.lift_apply_of]
    fin_cases i
    · exact A_mem
    · exact B_mem
  | inv_of i h => rw [map_inv]; exact Subgroup.inv_mem _ h
  | mul x y hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy

/-- [proved-standard; formal-checked] `g` and `−g` are one move of `PSL(2, ℤ)`. -/
theorem proj_neg (g : SL(2, ℤ)) : proj (-g) = proj g := by
  have h1 : proj (-1) = 1 := (proj_eq_one_iff _).2 neg_one_mem_center
  rw [show -g = -1 * g by rw [neg_mul, one_mul], map_mul, h1, one_mul]

/-- [proved-standard; formal-checked] The image of `Γ(2)` in `PSL(2, ℤ)` is the range of the word map. -/
theorem map_Gamma_two_eq_range :
    (CongruenceSubgroup.Gamma 2).map proj = (proj.comp sanov).range := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨w, hw | hw⟩ := exists_sanov_eq hg
    · exact ⟨w, by rw [MonoidHom.comp_apply, hw]⟩
    · exact ⟨w, by rw [MonoidHom.comp_apply, hw, proj_neg]⟩
  · rintro ⟨w, rfl⟩
    exact ⟨sanov w, sanov_mem_Gamma_two w, rfl⟩

/-- [proved-standard; formal-checked] **`Γ(2)/±1` is free on `A` and `B`**: the word map is an isomorphism of
the free group of rank two onto the image of Legendre's level-two group in `PSL(2, ℤ)`. -/
noncomputable def gammaTwoFree : FreeGroup (Fin 2) ≃* (CongruenceSubgroup.Gamma 2).map proj :=
  (MonoidHom.ofInjective sanov_psl_injective).trans (MulEquiv.subgroupCongr map_Gamma_two_eq_range.symm)

/-- [proved-standard; formal-checked] The isomorphism sends a word to its move. -/
theorem gammaTwoFree_apply (w : FreeGroup (Fin 2)) :
    (gammaTwoFree w : PSL(2, ℤ)) = proj (sanov w) := rfl

end Holonics.Geometry.LegendreLevelTwo

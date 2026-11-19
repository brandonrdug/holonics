import Mathlib
import HolonicsResearch.Landmarks.IharaAbelianCover
import HolonicsResearch.Landmarks.PrimeCycleHalf

/-!
# Closed walks equidistribute over holonomy classes: the finite Chebotarev density at the half

Source record: `research/records/2026-11-18_HARD_LEFSCHETZ_HOLDS_ON_A_FLAT_TORUS_LETTER_BY_LETTER_A_COVERS_CLOSED_WALKS_FALL_INTO_THEIR_HOLONOMY_CLASSES_AT_THE_HALF_AND_THE_COVERING_TREES_RETURNS_SET_THE_FLOOR_AT_THE_HALF.md`,
§4, the sequel to `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md`,
§3.

`Landmarks/IharaAbelianCover` factors an abelian cover's dart determinant through the characters
of its voltage group.  This module reads the same factorization on the closed walks themselves.
A closed walk of the base (`IharaEulerProduct.ClosedWalk`: `n` darts, no backtrack, the wrap
included) carries a **holonomy**, the sum of the voltages it crosses; the characters read that
holonomy, and their orthogonality sorts the walks by it.

**[definition]** `weighted a b ω`: the dart operator with entry `ω d f` where `f` continues `d`;
`holonomy a b σ c = Σ_i σ (c i)`; `holonomyCount a b σ n g`, written `W_n(g)`: the closed walks of
`n` darts whose holonomy is `g`.

**[proved-derived; formal-checked] What is proved.**

1. **C1, the trace of a weighted power is a sum over closed walks** (`trace_pow_weighted`):
   `tr (weighted ω)ⁿ = Σ_(closed walks c) ∏_i ω (c i) (c (i + 1))`, read through the cyclic-word
   expansion of `Compression/Landmark/NecklaceIntegrality`.  The twisted operator of the factors,
   `hashimotoC a b g` (weight on the dart entered), and `diag g · B` (weight on the dart left) both
   give `Σ_c ∏_i g (c i)` (`trace_pow_hashimotoC`, `trace_pow_diagonal_mul_hashimoto`).
2. **C2, a twist reads the holonomy** (`trace_pow_twist`): with the `k`-th twist
   `d ↦ ψ (k σ d)`, `tr (B_k)ⁿ = Σ_c ψ (k · hol c)`.
3. **C3, orthogonality sorts the walks** (`sum_char_mul_trace`): for primitive `ψ` into a domain,
   `Σ_k ψ (−k g) · tr (B_k)ⁿ = #G · W_n(g)` for every `g`; the classes add up to all the closed
   walks (`sum_holonomyCount`), and the trivial character's term is the base's trace
   (`trace_pow_twist_zero`).
4. **C4, the cover counts the walks of holonomy zero** (`trace_cover_pow`, `trace_cover_pow_eq`):
   `tr B_Yⁿ = Σ_k tr (B_k)ⁿ = #G · W_n(0)`, through the frame change of `IharaAbelianCover` and its
   two-sided inverse there (`IharaAbelianCover.charFrameInv_mul_charFrame`,
   `IharaAbelianCover.charFrame_mul_charFrameInv`): a closed walk of the cover is a closed walk of the base of holonomy
   zero with a starting sheet.
5. **C5, Chebotarev at the half** (`holonomyCount_sub_le`): over `ℂ`, if every nontrivial twist has
   `‖tr (B_k)ⁿ‖ ≤ M`, then `|W_n(g) − tr Bⁿ/#G| ≤ (#G − 1)/#G · M` for every class `g`; with the
   base tempered and the twists' traces bounded by `C (√q)ⁿ` (`holonomyCount_tempered`),
   `|W_n(g) − qⁿ/#G| ≤ ((#G − 1) C (√q)ⁿ + 1 + 2|c| + 2(|V| − 1)(√q)ⁿ)/#G`, `c = |E| − |V|`.

**Reading.**  [interpretation] `agent-inferred`.  The holonomy of a closed walk is what a pair
contact's carry adds up to around it, and the characters are the frames that read it.  The base's
own count is the trivial frame; each other frame reads a twisted count, and where every twisted
count stays at the half's size, the walks fall into the holonomy classes in equal shares up to the
half: the finite form of Chebotarev's density theorem with the Riemann hypothesis's error, for the
cover's Galois group `G` (Stark and Terras, `from training`).

**What this does not state.**  The bound on the twisted traces is a hypothesis: no spectral bound
for a twisted operator is proved here (the twisted Ihara–Bass of `IharaBassConnection` reads its
modes, and placing them in the band is the twisted complex's own half).  The count is of closed
walks, not of prime cycles: a prime cycle repeated `d` times has holonomy `d · h`, and the
Möbius inversion by holonomy class is not made.  Non-abelian covers are not here.

**Computational object.**  The helical pair interaction: the voltage is the carry a contact adds
between sheets, the holonomy the carry around a closed strand, and the characters the cover's own
frames.  Of the winding guide's six objects: the pair (the darts and their carries), cell holonomy
(what each character reads around a closed walk) and the tower thread (the cover as a transverse
restriction whose gluing is plural); the helix, faces and placement and the tube stay attached.

**Consumers.**  The atlas row `trace.cover-holonomy-equidistribution`, beside
`trace.abelian-cover-artin` and `trace.prime-cycle-theorem-half`.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Finset Matrix
open scoped Kronecker

namespace Holonics.Landmarks.IharaCoverChebotarev

open Holonics.Landmarks.IharaBass Holonics.Landmarks.IharaBassConnection
open Holonics.Landmarks.IharaAbelianCover Holonics.Landmarks.IharaEulerProduct
open Holonics.Compression.Landmark.NecklaceIntegrality

/-! ## C1. The trace of a weighted power is a sum over closed walks -/

section Weighted

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)
variable {K : Type*} [CommRing K]

/-- [definition] The weighted dart operator: `ω d f` where `f` leaves the cell `d` enters and is
not `d` reversed, `0` elsewhere. -/
def weighted (ω : E ⊕ E → E ⊕ E → K) : Matrix (E ⊕ E) (E ⊕ E) K :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap then ω d f else 0

/-- [proved-derived; formal-checked] **C1.**  The trace of a power of the weighted dart operator is
the sum over the closed walks of `n` darts of the product of the weights along them. -/
theorem trace_pow_weighted (ω : E ⊕ E → E ⊕ E → K) (n : ℕ) [NeZero n] :
    (weighted a b ω ^ n).trace = ∑ c : ClosedWalk a b n, ∏ i, ω (c.1 i) (c.1 (i + 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [trace_pow_succ_eq_sum_cyclic]
  simp only [weighted, Matrix.of_apply]
  simp_rw [Fintype.prod_ite_zero]
  rw [← Finset.sum_subtype (univ.filter fun u : ZMod (k + 1) → E ⊕ E =>
      ∀ i, tgt a b (u i) = src a b (u (i + 1)) ∧ u (i + 1) ≠ (u i).swap) (fun u => by simp)
      (fun u => ∏ i, ω (u i) (u (i + 1))), Finset.sum_filter]
  rfl

omit [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A product around a closed walk is unchanged by a turn of one
dart. -/
theorem prod_succ_eq {n : ℕ} [NeZero n] (g : E ⊕ E → K) (w : ZMod n → E ⊕ E) :
    ∏ i, g (w (i + 1)) = ∏ i, g (w i) :=
  Fintype.prod_equiv (Equiv.addRight 1) _ _ fun _ => rfl

omit [Fintype E] in
/-- [proved-derived; formal-checked] The twisted operator of the factors (weight on the dart
entered) is a weighted dart operator. -/
theorem weighted_col (g : E ⊕ E → K) : weighted a b (fun _ f => g f) = hashimotoC a b g := rfl

/-- [proved-derived; formal-checked] So is `diag g · B` (weight on the dart left). -/
theorem weighted_row (g : E ⊕ E → K) :
    weighted a b (fun d _ => g d) = Matrix.diagonal g * hashimoto K a b := by
  ext d f
  rw [Matrix.diagonal_mul]
  simp only [weighted, Matrix.of_apply, hashimoto_apply]
  split_ifs <;> simp

/-- [proved-derived; formal-checked] `tr (B_g)ⁿ = Σ_c ∏_i g (c i)`. -/
theorem trace_pow_hashimotoC (g : E ⊕ E → K) (n : ℕ) [NeZero n] :
    (hashimotoC a b g ^ n).trace = ∑ c : ClosedWalk a b n, ∏ i, g (c.1 i) := by
  rw [← weighted_col, trace_pow_weighted]
  exact Finset.sum_congr rfl fun c _ => prod_succ_eq g c.1

/-- [proved-derived; formal-checked] `tr (diag g · B)ⁿ = Σ_c ∏_i g (c i)`. -/
theorem trace_pow_diagonal_mul_hashimoto (g : E ⊕ E → K) (n : ℕ) [NeZero n] :
    ((Matrix.diagonal g * hashimoto K a b) ^ n).trace = ∑ c : ClosedWalk a b n, ∏ i, g (c.1 i) := by
  rw [← weighted_row, trace_pow_weighted]

/-- [proved-derived; formal-checked] The two placements of the weight have one trace at every
power. -/
theorem trace_pow_diagonal_mul_hashimoto_eq (g : E ⊕ E → K) (n : ℕ) :
    ((Matrix.diagonal g * hashimoto K a b) ^ n).trace = (hashimotoC a b g ^ n).trace := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : NeZero n := ⟨hn.ne'⟩
    rw [trace_pow_diagonal_mul_hashimoto, trace_pow_hashimotoC]

end Weighted

/-! ## C2 and C3. The holonomy, its characters and their orthogonality -/

section Holonomy

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)
variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]
variable {K : Type*} [CommRing K]

/-- [definition] The holonomy of a closed walk: the sum of the voltages of its darts. -/
def holonomy (σ : E ⊕ E → G) {n : ℕ} [NeZero n] (c : ClosedWalk a b n) : G := ∑ i, σ (c.1 i)

/-- [definition] `W_n(g)`: the closed walks of `n` darts whose holonomy is `g`. -/
def holonomyCount (σ : E ⊕ E → G) (n : ℕ) [NeZero n] (g : G) : ℕ :=
  (univ.filter fun c : ClosedWalk a b n => holonomy a b σ c = g).card

omit [Fintype G] [DecidableEq G] in
/-- [proved-standard; formal-checked] An additive character sends a sum to the product of its
values. -/
theorem addChar_map_sum {ι : Type*} (ψ : AddChar G K) (s : Finset ι) (x : ι → G) :
    ψ (∑ i ∈ s, x i) = ∏ i ∈ s, ψ (x i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro j s hj ih
  rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

omit [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] **C2.**  The `k`-th twist reads each closed walk by the
character of its holonomy: `tr (B_k)ⁿ = Σ_c ψ (k · hol c)`. -/
theorem trace_pow_twist (ψ : AddChar G K) (σ : E ⊕ E → G) (k : G) (n : ℕ) [NeZero n] :
    (hashimotoC a b (twist ψ σ k) ^ n).trace =
      ∑ c : ClosedWalk a b n, ψ (k * holonomy a b σ c) := by
  rw [trace_pow_hashimotoC]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [holonomy, Finset.mul_sum, addChar_map_sum]
  rfl

omit [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] The trivial character's term is the base's trace. -/
theorem trace_pow_twist_zero (ψ : AddChar G K) (σ : E ⊕ E → G) (n : ℕ) :
    (hashimotoC a b (twist ψ σ 0) ^ n).trace = (hashimoto K a b ^ n).trace := by
  rw [twist_zero, hashimotoC_one]

/-- [proved-derived; formal-checked] **C3, orthogonality sorts the walks.**  For a primitive `ψ`
into a domain, `Σ_k ψ (−k g) · tr (B_k)ⁿ = #G · W_n(g)`. -/
theorem sum_char_mul_trace [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (σ : E ⊕ E → G) (n : ℕ) [NeZero n] (g : G) :
    ∑ k, ψ (-(k * g)) * (hashimotoC a b (twist ψ σ k) ^ n).trace =
      (Fintype.card G : K) * (holonomyCount a b σ n g : K) := by
  simp_rw [trace_pow_twist, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ c : ClosedWalk a b n, ∑ k, ψ (-(k * g)) * ψ (k * holonomy a b σ c) =
      if holonomy a b σ c - g = 0 then (Fintype.card G : K) else 0 := by
    intro c
    have hk : ∀ k : G, ψ (-(k * g)) * ψ (k * holonomy a b σ c) = ψ (k * (holonomy a b σ c - g)) := by
      intro k
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    simp_rw [hk]
    rw [AddChar.sum_mulShift _ hψ]
    split_ifs <;> simp
  simp_rw [h, sub_eq_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, holonomyCount]

/-- [proved-derived; formal-checked] The holonomy classes add up to all the closed walks. -/
theorem sum_holonomyCount (σ : E ⊕ E → G) (n : ℕ) [NeZero n] :
    ∑ g, holonomyCount a b σ n g = Fintype.card (ClosedWalk a b n) := by
  unfold holonomyCount
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := holonomy a b σ) (t := univ)
    (fun _ _ => Finset.mem_univ _)]

end Holonomy

/-! ## C4. The cover counts the base's walks of holonomy zero -/

section Cover

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)
variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]
variable {K : Type*} [CommRing K]

/-- [proved-derived; formal-checked] **The cover's traces are the twists' traces**:
`tr B_Yⁿ = Σ_k tr (B_k)ⁿ` at every power. -/
theorem trace_cover_pow [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (n : ℕ) :
    (coverHashimoto K a b σ ^ n).trace = ∑ k, (hashimotoC a b (twist ψ σ k) ^ n).trace := by
  set W := charFrame (E ⊕ E) ψ
  set W' := charFrameInv (E ⊕ E) ψ
  set Bd := Matrix.blockDiagonal fun k => Matrix.diagonal (twist ψ σ k) * hashimoto K a b
  have hs : SemiconjBy W Bd (coverHashimoto K a b σ) :=
    (coverHashimoto_mul_charFrame a b ψ σ).symm
  have hn : W * Bd ^ n = coverHashimoto K a b σ ^ n * W := hs.pow_right n
  have h1 : (W' * (coverHashimoto K a b σ ^ n * W)).trace =
      (Fintype.card G : K) * (coverHashimoto K a b σ ^ n).trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, charFrame_mul_charFrameInv _ hψ, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
  have h2 : (W' * (coverHashimoto K a b σ ^ n * W)).trace = (Fintype.card G : K) * (Bd ^ n).trace := by
    rw [← hn, ← Matrix.mul_assoc, charFrameInv_mul_charFrame _ hψ, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul]
  have h3 := mul_left_cancel₀ hG (h1.symm.trans h2)
  rw [h3, ← Matrix.blockDiagonal_pow, Matrix.trace_blockDiagonal]
  exact Finset.sum_congr rfl fun k _ => trace_pow_diagonal_mul_hashimoto_eq a b _ n

/-- [proved-derived; formal-checked] **C4.**  The cover's closed walks of `n` darts count `#G`
times the base's closed walks of holonomy zero: `tr B_Yⁿ = #G · W_n(0)`. -/
theorem trace_cover_pow_eq [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (n : ℕ) [NeZero n] :
    (coverHashimoto K a b σ ^ n).trace = (Fintype.card G : K) * (holonomyCount a b σ n 0 : K) := by
  rw [trace_cover_pow a b hψ hG σ n, ← sum_char_mul_trace a b hψ σ n 0]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Cover

/-! ## C5. Chebotarev at the half -/

section Chebotarev

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E] (a b : E → V)
variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]

/-- [proved-derived; formal-checked] The base's complex trace counts its closed walks. -/
theorem trace_hashimoto_complex (n : ℕ) [NeZero n] :
    (hashimoto ℂ a b ^ n).trace = (Fintype.card (ClosedWalk a b n) : ℂ) := by
  rw [trace_hashimoto_pow_eq_natCast, card_closedWalk]

/-- [proved-derived; formal-checked] **C5, Chebotarev with the twists' error.**  Over `ℂ`, if every
nontrivial twist has `‖tr (B_k)ⁿ‖ ≤ M`, every holonomy class holds its share of the closed walks
up to `(#G − 1)/#G · M`: `|W_n(g) − tr Bⁿ/#G| ≤ (#G − 1)/#G · M`. -/
theorem holonomyCount_sub_le {ψ : AddChar G ℂ} (hψ : ψ.IsPrimitive) (σ : E ⊕ E → G) (n : ℕ)
    [NeZero n] {M : ℝ} (hM : ∀ k : G, k ≠ 0 → ‖(hashimotoC a b (twist ψ σ k) ^ n).trace‖ ≤ M)
    (g : G) :
    |(holonomyCount a b σ n g : ℝ) - (Fintype.card (ClosedWalk a b n) : ℝ) / Fintype.card G| ≤
      ((Fintype.card G : ℝ) - 1) / Fintype.card G * M := by
  set N := (Fintype.card (ClosedWalk a b n) : ℝ)
  set W := (holonomyCount a b σ n g : ℝ)
  have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hsum := sum_char_mul_trace a b hψ σ n g
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G)), zero_mul, neg_zero,
    AddChar.map_zero_eq_one, one_mul, trace_pow_twist_zero, trace_hashimoto_complex] at hsum
  -- the error is the nontrivial characters' sum
  have herr : (((Fintype.card G : ℝ) * W - N : ℝ) : ℂ) =
      ∑ k ∈ univ.erase (0 : G), ψ (-(k * g)) * (hashimotoC a b (twist ψ σ k) ^ n).trace := by
    simp only [W, N]
    push_cast
    linear_combination -hsum
  have hle : |(Fintype.card G : ℝ) * W - N| ≤ ((Fintype.card G : ℝ) - 1) * M := by
    have h1 := congrArg (‖·‖) herr
    simp only [Complex.norm_real, Real.norm_eq_abs] at h1
    rw [h1]
    calc ‖∑ k ∈ univ.erase (0 : G), ψ (-(k * g)) * (hashimotoC a b (twist ψ σ k) ^ n).trace‖
        ≤ ∑ k ∈ univ.erase (0 : G), ‖ψ (-(k * g)) * (hashimotoC a b (twist ψ σ k) ^ n).trace‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _k ∈ univ.erase (0 : G), M := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [norm_mul, AddChar.norm_apply, one_mul]
          exact hM k (Finset.ne_of_mem_erase hk)
      _ = ((Fintype.card G : ℝ) - 1) * M := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
            nsmul_eq_mul, Nat.cast_sub Fintype.card_pos, Nat.cast_one]
  have heq : W - N / Fintype.card G = ((Fintype.card G : ℝ) * W - N) / Fintype.card G := by
    field_simp
  rw [heq, abs_div, abs_of_pos hGpos, div_le_iff₀ hGpos]
  calc |(Fintype.card G : ℝ) * W - N| ≤ ((Fintype.card G : ℝ) - 1) * M := hle
    _ = ((Fintype.card G : ℝ) - 1) / Fintype.card G * M * Fintype.card G := by
        field_simp

variable [Fintype V]

/-- [proved-derived; formal-checked] **C5 on a tempered base.**  With `q + 1` darts at every cell,
the base's modes other than the count tempered and every nontrivial twist's trace within
`C (√q)ⁿ`, every holonomy class holds `qⁿ/#G` closed walks up to the half:
`|W_n(g) − qⁿ/#G| ≤ ((#G − 1) C (√q)ⁿ + 1 + 2|c| + 2(|V| − 1)(√q)ⁿ)/#G`. -/
theorem holonomyCount_tempered {ψ : AddChar G ℂ} (hψ : ψ.IsPrimitive) (σ : E ⊕ E → G)
    {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
    (hVE : Fintype.card V ≤ Fintype.card E) {i₀ : V}
    (h0 : RegularComplexZeros.eigen a b i₀ = (q : ℝ) + 1)
    (htemp : ∀ i, i ≠ i₀ → (RegularComplexZeros.eigen a b i) ^ 2 ≤ 4 * (q : ℝ))
    (n : ℕ) [NeZero n] {C : ℝ}
    (hC : ∀ k : G, k ≠ 0 → ‖(hashimotoC a b (twist ψ σ k) ^ n).trace‖ ≤ C * Real.sqrt q ^ n)
    (g : G) :
    |(holonomyCount a b σ n g : ℝ) - (q : ℝ) ^ n / Fintype.card G| ≤
      (((Fintype.card G : ℝ) - 1) * (C * Real.sqrt q ^ n) + (1 + 2 * |(Fintype.card E : ℝ) -
        Fintype.card V| + 2 * ((Fintype.card V : ℝ) - 1) * Real.sqrt q ^ n)) /
        Fintype.card G := by
  have hGpos : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have h1 := holonomyCount_sub_le a b hψ σ n hC g
  have h2 := PrimeCycleHalf.walkCount_sub_pow_le a b hreg hVE h0 htemp n
  have hN : RegularComplexZeros.walkCount a b n = (Fintype.card (ClosedWalk a b n) : ℝ) := by
    rw [PrimeCycleHalf.walkCount_eq_natCast, card_closedWalk]
  rw [hN] at h2
  have hsplit : (holonomyCount a b σ n g : ℝ) - (q : ℝ) ^ n / Fintype.card G =
      ((holonomyCount a b σ n g : ℝ) - (Fintype.card (ClosedWalk a b n) : ℝ) / Fintype.card G) +
        ((Fintype.card (ClosedWalk a b n) : ℝ) - (q : ℝ) ^ n) / Fintype.card G := by
    field_simp
    ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_div, abs_of_pos hGpos, add_div]
  refine add_le_add ?_ (div_le_div_of_nonneg_right h2 hGpos.le)
  calc _ ≤ ((Fintype.card G : ℝ) - 1) / Fintype.card G * (C * Real.sqrt q ^ n) := h1
    _ = ((Fintype.card G : ℝ) - 1) * (C * Real.sqrt q ^ n) / Fintype.card G := by ring

end Chebotarev

/-! ## Audit -/

section Audit

#print axioms trace_pow_weighted
#print axioms trace_pow_hashimotoC
#print axioms trace_pow_diagonal_mul_hashimoto
#print axioms trace_pow_diagonal_mul_hashimoto_eq
#print axioms addChar_map_sum
#print axioms trace_pow_twist
#print axioms trace_pow_twist_zero
#print axioms sum_char_mul_trace
#print axioms sum_holonomyCount
#print axioms trace_cover_pow
#print axioms trace_cover_pow_eq
#print axioms trace_hashimoto_complex
#print axioms holonomyCount_sub_le
#print axioms holonomyCount_tempered

end Audit

end Holonics.Landmarks.IharaCoverChebotarev

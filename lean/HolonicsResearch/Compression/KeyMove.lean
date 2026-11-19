import Mathlib

/-!
# A key's move: the covector summed over a symbol's places is the derivative of the code under the move

[proved-derived; formal-checked] The source is the symbol record of November 12
(`research/records/2026-11-12_THE_STORE_CODES_HELD_TEXT_AT_THE_LEVEL_OF_TWO_KNOWN_NEIGHBOURS_A_SIDE_A_SYMBOL_IS_A_WORD_ON_LOCATED_RINGS_AND_A_DARK_PLACE_IS_THE_INTERIOR_OF_A_COMPOSITE.md`,
§8.3; atlas `code.key-move-first-order`, beside `code.symbol-word-located-rings`). A symbol `u` carries a key
`κ(u) = (r_j(u))_j` on rings `j`; ring `j` holds rows `F_j[r]`, and the symbol's encoding is the series
`E(κ) = Σ_j F_j[r_j] + G(κ)`, its first order and the terms `G` that read two rings or more (`Compression/SymbolWord`
proves the decomposition). A passage `x` puts symbols at places `k`, the field reads the encodings `E(κ(x_k))`, and the
code `L` is a function of those encodings with derivative `L′` there. The covector reaching place `k` is
`c_k = L′ ∘ (insert at k)` (`covector`).

What is proved, for a code differentiable at the passage's encodings, over any real normed space of rows.

1. **Moving one key moves the encoding at every place the symbol stood, and only there** (`moved_sub`): with the key
   of `u` moved on ring `j` to `v` (`moveKey`) and every row held, the encodings differ by
   `Δ = (F_j[v] − F_j[r_j(u)]) + (G(κ[j ↦ v]) − G(κ))` at the places of `u` and by zero elsewhere (`step_eq`).
2. **The derivative of the code along the move** (`hasDerivAt_move`): `t ↦ L(e + t (e′ − e))`, the code on the segment
   from the encodings to the moved ones, has derivative `Σ_(k : x_k = u) c_k(Δ)` at `t = 0`, the covector summed over
   the places `u` stood and paired with the step.
3. **The record's identity** (`key_move_first_order`): when no term of `G` reads ring `j` (`ReadsNot`), the step is
   `F_j[v] − F_j[r_j(u)]` and that derivative is `g_j(u, v) = Σ_(k : x_k = u) c_k(F_j[v] − F_j[r_j(u)])` (`keyMoveSum`).
   On an inner product space of rows, with `c_k = ⟨γ_k, ·⟩` (`gradAt`), it is the record's
   `Σ_(k : x_k = u) ⟨γ_k, F_j[v] − F_j[r_j(u)]⟩` (`keyMoveSum_eq_inner`, `key_move_first_order_inner`). The sum is the
   covector summed over the places, paired once (`keyMoveSum_eq_sum_covector`), so moves of one symbol to two residues
   compare by their rows alone (`keyMoveSum_sub`).
4. **A term that reads ring `j` with another ring enters** (`second_order_enters`): on two rings of two residues, one
   place, the code `L(e) = e(0)`, no first-order rows and the term `G(κ) = r_0 r_1`, moving ring 0 from 1 to 0 at
   `r_1 = 1` has derivative `−1` while `g_0 = 0`. "With the rows held" names every row of every order, and the record's
   sum is the derivative exactly when the higher terms do not read the moved ring; otherwise item 2's step holds.

What is not claimed. The key's discrete step (a carry event where the sum over a declared count of places passes a
declared grain) is the record's design and is not a theorem; a derivative along the segment is not the code's change
at the moved key, which item 2 bounds to first order only through `HasFDerivAt`. The code's own form (the release's
cross-entropy, its readout) is the consumer's and enters only through `L′`.

The computational object is the helical pair interaction read on a symbol's word: the rows a ring holds are shared by
every symbol at a residue, and the covector that reaches them through the faces is what locates a key. Of the winding
guide's six general objects this touches the helix (a ring's residue) and faces and placement (the covector at a
place); the pair, the cell holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.KeyMove

open scoped InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {U : Type*} [DecidableEq U] {n : ℕ}

/-! ## 1. The word, the passage and the move -/

/-- A key's encoding: the first-order rows of every ring at its residue, plus the higher terms `G`. -/
def encode (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (κ : ∀ i, α i) : V := (∑ i, F i (κ i)) + G κ

/-- The encodings the field reads at the passage's places. -/
def encodings (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (key : U → ∀ i, α i) (x : Fin n → U) : Fin n → V :=
  fun k => encode F G (key (x k))

/-- The keys after `u`'s residue on ring `j` moves to `v`; every other symbol keeps its key. -/
def moveKey (key : U → ∀ i, α i) (u : U) (j : ι) (v : α j) : U → ∀ i, α i :=
  Function.update key u (Function.update (key u) j v)

/-- The step of `u`'s encoding under the move, with every row held. -/
def step (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (κ : ∀ i, α i) (j : ι) (v : α j) : V :=
  (F j v - F j (κ j)) + (G (Function.update κ j v) - G κ)

/-- No term of `G` reads ring `j`: it is constant along that ring. -/
def ReadsNot (G : (∀ i, α i) → V) (j : ι) : Prop := ∀ κ (a : α j), G (Function.update κ j a) = G κ

omit [NormedSpace ℝ V] in
theorem encode_update (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (κ : ∀ i, α i) (j : ι) (v : α j) :
    encode F G (Function.update κ j v) - encode F G κ = step F G κ j v := by
  unfold encode step
  have h : ∑ i, F i (Function.update κ j v i) = (∑ i, F i (κ i)) - F j (κ j) + F j v := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    have : ∑ i ∈ Finset.univ.erase j, F i (Function.update κ j v i) = ∑ i ∈ Finset.univ.erase j, F i (κ i) :=
      Finset.sum_congr rfl fun i hi => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
    rw [this]
    abel
  rw [h]
  abel

omit [NormedSpace ℝ V] in
/-- Statement 1: the encodings move by the step at the places of `u` and nowhere else. -/
theorem moved_sub (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (key : U → ∀ i, α i) (x : Fin n → U) (u : U) (j : ι)
    (v : α j) (k : Fin n) :
    encodings F G (moveKey key u j v) x k - encodings F G key x k
      = if x k = u then step F G (key u) j v else 0 := by
  unfold encodings moveKey
  split_ifs with h
  · rw [h, Function.update_self, encode_update]
  · rw [Function.update_of_ne h, sub_self]

omit [Fintype ι] [NormedSpace ℝ V] in
/-- The step is the first-order rows' difference when no higher term reads the moved ring. -/
theorem step_eq (F : ∀ i, α i → V) (G : (∀ i, α i) → V) (κ : ∀ i, α i) (j : ι) (v : α j) (hG : ReadsNot G j) :
    step F G κ j v = F j v - F j (κ j) := by
  rw [step, hG, sub_self, add_zero]

/-! ## 2. The covector and the derivative along the move -/

/-- The covector reaching place `k`: the code's derivative restricted to the encoding at `k`. -/
noncomputable def covector (L' : (Fin n → V) →L[ℝ] ℝ) (k : Fin n) : V →L[ℝ] ℝ :=
  L'.comp (ContinuousLinearMap.single ℝ (fun _ : Fin n => V) k)

/-- A linear functional on the places' encodings is the sum of its covectors. -/
theorem apply_eq_sum_covector (L' : (Fin n → V) →L[ℝ] ℝ) (d : Fin n → V) :
    L' d = ∑ k, covector L' k (d k) := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  rfl

/-- The record's sum: the covector at each place `u` stood, paired with the first-order rows' difference. -/
noncomputable def keyMoveSum (L' : (Fin n → V) →L[ℝ] ℝ) (F : ∀ i, α i → V) (key : U → ∀ i, α i) (x : Fin n → U)
    (u : U) (j : ι) (v : α j) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => x k = u), covector L' k (F j v - F j (key u j))

/-- Statement 2: the code on the segment from the encodings to the moved ones has, at the start, the derivative
`Σ_(k : x_k = u) c_k(Δ)`. -/
theorem hasDerivAt_move (L : (Fin n → V) → ℝ) (L' : (Fin n → V) →L[ℝ] ℝ) (F : ∀ i, α i → V)
    (G : (∀ i, α i) → V) (key : U → ∀ i, α i) (x : Fin n → U) (u : U) (j : ι) (v : α j)
    (hL : HasFDerivAt L L' (encodings F G key x)) :
    HasDerivAt (fun t : ℝ => L (encodings F G key x + t • (encodings F G (moveKey key u j v) x
        - encodings F G key x)))
      (∑ k ∈ Finset.univ.filter (fun k => x k = u), covector L' k (step F G (key u) j v)) 0 := by
  set e := encodings F G key x
  set d := encodings F G (moveKey key u j v) x - e
  have hline : HasDerivAt (fun t : ℝ => e + t • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add e
  have hL0 : HasFDerivAt L L' (e + (0 : ℝ) • d) := by simpa using hL
  have h2 : HasDerivAt (fun t : ℝ => L (e + t • d)) (L' d) 0 := hL0.comp_hasDerivAt (0 : ℝ) hline
  refine h2.congr_deriv ?_
  rw [apply_eq_sum_covector, Finset.sum_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : d k = if x k = u then step F G (key u) j v else 0 := by
    simp only [d, Pi.sub_apply]
    exact moved_sub F G key x u j v k
  rw [hk]
  split_ifs <;> simp

/-- Statement 3: when no higher term reads ring `j`, the record's sum `g_j(u, v)` is the derivative of the code under
moving `u`'s residue on ring `j` to `v`. -/
theorem key_move_first_order (L : (Fin n → V) → ℝ) (L' : (Fin n → V) →L[ℝ] ℝ) (F : ∀ i, α i → V)
    (G : (∀ i, α i) → V) (key : U → ∀ i, α i) (x : Fin n → U) (u : U) (j : ι) (v : α j)
    (hL : HasFDerivAt L L' (encodings F G key x)) (hG : ReadsNot G j) :
    HasDerivAt (fun t : ℝ => L (encodings F G key x + t • (encodings F G (moveKey key u j v) x
        - encodings F G key x)))
      (keyMoveSum L' F key x u j v) 0 := by
  have := hasDerivAt_move L L' F G key x u j v hL
  rwa [step_eq F G (key u) j v hG] at this

omit [Fintype ι] [DecidableEq ι] in
/-- The sum is the covector summed over the places `u` stood, paired once. -/
theorem keyMoveSum_eq_sum_covector (L' : (Fin n → V) →L[ℝ] ℝ) (F : ∀ i, α i → V) (key : U → ∀ i, α i)
    (x : Fin n → U) (u : U) (j : ι) (v : α j) :
    keyMoveSum L' F key x u j v
      = (∑ k ∈ Finset.univ.filter (fun k => x k = u), covector L' k) (F j v - F j (key u j)) := by
  rw [keyMoveSum, _root_.sum_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- Two moves of one symbol compare by their rows alone: `g_j(u, v) − g_j(u, w)` pairs the summed covector with
`F_j[v] − F_j[w]`. -/
theorem keyMoveSum_sub (L' : (Fin n → V) →L[ℝ] ℝ) (F : ∀ i, α i → V) (key : U → ∀ i, α i) (x : Fin n → U)
    (u : U) (j : ι) (v w : α j) :
    keyMoveSum L' F key x u j v - keyMoveSum L' F key x u j w
      = (∑ k ∈ Finset.univ.filter (fun k => x k = u), covector L' k) (F j v - F j w) := by
  rw [keyMoveSum_eq_sum_covector, keyMoveSum_eq_sum_covector, ← map_sub]
  congr 1
  abel

/-! ## 3. On an inner product space of rows -/

section Inner

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- The covector at place `k` as a vector of rows: `c_k = ⟨γ_k, ·⟩`. -/
noncomputable def gradAt (L' : (Fin n → W) →L[ℝ] ℝ) (k : Fin n) : W :=
  (InnerProductSpace.toDual ℝ W).symm (covector L' k)

theorem covector_eq_inner (L' : (Fin n → W) →L[ℝ] ℝ) (k : Fin n) (w : W) :
    covector L' k w = ⟪gradAt L' k, w⟫_ℝ := by
  rw [gradAt, InnerProductSpace.toDual_symm_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- The record's form: `g_j(u, v) = Σ_(k : x_k = u) ⟨γ_k, F_j[v] − F_j[r_j(u)]⟩`. -/
theorem keyMoveSum_eq_inner (L' : (Fin n → W) →L[ℝ] ℝ) (F : ∀ i, α i → W) (key : U → ∀ i, α i) (x : Fin n → U)
    (u : U) (j : ι) (v : α j) :
    keyMoveSum L' F key x u j v
      = ∑ k ∈ Finset.univ.filter (fun k => x k = u), ⟪gradAt L' k, F j v - F j (key u j)⟫_ℝ := by
  unfold keyMoveSum
  exact Finset.sum_congr rfl fun k _ => covector_eq_inner L' k _

theorem key_move_first_order_inner (L : (Fin n → W) → ℝ) (L' : (Fin n → W) →L[ℝ] ℝ) (F : ∀ i, α i → W)
    (G : (∀ i, α i) → W) (key : U → ∀ i, α i) (x : Fin n → U) (u : U) (j : ι) (v : α j)
    (hL : HasFDerivAt L L' (encodings F G key x)) (hG : ReadsNot G j) :
    HasDerivAt (fun t : ℝ => L (encodings F G key x + t • (encodings F G (moveKey key u j v) x
        - encodings F G key x)))
      (∑ k ∈ Finset.univ.filter (fun k => x k = u), ⟪gradAt L' k, F j v - F j (key u j)⟫_ℝ) 0 := by
  rw [← keyMoveSum_eq_inner]
  exact key_move_first_order L L' F G key x u j v hL hG

end Inner

/-! ## 4. A term reading the moved ring with another enters -/

section Second

/-- Two rings of two residues; one symbol; one place; no first-order rows; the second-order term `r_0 r_1`. -/
def keySecond : Unit → ∀ _ : Fin 2, Fin 2 := fun _ _ => 1

def rowsZero : ∀ _ : Fin 2, Fin 2 → ℝ := fun _ _ => 0

def crossTerm : (∀ _ : Fin 2, Fin 2) → ℝ := fun κ => ((κ 0 : ℕ) : ℝ) * ((κ 1 : ℕ) : ℝ)

/-- The code reads the one place's encoding. -/
noncomputable def readOne : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0

/-- The record's sum is `0` (no first-order rows), while the derivative along the move of ring `0` from residue `1`
to `0` at `r_1 = 1` is `−1`: the term reading both rings enters, and `ReadsNot crossTerm 0` fails. -/
theorem second_order_enters :
    keyMoveSum readOne rowsZero keySecond (fun _ : Fin 1 => ()) () 0 0 = 0 ∧
      HasDerivAt (fun t : ℝ => readOne (encodings rowsZero crossTerm keySecond (fun _ : Fin 1 => ()) +
          t • (encodings rowsZero crossTerm (moveKey keySecond () 0 0) (fun _ : Fin 1 => ())
            - encodings rowsZero crossTerm keySecond (fun _ : Fin 1 => ())))) (-1) 0 ∧
      ¬ ReadsNot crossTerm 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [keyMoveSum, rowsZero]
  · have h := hasDerivAt_move (fun e => readOne e) readOne rowsZero crossTerm keySecond (fun _ : Fin 1 => ()) ()
      0 0 readOne.hasFDerivAt
    convert h using 1
    simp [covector, readOne, step, rowsZero, crossTerm, keySecond, Function.update]
  · intro h
    have := h (fun _ => 1) 0
    simp [crossTerm, Function.update] at this

end Second

end Holonics.Compression.KeyMove

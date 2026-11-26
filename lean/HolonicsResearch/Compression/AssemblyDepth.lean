import Mathlib

/-!
# A build's depth: the joins a composition costs from a locale's parts, with every made thing kept as a part

[proved-derived; formal-checked] The source is the record of November 26
(`research/records/2026-11-26_A_COMPOSITION_STANDS_IN_A_LOCALE_ONLY_AFTER_ITS_CAUSES_ITS_COST_IS_ITS_BUILD_FROM_THE_PARTS_THE_LOCALE_HOLDS_A_HOLARCHY_OVER_AN_AEON_IS_THAT_BUILD_KEPT_AND_GENERALIZATION_IS_A_SHORT_BUILD_FROM_ONES_OWN_PARTS.md`;
atlas `compression.build-depth-doubling-floor`, `compression.made-part-reused`, `prime.no-join-produces-a-prime`).
A locale holds parts `B` and a join `glue`. A pool is built by listing a part or by joining two things the pool already
holds; a made thing stays in the pool, so it is a part for every later join. `Built glue B l r` says that the pool `l` was
built from `B` with `r` joins.

What is proved.

1. **The doubling floor** (`Built.size_le`, `addition_floor`): where a join's size is at most the sum of its two sizes and
   every part has size at most `s`, a pool built with `r` joins holds nothing larger than `s · 2 ^ r`. So a composition of `n`
   units costs at least `log₂ n` joins. The floor is met (`doubling_built`): `2 ^ r` units stand after `r` joins, each
   a thing joined to itself.
2. **A prime no join produces** (`Built.prime_dvd_part`, `five_not_from_two_three`): under multiplication, a prime that
   divides a made thing divides a part. Octaves and fifths (`2` and `3`) never make a multiple of `5` at any depth: the
   third's prime is supplied as a part or it is absent.
3. **A made thing reused** (`Built.sample`, `Reaches.sample`, `Reaches.same_closure`, `Reaches.made_is_free`): if `C` costs
   `c` joins from `B`, anything that costs `r` joins from `B` with `C` added costs at most `r + c` from `B`. A made
   composition taken as a part makes nothing newly reachable; it makes what factors through it cheaper, and itself free.
4. **A basis only grows what it reaches** (`Built.mono`).
5. **Two coprime periods' gaps** (`frobenius_three_five`, from Mathlib's `frobeniusNumber_pair`): periods `3` and `5` never
   sum to `7` and sum to every count past it.
-/

namespace Holonics.Compression.AssemblyDepth

variable {α : Type*}

/-- A pool built from the parts `B` with `r` joins: a part is listed at no cost, a join of two things the pool holds costs
one, and whatever was made stays in the pool. -/
inductive Built (glue : α → α → α) (B : Set α) : List α → ℕ → Prop
  | nil : Built glue B [] 0
  | part {l : List α} {r : ℕ} {b : α} : Built glue B l r → b ∈ B → Built glue B (b :: l) r
  | join {l : List α} {r : ℕ} {x y : α} :
      Built glue B l r → x ∈ l → y ∈ l → Built glue B (glue x y :: l) (r + 1)

/-- `x` stands in some pool built from `B` with `r` joins. -/
def Reaches (glue : α → α → α) (B : Set α) (r : ℕ) (x : α) : Prop :=
  ∃ l, Built glue B l r ∧ x ∈ l

/-- A larger basis builds every pool a smaller one builds, at the same count of joins. -/
theorem Built.mono {glue : α → α → α} {B B' : Set α} (hBB : B ⊆ B') {l : List α} {r : ℕ}
    (h : Built glue B l r) : Built glue B' l r := by
  induction h with
  | nil => exact Built.nil
  | part _ hb ih => exact Built.part ih (hBB hb)
  | join _ hx hy ih => exact Built.join ih hx hy

/-- **The doubling floor.** With a join no larger than the sum of its two sizes and parts of size at most `s`, a pool built
with `r` joins holds nothing larger than `s · 2 ^ r`. -/
theorem Built.size_le {glue : α → α → α} {B : Set α} {size : α → ℕ} {s : ℕ}
    (hglue : ∀ x y, size (glue x y) ≤ size x + size y) (hB : ∀ b ∈ B, size b ≤ s)
    {l : List α} {r : ℕ} (h : Built glue B l r) : ∀ x ∈ l, size x ≤ s * 2 ^ r := by
  induction h with
  | nil => intro x hx; simp at hx
  | @part l r b _ hb ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxb | hx
    · rw [hxb]
      calc size b ≤ s := hB b hb
        _ = s * 1 := (mul_one s).symm
        _ ≤ s * 2 ^ r := Nat.mul_le_mul_left s Nat.one_le_two_pow
    · exact ih x hx
  | @join l r a d _ ha hd ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxad | hx
    · rw [hxad]
      calc size (glue a d) ≤ size a + size d := hglue a d
        _ ≤ s * 2 ^ r + s * 2 ^ r := Nat.add_le_add (ih a ha) (ih d hd)
        _ = s * 2 ^ (r + 1) := by ring
    · calc size x ≤ s * 2 ^ r := ih x hx
        _ ≤ s * 2 ^ (r + 1) :=
          Nat.mul_le_mul_left s (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r))

/-- **The floor for counts.** From the unit alone, under addition, `r` joins reach no count past `2 ^ r`: a count `n`
costs at least `log₂ n` joins (the lower bound of an addition chain). -/
theorem addition_floor {l : List ℕ} {r n : ℕ} (h : Built (· + ·) ({1} : Set ℕ) l r) (hn : n ∈ l) :
    n ≤ 2 ^ r := by
  have key := Built.size_le (size := fun k : ℕ => k) (s := 1) (fun _ _ => le_rfl)
    (fun b hb => le_of_eq (Set.mem_singleton_iff.mp hb)) h n hn
  simpa using key

/-- **The floor is met by doubling.** After `r` joins, each a thing joined to itself, `2 ^ r` units stand. -/
theorem doubling_built (r : ℕ) : ∃ l, Built (· + ·) ({1} : Set ℕ) l r ∧ 2 ^ r ∈ l := by
  induction r with
  | zero => exact ⟨[1], Built.part Built.nil (Set.mem_singleton 1), by simp⟩
  | succ r ih =>
    obtain ⟨l, hl, hmem⟩ := ih
    refine ⟨(2 ^ r + 2 ^ r) :: l, Built.join hl hmem hmem, ?_⟩
    have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
    rw [h2]
    exact List.mem_cons_self

/-- **A prime no join produces.** Under multiplication, a prime that divides a made thing divides a part. -/
theorem Built.prime_dvd_part {B : Set ℕ} {l : List ℕ} {r : ℕ} (h : Built (· * ·) B l r)
    {p : ℕ} (hp : p.Prime) : ∀ x ∈ l, p ∣ x → ∃ b ∈ B, p ∣ b := by
  induction h with
  | nil => intro x hx; simp at hx
  | @part l r b _ hb ih =>
    intro x hx hpx
    rcases List.mem_cons.mp hx with hxb | hx
    · exact ⟨b, hb, hxb ▸ hpx⟩
    · exact ih x hx hpx
  | @join l r a d _ ha hd ih =>
    intro x hx hpx
    rcases List.mem_cons.mp hx with hxad | hx
    · have hmul : p ∣ a * d := hxad ▸ hpx
      rcases (Nat.Prime.dvd_mul hp).mp hmul with h | h
      · exact ih a ha h
      · exact ih d hd h
    · exact ih x hx hpx

/-- Octaves and fifths never make the third's prime: no pool built from `2` and `3` under multiplication holds a
multiple of `5`, at any count of joins. -/
theorem five_not_from_two_three {l : List ℕ} {r : ℕ} (h : Built (· * ·) ({2, 3} : Set ℕ) l r) :
    ∀ x ∈ l, ¬ 5 ∣ x := by
  intro x hx h5
  obtain ⟨b, hb, hdvd⟩ := h.prime_dvd_part (by norm_num : Nat.Prime 5) x hx h5
  rcases Set.mem_insert_iff.mp hb with hb2 | hb3
  · rw [hb2] at hdvd; exact absurd hdvd (by norm_num)
  · rw [Set.mem_singleton_iff.mp hb3] at hdvd; exact absurd hdvd (by norm_num)

/-- **A made thing reused.** If the pool `lc`, built from `B` with `c` joins, holds `C`, then whatever a pool built from
`B` with `C` added holds after `r` joins, a pool built from `B` alone holds after `r + c`. -/
theorem Built.sample {glue : α → α → α} {B : Set α} {C : α} {lc : List α} {c : ℕ}
    (hc : Built glue B lc c) (hC : C ∈ lc) {l : List α} {r : ℕ}
    (h : Built glue (insert C B) l r) :
    ∃ l', Built glue B l' (r + c) ∧ ∀ x, x ∈ l ∨ x ∈ lc → x ∈ l' := by
  induction h with
  | nil =>
    refine ⟨lc, by simpa using hc, fun x hx => ?_⟩
    rcases hx with hx | hx
    · simp at hx
    · exact hx
  | @part l r b _ hb ih =>
    obtain ⟨l', hl', hsub⟩ := ih
    rcases Set.mem_insert_iff.mp hb with hbC | hb
    · refine ⟨l', hl', fun x hx => ?_⟩
      rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with hxb | hx
        · rw [hxb, hbC]; exact hsub C (Or.inr hC)
        · exact hsub x (Or.inl hx)
      · exact hsub x (Or.inr hx)
    · refine ⟨b :: l', Built.part hl' hb, fun x hx => ?_⟩
      rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with hxb | hx
        · rw [hxb]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub x (Or.inl hx))
      · exact List.mem_cons_of_mem _ (hsub x (Or.inr hx))
  | @join l r a d _ ha hd ih =>
    obtain ⟨l', hl', hsub⟩ := ih
    refine ⟨glue a d :: l', ?_, fun x hx => ?_⟩
    · have hj := Built.join hl' (hsub a (Or.inl ha)) (hsub d (Or.inl hd))
      rwa [Nat.add_right_comm] at hj
    · rcases hx with hx | hx
      · rcases List.mem_cons.mp hx with hxad | hx
        · rw [hxad]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub x (Or.inl hx))
      · exact List.mem_cons_of_mem _ (hsub x (Or.inr hx))

/-- A larger basis reaches whatever a smaller one reaches, at the same count. -/
theorem Reaches.mono {glue : α → α → α} {B B' : Set α} (hBB : B ⊆ B') {r : ℕ} {x : α}
    (h : Reaches glue B r x) : Reaches glue B' r x := by
  obtain ⟨l, hl, hx⟩ := h
  exact ⟨l, hl.mono hBB, hx⟩

/-- **The pivot's price is paid once.** If `C` costs `c` joins from `B`, what costs `r` joins from `B` with `C` added
costs at most `r + c` from `B`. -/
theorem Reaches.sample {glue : α → α → α} {B : Set α} {C X : α} {c r : ℕ}
    (hC : Reaches glue B c C) (hX : Reaches glue (insert C B) r X) : Reaches glue B (r + c) X := by
  obtain ⟨lc, hlc, hCmem⟩ := hC
  obtain ⟨l, hl, hXmem⟩ := hX
  obtain ⟨l', hl', hsub⟩ := hlc.sample hCmem hl
  exact ⟨l', hl', hsub X (Or.inl hXmem)⟩

/-- **A made thing taken as a part makes nothing newly reachable.** What a basis reaches with a made `C` added, it
reaches without it. -/
theorem Reaches.same_closure {glue : α → α → α} {B : Set α} {C X : α} {c : ℕ}
    (hC : Reaches glue B c C) : (∃ r, Reaches glue (insert C B) r X) ↔ ∃ r, Reaches glue B r X := by
  constructor
  · rintro ⟨r, hX⟩
    exact ⟨r + c, hC.sample hX⟩
  · rintro ⟨r, hX⟩
    exact ⟨r, hX.mono (Set.subset_insert C B)⟩

/-- **And it is itself free there.** Over a basis that holds it as a part, a made thing costs no join. -/
theorem Reaches.made_is_free (glue : α → α → α) (B : Set α) (C : α) :
    Reaches glue (insert C B) 0 C :=
  ⟨[C], Built.part Built.nil (Set.mem_insert C B), List.mem_cons_self⟩

/-- **Two coprime periods' gaps.** Periods `3` and `5` never sum to `7`, and they sum to every count past it. -/
theorem frobenius_three_five : FrobeniusNumber 7 ({3, 5} : Set ℕ) := by
  have h := frobeniusNumber_pair (m := 3) (n := 5) (by decide) (by norm_num) (by norm_num)
  simpa using h

end Holonics.Compression.AssemblyDepth

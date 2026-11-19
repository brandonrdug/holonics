import Mathlib
import Holonics.Compression.Landmark.Context.Tree

/-!
# Ville's inequality bounds the chance that any ring of a founding family founds under the node null

Source: comment c6249536068 of #62, box "Founding" of #410 (`founding_universal_inference`), on the
founding law of #398 (`hnn::founding::FoundingLaw::{open, receive, read}` at `d5ed4adc1`; atlas
`hnn.founding-universal-inference`). A candidate ring of period `ℓ` with a description cost is
fixed at `open`, before the stream. The law counts each arriving class `y_k` whose history holds a
full context (`k ≥ offset`, `k` counting every ingested cell) at the split cell
`(k mod ℓ, y_(k−offset))` and at the node cell `(k mod g, y_(k−offset))`, `g = gcd(ℓ, L)` with `L`
the cell clock. The split's code `Q_ℓ` is the product of its Krichevsky–Trofimov faces
`(2·seen + 1)/(2·total + |A|)`; the node's code is the maximum-likelihood code
`ML_g = Σ_rows (n log₂ n − Σ_y N_y log₂ N_y)`; the ring founds when the surplus `ML_g − bits(Q_ℓ)`
exceeds its cost. The box: under the null where `y_k` depends on the past only through
`(k mod g, y_(k−offset))`, Ville's inequality bounds the chance that any ring founds by
`Σ_ℓ 2^(−cost_ℓ)`, which `open` holds below one.

## What is proved

The finite-horizon form, for every horizon, on a finite alphabet. A law is a sequential law on
histories (held newest first): `p h a` is its conditional of the class `a` after the history `h`,
and `wordProb p w` the likelihood of a history. The chance `chance p hit N` is the mass `p` gives
the histories of `N` cells along which some read time `n ≤ N` satisfies `hit` (`not_survives_iff`).

* **Ville's inequality at every horizon** (`ville`). For a law `p` (conditionals summing to one)
  and a test `q` (nonnegative conditionals summing to at most one), the chance under `p` that the
  likelihood ratio `Q/P` reaches `λ > 0` at some read time up to `N` is at most `1/λ`. The proof is
  the stopped likelihood ratio's: the chance is the sum of the first hits (`chance_eq_sum`), each
  first hit carries `λ` times its `p` mass in `q` mass, and `q`'s first hits and survivors never
  carry more than its whole mass (`survivor_step`, `firstHits_add_survivors_le`). No positivity of
  `p` is used, and the horizon is arbitrary.
* **The chance's order** (`chance_mono_horizon`, `chance_mono_hit`, `chance_exists_le`): it is
  nondecreasing in the horizon, monotone in the event, and a union over a finite family is bounded
  by the sum. Reading the law at every cell is the largest event; reading it at fewer read times is
  covered by monotonicity ("however often the law is read").
* **The node's maximum likelihood dominates every node law** (`countedProb_le_nodeML`). A law whose
  conditional at every counted cell is a subprobability kernel `K` at the cell's node gives the
  counted cells `∏_c ∏_y K(c,y)^{N_{c,y}}` (`countedProb_node`), which is at most
  `ML(w) = ∏_c ∏_y (N_{c,y}/n_c)^{N_{c,y}}` (Gibbs' inequality on each row, `gibbs_row`, by
  `t^N ≤ exp(N(t−1))`). This is the source's `Q/P_ML ≤ Q/P`.
* **A founding is a reached ratio** (`founds_reaches`). `2^cost · ML(w) < Q_counted(w)` makes the
  test that is the candidate's law on counted cells and the null's on opening cells (`mix`) reach
  `Q/P ≥ 2^cost`.
* **Universal inference over a family** (`founding_ville`): for any finite family of candidates,
  any tests, node maps and costs, and a null whose counted conditionals are a kernel at every
  candidate's node, the chance that some candidate founds at some read time up to `N` is at most
  `Σ_i 2^(−cost_i)`.
* **The box (`founding_universal_inference`).** The helical instance: counted cells `k ≥ offset`,
  split contexts `(k mod ℓ, y_(k−offset))` (`splitCtx`), node contexts `(k mod gcd(ℓ, L), y_(k−offset))`
  (`nodeCtx`), and the KT split law (`ktTest`, whose face is the Rust's `(2n + 1)/(2t + |A|)`,
  `ktTest_eq`). Under any law whose counted conditionals depend, for each candidate `ℓ` of the
  family, only on `(k mod gcd(ℓ, L), y_(k−offset))`, the chance that any ring founds by a read time
  `N` is at most `Σ_ℓ 2^(−cost_ℓ)`, for every `N`. One null for the whole family, depending on
  `(k mod g, y_(k−offset))` with `g` dividing every `gcd(ℓ, L)`, meets the hypothesis
  (`founding_universal_inference_of_dvd`). With `open`'s family bound below one, the chance stays
  below one at every horizon, and its supremum over the horizons is at most the bound
  (`founding_below_one`).

## Limits

* **The horizon.** No measure on infinite streams is built. The bound holds at every finite
  horizon, uniformly, and the chance is nondecreasing in it, so its supremum is bounded too; that
  the supremum is the probability of a founding at some read time ever is continuity from below
  under the process measure (Ionescu-Tulcea), which is not formalized here.
* **The node null is per candidate.** `g = gcd(ℓ, L)` depends on the candidate, so the hypothesis
  is that the null is a node law at every candidate's node. For a null that is a node law at only
  some candidates' nodes, the theorem applied to that subfamily bounds the chance that one of them
  founds by the subfamily's sum, which the family bound dominates.
* **The read's enclosure** is not modelled: `founds` is the strict inequality
  `log₂(Q/P_ML) > cost` itself. `FoundingLaw::read` founds only when the lower endpoint of the
  enclosed surplus exceeds the cost, which implies it, so the Rust founds less often.
* **The kernel** is a subprobability at every `(k mod g, y)`, including values the counted cells
  never read; a node law can always be completed there.
* **Not modelled:** `reopen` (a fresh e-process from its own first counted cell), the description
  ceiling and the refusals of `open` (a period dividing the clock, duplicates), the tie-break of
  `read`, and the bounded product carrier of `Q`.

The computational object is the helical pair interaction at the declared offset: a class `y_k`
paired with the class `offset` cells back. Of the winding guide's six objects this touches the
helix (the phases `k mod ℓ` of a candidate ring and `k mod g` of its node), the pair (the context
`y_(k−offset)`), and faces and placement (the KT face each counted cell emits, and the node's
maximum-likelihood face); cell holonomy, the tube and the tower thread stay attached through
`Context/Tree` and the founding law.

Consumers: the founding law's guarantee (`hnn::founding::FoundingLaw::{open, receive, read}` at
`d5ed4adc1`), `Context/Tree`'s KT face (`ktFace`, `ktFace_pos`, `ktFace_sum`), the KT partition
invariance beside it (`Compression/KTPartitionInvariant`, which shows a split by a phase the context
carries never founds), and the atlas row `hnn.founding-universal-inference`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.FoundingVille

open Classical

/-! ## 1. Sequential laws on histories -/

section Laws

variable {A : Type*} [Fintype A]

/-- [definition] **The likelihood a sequential law gives a history.** A history is held newest
first, so `a :: h` is the history `h` followed by the class `a`; `p h a` is the law's conditional
of `a` after `h`. -/
def wordProb (p : List A → A → ℝ) : List A → ℝ
  | [] => 1
  | a :: h => wordProb p h * p h a

/-- [definition] **The histories of `n` cells.** -/
def words : ℕ → Finset (List A)
  | 0 => {[]}
  | n + 1 => ((words n) ×ˢ (Finset.univ : Finset A)).image fun x => x.2 :: x.1

/-- [proved-derived; formal-checked] A sum over the histories of `n + 1` cells is a sum over the
histories of `n` cells and the class that follows. -/
theorem sum_words_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List A → M) :
    ∑ w ∈ words (n + 1), f w = ∑ w ∈ words n, ∑ a, f (a :: w) := by
  rw [words, Finset.sum_image, Finset.sum_product]
  rintro ⟨w, a⟩ _ ⟨w', a'⟩ _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.2 h.1

omit [Fintype A] in
/-- [proved-derived; formal-checked] A law with nonnegative conditionals gives every history a
nonnegative likelihood. -/
theorem wordProb_nonneg {p : List A → A → ℝ} (hp : ∀ h a, 0 ≤ p h a) :
    ∀ w, 0 ≤ wordProb p w
  | [] => zero_le_one
  | a :: h => mul_nonneg (wordProb_nonneg hp h) (hp h a)

end Laws

/-! ## 2. Hitting a threshold at some read time -/

section Hit

variable {A : Type*} [Fintype A]

/-- [definition] **No read time has hit**: neither the history nor any earlier history satisfies
`hit`. -/
def survives (hit : List A → Prop) : List A → Prop
  | [] => ¬ hit []
  | a :: w => ¬ hit (a :: w) ∧ survives hit w

/-- [definition] **No earlier history has hit** (the history itself aside). -/
def before (hit : List A → Prop) : List A → Prop
  | [] => True
  | _ :: w => survives hit w

omit [Fintype A] in
/-- [proved-derived; formal-checked] A history survives when it does not hit and nothing before
it hit. -/
theorem survives_iff (hit : List A → Prop) (w : List A) :
    survives hit w ↔ ¬ hit w ∧ before hit w := by
  cases w <;> simp [survives, before]

omit [Fintype A] in
/-- [proved-derived; formal-checked] **A read time hits** exactly when some history along the word,
the word itself or one of its earlier histories `w.drop j`, satisfies `hit`. -/
theorem not_survives_iff (hit : List A → Prop) :
    ∀ w : List A, ¬ survives hit w ↔ ∃ j ≤ w.length, hit (w.drop j)
  | [] => by simp [survives]
  | a :: w => by
    rw [survives, not_and_or, not_not, not_survives_iff hit w]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨0, Nat.zero_le _, h⟩
      · exact ⟨j + 1, by simp; omega, by simpa using h⟩
    · rintro ⟨j, hj, h⟩
      rcases j with _ | j
      · exact Or.inl h
      · exact Or.inr ⟨j, by simp at hj; omega, by simpa using h⟩

/-- [definition] **The chance that some read time up to `N` hits**, under the law `p`. -/
def chance (p : List A → A → ℝ) (hit : List A → Prop) (N : ℕ) : ℝ :=
  ∑ w ∈ words N, if survives hit w then 0 else wordProb p w

/-- [definition] **The chance that the first hit falls at read time `n`.** -/
def firstHit (p : List A → A → ℝ) (hit : List A → Prop) (n : ℕ) : ℝ :=
  ∑ w ∈ words n, if hit w ∧ before hit w then wordProb p w else 0

variable {p : List A → A → ℝ}

/-- [proved-derived; formal-checked] **The chance grows by the first hits**: with conditionals
summing to one, `chance (N + 1) = chance N + firstHit (N + 1)`. -/
theorem chance_succ (hp1 : ∀ h, ∑ a, p h a = 1) (hit : List A → Prop) (N : ℕ) :
    chance p hit (N + 1) = chance p hit N + firstHit p hit (N + 1) := by
  unfold chance firstHit
  rw [sum_words_succ, sum_words_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases hs : survives hit w
  · simp only [survives, hs, and_true, if_true, zero_add, before]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : hit (a :: w) <;> simp [ha]
  · simp only [survives, hs, and_false, if_false, before, Finset.sum_const_zero, add_zero,
      wordProb]
    rw [← Finset.mul_sum, hp1, mul_one]

/-- [proved-derived; formal-checked] At horizon zero the chance is the empty history's hit. -/
theorem chance_zero (hit : List A → Prop) : chance p hit 0 = firstHit p hit 0 := by
  by_cases h0 : hit [] <;> simp [chance, firstHit, words, survives, before, wordProb, h0]

/-- [proved-derived; formal-checked] **The chance is the sum of the first hits.** -/
theorem chance_eq_sum (hp1 : ∀ h, ∑ a, p h a = 1) (hit : List A → Prop) :
    ∀ N, chance p hit N = ∑ n ∈ Finset.range (N + 1), firstHit p hit n
  | 0 => by rw [chance_zero, Finset.sum_range_one]
  | N + 1 => by rw [chance_succ hp1, chance_eq_sum hp1 hit N, Finset.sum_range_succ _ (N + 1)]

/-- [proved-derived; formal-checked] **The chance is nondecreasing in the horizon.** -/
theorem chance_mono_horizon (hp0 : ∀ h a, 0 ≤ p h a) (hp1 : ∀ h, ∑ a, p h a = 1)
    (hit : List A → Prop) (N : ℕ) : chance p hit N ≤ chance p hit (N + 1) := by
  rw [chance_succ hp1]
  refine le_add_of_nonneg_right (Finset.sum_nonneg fun w _ => ?_)
  split_ifs
  · exact wordProb_nonneg hp0 w
  · exact le_rfl

/-- [proved-derived; formal-checked] **A weaker hit has a smaller chance.** -/
theorem chance_mono_hit (hp0 : ∀ h a, 0 ≤ p h a) {hit hit' : List A → Prop}
    (h : ∀ w, hit w → hit' w) (N : ℕ) : chance p hit N ≤ chance p hit' N := by
  have hs : ∀ w, survives hit' w → survives hit w := by
    intro w
    induction w with
    | nil => exact fun h' h0 => h' (h _ h0)
    | cons a w ih => exact fun ⟨h1, h2⟩ => ⟨fun h0 => h1 (h _ h0), ih h2⟩
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases h1 : survives hit w
  · rw [if_pos h1]; split_ifs
    · exact le_rfl
    · exact wordProb_nonneg hp0 w
  · rw [if_neg h1, if_neg fun h2 => h1 (hs w h2)]

/-- [proved-derived; formal-checked] **A union bound over a finite family of hits.** -/
theorem chance_exists_le (hp0 : ∀ h a, 0 ≤ p h a) {ι : Type*} (F : Finset ι)
    (hit : ι → List A → Prop) (N : ℕ) :
    chance p (fun w => ∃ i ∈ F, hit i w) N ≤ ∑ i ∈ F, chance p (hit i) N := by
  have hs : ∀ w, survives (fun w => ∃ i ∈ F, hit i w) w ↔ ∀ i ∈ F, survives (hit i) w := by
    intro w
    induction w with
    | nil => simp [survives]
    | cons a w ih =>
      simp only [survives, ih, not_exists, not_and]
      constructor
      · rintro ⟨h1, h2⟩ i hi
        exact ⟨h1 i hi, h2 i hi⟩
      · intro h
        exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
  unfold chance
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun w _ => ?_
  by_cases hall : ∀ i ∈ F, survives (hit i) w
  · rw [if_pos ((hs w).mpr hall)]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp [wordProb_nonneg hp0 w]
  · simp only [not_forall] at hall
    obtain ⟨i, hi, hni⟩ := hall
    rw [if_neg fun h => hni ((hs w).mp h i hi)]
    calc wordProb p w = (if survives (hit i) w then 0 else wordProb p w) := by rw [if_neg hni]
      _ ≤ ∑ j ∈ F, (if survives (hit j) w then 0 else wordProb p w) :=
        Finset.single_le_sum (f := fun j => if survives (hit j) w then 0 else wordProb p w)
          (fun j _ => by split_ifs <;> simp [wordProb_nonneg hp0 w]) hi

end Hit

/-! ## 3. Ville's inequality at every horizon -/

section Ville

variable {A : Type*} [Fintype A] {p q : List A → A → ℝ}

/-- [definition] **The likelihood ratio reaches `λ`**: `λ·P(h) ≤ Q(h)`. -/
def reaches (p q : List A → A → ℝ) (lam : ℝ) (h : List A) : Prop :=
  lam * wordProb p h ≤ wordProb q h

/-- [definition] The test's mass on the histories of `n` cells that have not hit. -/
def survivorMass (q : List A → A → ℝ) (hit : List A → Prop) (n : ℕ) : ℝ :=
  ∑ w ∈ words n, if survives hit w then wordProb q w else 0

/-- [definition] The test's mass on the first hits at read time `n`. -/
def firstHitMass (q : List A → A → ℝ) (hit : List A → Prop) (n : ℕ) : ℝ :=
  ∑ w ∈ words n, if hit w ∧ before hit w then wordProb q w else 0

/-- [proved-derived; formal-checked] **The test's mass does not grow**: the survivors at `n + 1`
and the first hits at `n + 1` carry at most the survivors' mass at `n`, since the test's
conditionals sum to at most one. -/
theorem survivor_step (hq0 : ∀ h a, 0 ≤ q h a) (hq1 : ∀ h, ∑ a, q h a ≤ 1)
    (hit : List A → Prop) (n : ℕ) :
    survivorMass q hit (n + 1) + firstHitMass q hit (n + 1) ≤ survivorMass q hit n := by
  unfold survivorMass firstHitMass
  rw [sum_words_succ, sum_words_succ, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w _ => ?_
  rw [← Finset.sum_add_distrib]
  by_cases hs : survives hit w
  · rw [if_pos hs]
    calc ∑ a, ((if survives hit (a :: w) then wordProb q (a :: w) else 0) +
          (if hit (a :: w) ∧ before hit (a :: w) then wordProb q (a :: w) else 0))
        = ∑ a, wordProb q w * q w a := by
          refine Finset.sum_congr rfl fun a _ => ?_
          by_cases ha : hit (a :: w) <;> simp [survives, before, hs, ha, wordProb]
      _ = wordProb q w * ∑ a, q w a := by rw [Finset.mul_sum]
      _ ≤ wordProb q w * 1 := mul_le_mul_of_nonneg_left (hq1 w) (wordProb_nonneg hq0 w)
      _ = wordProb q w := mul_one _
  · rw [if_neg hs]
    refine le_of_eq (Finset.sum_eq_zero fun a _ => ?_)
    simp [survives, before, hs]

/-- [proved-derived; formal-checked] **The first hits and the survivors carry at most the test's
whole mass.** -/
theorem firstHits_add_survivors_le (hq0 : ∀ h a, 0 ≤ q h a) (hq1 : ∀ h, ∑ a, q h a ≤ 1)
    (hit : List A → Prop) :
    ∀ N, ∑ n ∈ Finset.range (N + 1), firstHitMass q hit n + survivorMass q hit N ≤ 1
  | 0 => by
    by_cases h0 : hit [] <;> simp [firstHitMass, survivorMass, words, survives, before, h0,
      wordProb]
  | N + 1 => by
    have := survivor_step hq0 hq1 hit N
    have ih := firstHits_add_survivors_le hq0 hq1 hit N
    rw [Finset.sum_range_succ]
    linarith

/-- [proved-derived; formal-checked] **Ville's inequality at every horizon.** For a law `p` whose
conditionals sum to one and a test `q` whose conditionals sum to at most one, the chance under `p`
that the likelihood ratio `Q/P` reaches `λ > 0` at some read time up to `N` is at most `1/λ`, for
every horizon `N`. -/
theorem ville (hp1 : ∀ h, ∑ a, p h a = 1) (hq0 : ∀ h a, 0 ≤ q h a)
    (hq1 : ∀ h, ∑ a, q h a ≤ 1) {lam : ℝ} (hlam : 0 < lam) (N : ℕ) :
    chance p (reaches p q lam) N ≤ 1 / lam := by
  rw [le_div_iff₀ hlam, chance_eq_sum hp1, Finset.sum_mul]
  have hF : 0 ≤ survivorMass q (reaches p q lam) N :=
    Finset.sum_nonneg fun w _ => by split_ifs <;> simp [wordProb_nonneg hq0 w]
  have hle : ∀ n, firstHit p (reaches p q lam) n * lam ≤ firstHitMass q (reaches p q lam) n := by
    intro n
    unfold firstHit firstHitMass
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun w _ => ?_
    split_ifs with h
    · rw [mul_comm]; exact h.1
    · simp
  calc ∑ n ∈ Finset.range (N + 1), firstHit p (reaches p q lam) n * lam
      ≤ ∑ n ∈ Finset.range (N + 1), firstHitMass q (reaches p q lam) n :=
        Finset.sum_le_sum fun n _ => hle n
    _ ≤ 1 := by linarith [firstHits_add_survivors_le hq0 hq1 (reaches p q lam) N]

end Ville

/-! ## 4. Counted cells, their contexts and the node's maximum likelihood -/

section Counts

variable {A : Type*} [Fintype A] {C : Type*}

/-- [definition] **The count of a class at a context along a history**: the counted cells of `w`
whose history before them reads `c` under `ctx` and whose class is `b`. A cell is `a` after the
history `h` in `a :: h`; whether it is counted, and its context, are read from `h` alone. -/
def cnt (counted : List A → Prop) (ctx : List A → C) : List A → C → A → ℕ
  | [], _, _ => 0
  | a :: h, c, b => cnt counted ctx h c b + if counted h ∧ ctx h = c ∧ a = b then 1 else 0

/-- [definition] A context's row total along a history. -/
def rowCount (counted : List A → Prop) (ctx : List A → C) (w : List A) (c : C) : ℕ :=
  ∑ b, cnt counted ctx w c b

/-- [definition] **The node's maximum likelihood** of a history's counted cells:
`ML(w) = ∏_c ∏_y (N_{c,y}/n_c)^{N_{c,y}}`, the likelihood the empirical conditional of each row
gives the row's own cells (`2^(−ML_g)` of `FoundingLaw::read`). An empty row contributes one. -/
def nodeML [Fintype C] (counted : List A → Prop) (node : List A → C) (w : List A) : ℝ :=
  ∏ c, ∏ b, ((cnt counted node w c b : ℝ) / (rowCount counted node w c : ℝ)) ^
    cnt counted node w c b

/-- [definition] **The likelihood a law gives the counted cells** of a history. -/
def countedProb (counted : List A → Prop) (r : List A → A → ℝ) : List A → ℝ
  | [] => 1
  | a :: h => countedProb counted r h * if counted h then r h a else 1

/-- [definition] **The likelihood a law gives the opening cells** (those not counted). -/
def openProb (counted : List A → Prop) (r : List A → A → ℝ) : List A → ℝ
  | [] => 1
  | a :: h => openProb counted r h * if counted h then 1 else r h a

omit [Fintype A] in
/-- [proved-derived; formal-checked] A history's likelihood is its counted cells' likelihood times
its opening cells'. -/
theorem wordProb_eq_counted_mul_open (counted : List A → Prop) (r : List A → A → ℝ) :
    ∀ w, wordProb r w = countedProb counted r w * openProb counted r w
  | [] => by simp [wordProb, countedProb, openProb]
  | a :: h => by
    rw [wordProb, countedProb, openProb, wordProb_eq_counted_mul_open counted r h]
    by_cases hc : counted h
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring

omit [Fintype A] in
/-- [proved-derived; formal-checked] A nonnegative law gives the opening cells a nonnegative
likelihood. -/
theorem openProb_nonneg {counted : List A → Prop} {r : List A → A → ℝ}
    (hr : ∀ h a, 0 ≤ r h a) : ∀ w, 0 ≤ openProb counted r w
  | [] => zero_le_one
  | a :: h => mul_nonneg (openProb_nonneg hr h) (by split_ifs; exacts [zero_le_one, hr h a])

/-- [definition] **The test as a sequential law**: the candidate's conditional `k` on counted
cells and the null's own conditional on the opening cells, which the founding law does not code. -/
def mix (counted : List A → Prop) (k p : List A → A → ℝ) (h : List A) (a : A) : ℝ :=
  if counted h then k h a else p h a

omit [Fintype A] in
/-- [proved-derived; formal-checked] The test codes the counted cells by the candidate's law. -/
theorem countedProb_mix (counted : List A → Prop) (k p : List A → A → ℝ) :
    ∀ w, countedProb counted (mix counted k p) w = countedProb counted k w
  | [] => rfl
  | a :: h => by
    rw [countedProb, countedProb, countedProb_mix counted k p h]
    by_cases hc : counted h <;> simp [mix, hc]

omit [Fintype A] in
/-- [proved-derived; formal-checked] The test codes the opening cells by the null's own law, so
the ratio `Q/P` is read on the counted cells alone. -/
theorem openProb_mix (counted : List A → Prop) (k p : List A → A → ℝ) :
    ∀ w, openProb counted (mix counted k p) w = openProb counted p w
  | [] => rfl
  | a :: h => by
    rw [openProb, openProb, openProb_mix counted k p h]
    by_cases hc : counted h <;> simp [mix, hc]

omit [Fintype A] in
/-- [proved-derived; formal-checked] The test's conditionals are nonnegative. -/
theorem mix_nonneg {counted : List A → Prop} {k p : List A → A → ℝ} (hk : ∀ h a, 0 ≤ k h a)
    (hp : ∀ h a, 0 ≤ p h a) (h : List A) (a : A) : 0 ≤ mix counted k p h a := by
  unfold mix; split_ifs; exacts [hk h a, hp h a]

/-- [proved-derived; formal-checked] The test's conditionals sum to at most one. -/
theorem mix_sum_le {counted : List A → Prop} {k p : List A → A → ℝ} (hk : ∀ h, ∑ a, k h a ≤ 1)
    (hp : ∀ h, ∑ a, p h a = 1) (h : List A) : ∑ a, mix counted k p h a ≤ 1 := by
  unfold mix
  by_cases hc : counted h
  · simp only [hc, if_true]; exact hk h
  · simp only [hc, if_false]; exact (hp h).le

omit [Fintype A] in
/-- [proved-derived; formal-checked] A power by an indicator is the indicator's choice. -/
private theorem pow_indicator (x : ℝ) (P : Prop) [Decidable P] :
    x ^ (if P then 1 else 0) = if P then x else 1 := by
  split_ifs <;> simp

/-- [proved-derived; formal-checked] **A node law's counted likelihood regroups by row**: when the
law's conditional at every counted cell is the kernel `K` at the cell's node,
`P_counted(w) = ∏_c ∏_y K(c,y)^{N_{c,y}}`. -/
theorem countedProb_node [Fintype C] {counted : List A → Prop} {node : List A → C}
    {p : List A → A → ℝ} {K : C → A → ℝ} (hK : ∀ h, counted h → ∀ a, p h a = K (node h) a) :
    ∀ w, countedProb counted p w = ∏ c, ∏ b, K c b ^ cnt counted node w c b
  | [] => by simp [countedProb, cnt]
  | a :: h => by
    rw [countedProb, countedProb_node hK h]
    simp only [cnt, pow_add, Finset.prod_mul_distrib]
    congr 1
    simp only [pow_indicator]
    by_cases hc : counted h
    · rw [if_pos hc, hK h hc a, Fintype.prod_eq_single (node h), Fintype.prod_eq_single a]
      · simp [hc]
      · intro b hb
        simp [hc, Ne.symm hb]
      · intro c hc'
        exact Finset.prod_eq_one fun b _ => by simp [hc, Ne.symm hc']
    · rw [if_neg hc]
      exact (Finset.prod_eq_one fun c _ => Finset.prod_eq_one fun b _ => by simp [hc]).symm

/-- [proved-derived; formal-checked] **Gibbs' inequality on one row**: for a row of counts `N` and
any subprobability `K`, `∏_y K_y^{N_y} ≤ ∏_y (N_y/n)^{N_y}` with `n = Σ N`. The empirical
conditional is the row's maximum likelihood. Proof: write `K_y = (N_y/n)·t_y`; then
`t^N ≤ exp(N(t−1))` and `Σ N_y(t_y − 1) ≤ n·ΣK − n ≤ 0`. -/
theorem gibbs_row (N : A → ℕ) (K : A → ℝ) (hK0 : ∀ b, 0 ≤ K b) (hK1 : ∑ b, K b ≤ 1) :
    ∏ b, K b ^ N b ≤ ∏ b, ((N b : ℝ) / ((∑ b', N b' : ℕ) : ℝ)) ^ N b := by
  set n : ℝ := ((∑ b', N b' : ℕ) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set t : A → ℝ := fun b => K b * n / N b with ht
  have ht0 : ∀ b, 0 ≤ t b := fun b => div_nonneg (mul_nonneg (hK0 b) hn0) (Nat.cast_nonneg _)
  have hsplit : ∀ b, K b ^ N b = ((N b : ℝ) / n) ^ N b * t b ^ N b := by
    intro b
    rw [← mul_pow]
    rcases Nat.eq_zero_or_pos (N b) with h0 | hpos
    · simp [h0]
    · have hNb : (N b : ℝ) ≠ 0 := by positivity
      have hle : N b ≤ ∑ b', N b' :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
      have hnpos : n ≠ 0 := by
        rw [hn]; exact_mod_cast (lt_of_lt_of_le hpos hle).ne'
      congr 1
      simp only [ht]
      field_simp
  have hpow : ∀ b, t b ^ N b ≤ Real.exp ((N b : ℝ) * (t b - 1)) := by
    intro b
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (ht0 b) (by linarith [Real.add_one_le_exp (t b - 1)]) _
  have hexp : ∀ b, (N b : ℝ) * (t b - 1) ≤ K b * n - N b := by
    intro b
    rcases Nat.eq_zero_or_pos (N b) with h0 | hpos
    · simp only [h0, Nat.cast_zero, zero_mul, sub_zero]
      exact mul_nonneg (hK0 b) hn0
    · have hNb : (N b : ℝ) ≠ 0 := by positivity
      refine le_of_eq ?_
      simp only [ht]
      field_simp
  have hsum : ∑ b, (N b : ℝ) * (t b - 1) ≤ 0 := by
    calc ∑ b, (N b : ℝ) * (t b - 1) ≤ ∑ b, (K b * n - N b) := Finset.sum_le_sum fun b _ => hexp b
      _ = (∑ b, K b) * n - n := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hn, Nat.cast_sum]
      _ ≤ 1 * n - n := by nlinarith
      _ = 0 := by ring
  have hprod0 : 0 ≤ ∏ b, ((N b : ℝ) / n) ^ N b :=
    Finset.prod_nonneg fun b _ => pow_nonneg (div_nonneg (Nat.cast_nonneg _) hn0) _
  calc ∏ b, K b ^ N b = (∏ b, ((N b : ℝ) / n) ^ N b) * ∏ b, t b ^ N b := by
        rw [← Finset.prod_mul_distrib]; exact Finset.prod_congr rfl fun b _ => hsplit b
    _ ≤ (∏ b, ((N b : ℝ) / n) ^ N b) * ∏ b, Real.exp ((N b : ℝ) * (t b - 1)) :=
        mul_le_mul_of_nonneg_left
          (Finset.prod_le_prod (fun b _ => pow_nonneg (ht0 b) _) fun b _ => hpow b) hprod0
    _ = (∏ b, ((N b : ℝ) / n) ^ N b) * Real.exp (∑ b, (N b : ℝ) * (t b - 1)) := by
        rw [Real.exp_sum]
    _ ≤ (∏ b, ((N b : ℝ) / n) ^ N b) * 1 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hsum) hprod0
    _ = _ := mul_one _

/-- [proved-derived; formal-checked] **The node's maximum likelihood dominates every node law**:
`P_counted(w) ≤ ML(w)` for a law whose counted conditionals are a subprobability kernel `K` at the
cell's node. In bits, `ML_g` is the shortest code among the node laws (`Q/P_ML ≤ Q/P`). -/
theorem countedProb_le_nodeML [Fintype C] {counted : List A → Prop} {node : List A → C}
    {p : List A → A → ℝ} {K : C → A → ℝ} (hK0 : ∀ c a, 0 ≤ K c a) (hK1 : ∀ c, ∑ a, K c a ≤ 1)
    (hK : ∀ h, counted h → ∀ a, p h a = K (node h) a) (w : List A) :
    countedProb counted p w ≤ nodeML counted node w := by
  rw [countedProb_node hK, nodeML]
  exact Finset.prod_le_prod (fun c _ => Finset.prod_nonneg fun b _ => pow_nonneg (hK0 c b) _)
    fun c _ => gibbs_row _ _ (hK0 c) (hK1 c)

end Counts

/-! ## 5. Founding under the node null -/

section Founding

variable {A : Type*} [Fintype A] {C : Type*} {p : List A → A → ℝ}

/-- [definition] **A candidate founds at a history**: its test's likelihood of the counted cells
exceeds `2^cost` times the node's maximum likelihood, `log₂(Q/P_ML) > cost`. `FoundingLaw::read`
founds a candidate only where the lower endpoint of its enclosed surplus exceeds the cost, which
implies this. -/
def founds [Fintype C] (counted : List A → Prop) (node : List A → C) (k : List A → A → ℝ)
    (cost : ℕ) (w : List A) : Prop :=
  2 ^ cost * nodeML counted node w < countedProb counted k w

/-- [proved-derived; formal-checked] **A founding under a node null is a reached likelihood
ratio**: where the null's counted conditionals are a kernel at the node, a founding of the test `k`
means `Q/P ≥ 2^cost` for the sequential law `Q` that is `k` on counted cells and the null on the
opening cells. -/
theorem founds_reaches [Fintype C] {counted : List A → Prop} {node : List A → C}
    {K : C → A → ℝ} (hp0 : ∀ h a, 0 ≤ p h a) (hK0 : ∀ c a, 0 ≤ K c a)
    (hK1 : ∀ c, ∑ a, K c a ≤ 1) (hK : ∀ h, counted h → ∀ a, p h a = K (node h) a)
    {k : List A → A → ℝ} {cost : ℕ} {w : List A} (hf : founds counted node k cost w) :
    reaches p (mix counted k p) (2 ^ cost) w := by
  unfold reaches
  rw [wordProb_eq_counted_mul_open counted p, wordProb_eq_counted_mul_open counted (mix counted k p),
    countedProb_mix, openProb_mix]
  have hle := countedProb_le_nodeML hK0 hK1 hK w
  have ho : 0 ≤ openProb counted p w := openProb_nonneg hp0 w
  have h2 : (0 : ℝ) ≤ 2 ^ cost := by positivity
  calc 2 ^ cost * (countedProb counted p w * openProb counted p w)
      = (2 ^ cost * countedProb counted p w) * openProb counted p w := by ring
    _ ≤ countedProb counted k w * openProb counted p w := by
      refine mul_le_mul_of_nonneg_right ?_ ho
      calc 2 ^ cost * countedProb counted p w ≤ 2 ^ cost * nodeML counted node w :=
            mul_le_mul_of_nonneg_left hle h2
        _ ≤ countedProb counted k w := le_of_lt hf

/-- [proved-derived; formal-checked] **Universal inference over a family, at every horizon.** For
a finite family `F` of candidates, each with a test `k_i` (nonnegative conditionals summing to at
most one), a node map `node_i` and a cost, and a null `p` (a law: nonnegative, summing to one)
whose counted conditionals are, for every candidate of `F`, a subprobability kernel at that
candidate's node: the chance under `p` that some candidate of `F` founds at some read time up to
`N` is at most `Σ_{i∈F} 2^(−cost_i)`, for every `N`. -/
theorem founding_ville {ι : Type*} (F : Finset ι) (cost : ι → ℕ) {C : ι → Type*}
    [∀ i, Fintype (C i)] (counted : List A → Prop) (node : ∀ i, List A → C i)
    (k : ι → List A → A → ℝ) (hk0 : ∀ i h a, 0 ≤ k i h a) (hk1 : ∀ i h, ∑ a, k i h a ≤ 1)
    (hp0 : ∀ h a, 0 ≤ p h a) (hp1 : ∀ h, ∑ a, p h a = 1) (K : ∀ i, C i → A → ℝ)
    (hK0 : ∀ i c a, 0 ≤ K i c a) (hK1 : ∀ i c, ∑ a, K i c a ≤ 1)
    (hK : ∀ i ∈ F, ∀ h, counted h → ∀ a, p h a = K i (node i h) a) (N : ℕ) :
    chance p (fun w => ∃ i ∈ F, founds counted (node i) (k i) (cost i) w) N ≤
      ∑ i ∈ F, ((2 : ℝ) ^ cost i)⁻¹ := by
  calc chance p (fun w => ∃ i ∈ F, founds counted (node i) (k i) (cost i) w) N
      ≤ chance p (fun w => ∃ i ∈ F, reaches p (mix counted (k i) p) (2 ^ cost i) w) N :=
        chance_mono_hit hp0 (fun _ ⟨i, hi, hf⟩ =>
          ⟨i, hi, founds_reaches hp0 (hK0 i) (hK1 i) (hK i hi) hf⟩) N
    _ ≤ ∑ i ∈ F, chance p (reaches p (mix counted (k i) p) (2 ^ cost i)) N :=
        chance_exists_le hp0 F (fun i => reaches p (mix counted (k i) p) (2 ^ cost i)) N
    _ ≤ ∑ i ∈ F, ((2 : ℝ) ^ cost i)⁻¹ := Finset.sum_le_sum fun i _ => by
        rw [← one_div]
        exact ville hp1 (mix_nonneg (hk0 i) hp0) (mix_sum_le (hk1 i) hp1) (by positivity) N

end Founding

/-! ## 6. The helical instance: rings at `(k mod ℓ, y_(k−offset))`, nodes at `(k mod g, ·)` -/

section Helical

variable {A : Type*} [Fintype A] [Nonempty A] {p : List A → A → ℝ}

/-- [definition] **A cell is counted** when its history holds a full context: `k ≥ offset`, where
`k = |h|` counts every ingested cell, the opening context included. -/
def countedAt (offset : ℕ) (h : List A) : Prop := offset ≤ h.length

/-- [definition] **The class `offset` cells back**, `y_(k−offset)` (the history is newest first). -/
def earlier (offset : ℕ) (h : List A) : Option A := h[offset - 1]?

/-- [definition] **A candidate ring's split context**: `(k mod ℓ, y_(k−offset))`. -/
def splitCtx (offset period : ℕ) (h : List A) : ℕ × Option A :=
  (h.length % period, earlier offset h)

/-- [definition] **A node's context**: `(k mod g, y_(k−offset))`. -/
def nodeCtx (offset g : ℕ) (hg : 0 < g) (h : List A) : Fin g × Option A :=
  (⟨h.length % g, Nat.mod_lt _ hg⟩, earlier offset h)

/-- [definition] **The KT sequential law of a context map**: at each cell, the KT face
`(2·seen + 1)/(2·total + |A|)` of the counts already met at the cell's own context
(`FoundingLaw::receive`). -/
def ktTest {C : Type*} (counted : List A → Prop) (ctx : List A → C) (h : List A) (a : A) : ℝ :=
  ((Holonics.Compression.Landmark.Context.Tree.ktFace
    (fun b => cnt counted ctx h (ctx h) b) a : ℚ) : ℝ)

/-- [proved-derived; formal-checked] The KT face is the Rust face: `(n + 1/2)/(t + |A|/2)` is
`(2n + 1)/(2t + |A|)`. -/
theorem ktTest_eq {C : Type*} (counted : List A → Prop) (ctx : List A → C) (h : List A) (a : A) :
    ktTest counted ctx h a =
      (2 * cnt counted ctx h (ctx h) a + 1) / (2 * ∑ b, cnt counted ctx h (ctx h) b + Fintype.card A) := by
  have hk : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  unfold ktTest Holonics.Compression.Landmark.Context.Tree.ktFace Holonics.HNN.RegionCounts.ktProb
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- [proved-derived; formal-checked] The KT test's faces are nonnegative (`ktFace_pos`). -/
theorem ktTest_nonneg {C : Type*} (counted : List A → Prop) (ctx : List A → C) (h : List A)
    (a : A) : 0 ≤ ktTest counted ctx h a := by
  unfold ktTest
  exact_mod_cast (Holonics.Compression.Landmark.Context.Tree.ktFace_pos _ a).le

/-- [proved-derived; formal-checked] The KT test's faces sum to one (`ktFace_sum`). -/
theorem ktTest_sum {C : Type*} (counted : List A → Prop) (ctx : List A → C) (h : List A) :
    ∑ a, ktTest counted ctx h a = 1 := by
  unfold ktTest
  rw [← Rat.cast_sum, Holonics.Compression.Landmark.Context.Tree.ktFace_sum, Rat.cast_one]

/-- [definition] **Ring `ℓ` founds** at a history: its KT split law at `(k mod ℓ, y_(k−offset))`
beats `2^cost` times the maximum likelihood at its node `g = gcd(ℓ, cell_clock)`. -/
def ringFounds (offset clock : ℕ) (hclock : 0 < clock) (period cost : ℕ) (w : List A) : Prop :=
  founds (countedAt offset) (nodeCtx offset (Nat.gcd period clock) (Nat.gcd_pos_of_pos_right _ hclock))
    (ktTest (countedAt offset) (splitCtx offset period)) cost w

/-- [proved-derived; formal-checked] **`founding_universal_inference`** (#398). On a finite
alphabet, with a positive offset and cell clock and a finite family `F` of periods with costs fixed
before the stream: under any law `p` whose class `y_k` at every counted cell depends on the past,
for each candidate `ℓ ∈ F`, only through `(k mod gcd(ℓ, clock), y_(k−offset))` (a kernel `K ℓ`),
the chance that any ring of `F` founds at some read time up to `N` is at most `Σ_{ℓ∈F} 2^(−cost_ℓ)`,
for every horizon `N`. -/
theorem founding_universal_inference (offset clock : ℕ) (hclock : 0 < clock) (F : Finset ℕ)
    (cost : ℕ → ℕ) (hp0 : ∀ h a, 0 ≤ p h a) (hp1 : ∀ h, ∑ a, p h a = 1)
    (K : ℕ → ℕ → Option A → A → ℝ) (hK0 : ∀ ℓ r y a, 0 ≤ K ℓ r y a)
    (hK1 : ∀ ℓ r y, ∑ a, K ℓ r y a ≤ 1)
    (hK : ∀ ℓ ∈ F, ∀ h : List A, offset ≤ h.length → ∀ a,
      p h a = K ℓ (h.length % Nat.gcd ℓ clock) (earlier offset h) a) (N : ℕ) :
    chance p (fun w => ∃ ℓ ∈ F, ringFounds offset clock hclock ℓ (cost ℓ) w) N ≤
      ∑ ℓ ∈ F, ((2 : ℝ) ^ cost ℓ)⁻¹ :=
  founding_ville F cost (countedAt offset)
    (fun ℓ => nodeCtx offset (Nat.gcd ℓ clock) (Nat.gcd_pos_of_pos_right _ hclock))
    (fun ℓ => ktTest (countedAt offset) (splitCtx offset ℓ))
    (fun _ h a => ktTest_nonneg _ _ h a) (fun _ h => (ktTest_sum _ _ h).le) hp0 hp1
    (fun ℓ c a => K ℓ c.1.val c.2 a) (fun ℓ _ a => hK0 ℓ _ _ a) (fun ℓ _ => hK1 ℓ _ _)
    (fun ℓ hℓ h hh a => hK ℓ hℓ h hh a) N

/-- [proved-derived; formal-checked] **One null for the whole family**: a law depending at counted
cells only on `(k mod g, y_(k−offset))`, with `g` dividing every candidate's node
`gcd(ℓ, clock)`, satisfies the hypothesis of `founding_universal_inference` for every candidate. -/
theorem founding_universal_inference_of_dvd (offset clock : ℕ) (hclock : 0 < clock)
    (F : Finset ℕ) (cost : ℕ → ℕ) (hp0 : ∀ h a, 0 ≤ p h a) (hp1 : ∀ h, ∑ a, p h a = 1)
    (g : ℕ) (hg : ∀ ℓ ∈ F, g ∣ Nat.gcd ℓ clock) (K : ℕ → Option A → A → ℝ)
    (hK0 : ∀ r y a, 0 ≤ K r y a) (hK1 : ∀ r y, ∑ a, K r y a ≤ 1)
    (hK : ∀ h : List A, offset ≤ h.length → ∀ a, p h a = K (h.length % g) (earlier offset h) a)
    (N : ℕ) :
    chance p (fun w => ∃ ℓ ∈ F, ringFounds offset clock hclock ℓ (cost ℓ) w) N ≤
      ∑ ℓ ∈ F, ((2 : ℝ) ^ cost ℓ)⁻¹ :=
  founding_universal_inference offset clock hclock F cost hp0 hp1 (fun _ r y a => K (r % g) y a)
    (fun _ r y a => hK0 _ y a) (fun _ r y => hK1 _ y)
    (fun ℓ hℓ h hh a => by rw [Nat.mod_mod_of_dvd _ (hg ℓ hℓ)]; exact hK h hh a) N

/-- [proved-derived; formal-checked] **The guarantee is not vacuous**: when `open`'s family bound
is below one, so is the chance of any founding, at every horizon, and so is its supremum over the
horizons (the chance of a founding at any read time ever, as the limit of a nondecreasing
sequence: `chance_mono_horizon`). -/
theorem founding_below_one (offset clock : ℕ) (hclock : 0 < clock) (F : Finset ℕ)
    (cost : ℕ → ℕ) (hp0 : ∀ h a, 0 ≤ p h a) (hp1 : ∀ h, ∑ a, p h a = 1)
    (K : ℕ → ℕ → Option A → A → ℝ) (hK0 : ∀ ℓ r y a, 0 ≤ K ℓ r y a)
    (hK1 : ∀ ℓ r y, ∑ a, K ℓ r y a ≤ 1)
    (hK : ∀ ℓ ∈ F, ∀ h : List A, offset ≤ h.length → ∀ a,
      p h a = K ℓ (h.length % Nat.gcd ℓ clock) (earlier offset h) a)
    (hF : ∑ ℓ ∈ F, ((2 : ℝ) ^ cost ℓ)⁻¹ < 1) :
    (∀ N, chance p (fun w => ∃ ℓ ∈ F, ringFounds offset clock hclock ℓ (cost ℓ) w) N < 1) ∧
      (⨆ N, chance p (fun w => ∃ ℓ ∈ F, ringFounds offset clock hclock ℓ (cost ℓ) w) N) ≤
        ∑ ℓ ∈ F, ((2 : ℝ) ^ cost ℓ)⁻¹ := by
  have hb := founding_universal_inference offset clock hclock F cost hp0 hp1 K hK0 hK1 hK
  exact ⟨fun N => lt_of_le_of_lt (hb N) hF, ciSup_le hb⟩

end Helical

end Holonics.HNN.FoundingVille

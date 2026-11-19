import HolonicsResearch.HNN.EffectiveTension

/-!
# Laps found by composition: a reread leaves the tension, a founding lowers it, foundings are few

The record `research/records/2026-10-25_A_LAP_OVER_THE_SAME_TEXT_FOUNDS_ONLY_WHAT_THE_LAST_LAP_MADE_REACHABLE_SO_LEARNING_CLIMBS_STAIRCASES_AND_STEPS_AT_EACH_FOUNDING.md`
(§§1 to 5) runs the founding law of October 24 lap after lap over one passage: each lap reads the
moments `(H, B, T)` of its present faces, founds the candidates that pass their charge, and stops
at a lap that founds nothing. #410's box "Laps found by composition" asks for four statements; this
file proves them on `HNN/EffectiveTension`'s weighted moments and generalized inverses.

[proved-standard; formal-checked] What is proved.

1. **A reread leaves the tension** (`tension_eq_of_moments`). The tension `T − B G Bᵀ` is read off
   `(H, B, T)` alone: two reads, over any cells and weights, whose three moments agree leave one
   tension for every generalized inverse of each face Gram. A reread of one passage at one
   constitution meets the same moments, so a lap that founds nothing leaves the tension it met.
2. **Founding lowers the tension by `M G_Q Mᵀ ⪰ 0`** (`founding_le`, `founding_drop_posSemidef`,
   `founds_nothing_of_crossRemainder_eq_zero`). Reading a candidate `c` beside the face never raises
   the tension (the face is a read of the joint face), so with `EffectiveTension.tension_fromRows`
   the drop `M G_Q Mᵀ` is positive semidefinite for every generalized inverse `G_Q` of `Q`, and a
   candidate with `M = 0` founds nothing.
3. **Over laps** (`foundedRows`, `lapFace`, `lapTension`, `lapFace_factor`, `lapTension_le`,
   `lapTension_antitone`, `lap_fixed_point`, `lapTension_fixed`, `founds_nothing_until_added`). A
   lap's face is the opening face beside the candidates founded so far, the others read at zero; a
   smaller founded set is a read of a larger one, so the tension is non-increasing over laps whose
   founded sets grow. When each lap's founded set is a function of the last (item 1), a lap that
   founds nothing is a fixed point: every later lap founds nothing and the tension stands. A
   candidate whose `M` vanished at a lap founds nothing at every later lap with the same founded
   set, that is, until a face is added.
4. **The count of foundings** (`foundings_card_mul_le`, `foundings_card_le`, `foundings_finite`). A
   code that never rises from lap to lap, falls by at least `c_min > 0` at each founding and stands
   above `L_floor` admits at most `(L₀ − L_floor) / c_min` founding laps in any window, so only
   finitely many laps found.

Limits. The candidates are one finite family read at the cells, and the founded set grows inside
it; that a lap's pool is the products of the present faces, the founding rule itself (the leading
`M Q⁺ Mᵀ` against the charge), reach at most doubling per lap, and the record's witnesses on
`{±1}⁵` (`S = 96 → 64 → 32`, checked in its receipt `laps_found.py`) are not stated: the rule enters
only as a function of the founded set. The code `L` of item 4 is a hypothesis, the scalar chart that
reads it from the tension (`(N/2) log₂ S` for a scalar covector) is not built, and the charge's
lower bound `½ log₂ N` is the record's.

The computational object is the helical pair interaction: the covector meets the present faces at
a contact, the tension is what the contact cannot bridge, and a founded candidate is a new face
whose contact carries part of it. Of the winding guide's six general objects this touches the pair
(the contact's tension), faces and placement (which faces are founded, lap by lap) and the tube (a
lap is a pass over the passage's span); the helix, the cell holonomy and the tower thread stay
attached.

Consumers: the atlas rows `contact.lap-founds-reachable`, `contact.charge-falls-with-evidence` and
`contact.lap-stop-inertia`, and #410's box "Laps found by composition".

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix Finset
open scoped MatrixOrder

namespace Holonics.HNN.LapsByComposition

open EffectiveTension

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n m o p : Type*}
variable {w : ι → ℝ}

/-! ## 1. A reread at one constitution returns the same tension -/

/-- [proved-standard; formal-checked] **The tension is read off `(H, B, T)` alone.** Two reads
whose face Gram, cross moment and covector Gram agree, over any cells and weights and with any
generalized inverses, leave one tension; a reread of one passage at one constitution meets the
same moments, so a lap that founds nothing leaves the tension it met. -/
theorem tension_eq_of_moments [Fintype n] [DecidableEq n] [Fintype o] {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] (A : Matrix n ι ℝ) (Y : Matrix o ι ℝ) (A' : Matrix n ι' ℝ)
    (Y' : Matrix o ι' ℝ) {w' : ι' → ℝ} (hw : ∀ t, 0 ≤ w t)
    (hH : moment A A w = moment A' A' w') (hB : moment Y A w = moment Y' A' w')
    (hT : moment Y Y w = moment Y' Y' w') {G G' : Matrix n n ℝ} (hG : IsGInv (moment A A w) G)
    (hG' : IsGInv (moment A' A' w') G') : tension A Y w G = tension A' Y' w' G' := by
  have hG'' : IsGInv (moment A A w) G' := by rw [hH]; exact hG'
  rw [tension_eq_of_isGInv A Y hw hG hG'', tension, tension, hT, hB, ← moment_transpose Y A,
    ← moment_transpose Y' A', hB]

/-! ## 2. Founding lowers the tension by `M Q⁺ Mᵀ ⪰ 0` -/

/-- [proved-standard; formal-checked] **Founding never raises the tension**: reading a candidate
beside the face leaves at most the face's tension. -/
theorem founding_le [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype o]
    (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) {G' : Matrix (n ⊕ m) (n ⊕ m) ℝ}
    (hG' : IsGInv (moment (fromRows A Cf) (fromRows A Cf) w) G') :
    tension (fromRows A Cf) Y w G' ≤ tension A Y w G :=
  tension_le_of_factor (fromRows A Cf) A (fromCols 1 0)
    (by rw [fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero]) Y hw hG' hG

/-- [proved-standard; formal-checked] **The drop `M G_Q Mᵀ` is positive semidefinite**, for every
generalized inverse `G_Q` of the candidate's residual Gram `Q`. -/
theorem founding_drop_posSemidef [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    [Fintype o] (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) {GQ : Matrix m m ℝ}
    (hGQ : IsGInv (faceRemainder A Cf w G) GQ) :
    (crossRemainder A Cf Y w G * GQ * (crossRemainder A Cf Y w G)ᵀ).PosSemidef := by
  obtain ⟨G', hG'⟩ := exists_isGInv (fromRows A Cf) w
  have h := founding_le A Cf Y hw hG hG'
  rw [tension_fromRows A Cf Y hw hG hGQ hG', le_iff, sub_sub_cancel] at h
  exact h

/-- [proved-standard; formal-checked] **A candidate with `M = 0` founds nothing**: its reading
beside the face leaves the tension the face met. -/
theorem founds_nothing_of_crossRemainder_eq_zero [Fintype n] [DecidableEq n] [Fintype m]
    [DecidableEq m] [Fintype o] (A : Matrix n ι ℝ) (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ)
    (hw : ∀ t, 0 ≤ w t) {G : Matrix n n ℝ} (hG : IsGInv (moment A A w) G) {GQ : Matrix m m ℝ}
    (hGQ : IsGInv (faceRemainder A Cf w G) GQ) {G' : Matrix (n ⊕ m) (n ⊕ m) ℝ}
    (hG' : IsGInv (moment (fromRows A Cf) (fromRows A Cf) w) G')
    (hM : crossRemainder A Cf Y w G = 0) : tension (fromRows A Cf) Y w G' = tension A Y w G := by
  rw [tension_fromRows A Cf Y hw hG hGQ hG', hM, Matrix.zero_mul, Matrix.zero_mul, sub_zero]

/-! ## 3. Laps: a growing set of founded candidates -/

/-- [definition] The candidates founded in `F`, the others read at zero. -/
def foundedRows [DecidableEq p] (Cand : Matrix p ι ℝ) (F : Finset p) : Matrix p ι ℝ :=
  fun i t => if i ∈ F then Cand i t else 0

/-- [definition] A lap's face: the opening face `A` beside the founded candidates. -/
def lapFace [DecidableEq p] (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) (F : Finset p) :
    Matrix (n ⊕ p) ι ℝ :=
  fromRows A (foundedRows Cand F)

/-- [definition] A lap's tension, read with the Moore–Penrose inverse of its face Gram. -/
noncomputable def lapTension [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) (Y : Matrix o ι ℝ) (w : ι → ℝ) (F : Finset p) :
    Matrix o o ℝ :=
  tension (lapFace A Cand F) Y w (pinv (isHermitian_moment (lapFace A Cand F) w))

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] A smaller founded set is a read of a larger one. -/
theorem lapFace_factor [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) {F F' : Finset p} (hF : F ⊆ F') :
    lapFace A Cand F =
      fromBlocks 1 0 0 (diagonal fun i => if i ∈ F then (1 : ℝ) else 0) * lapFace A Cand F' := by
  rw [lapFace, lapFace, fromBlocks_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero,
    Matrix.zero_mul, zero_add]
  congr 1
  ext i t
  simp only [foundedRows, diagonal_mul]
  by_cases hi : i ∈ F
  · simp [hi, hF hi]
  · simp [hi]

/-- [proved-standard; formal-checked] **The tension does not rise as candidates are founded.** -/
theorem lapTension_le [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype o]
    (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {F F' : Finset p} (hF : F ⊆ F') : lapTension A Cand Y w F' ≤ lapTension A Cand Y w F :=
  tension_le_of_factor _ _ _ (lapFace_factor A Cand hF) Y hw (pinv_isGInv _) (pinv_isGInv _)

/-- [proved-standard; formal-checked] **The tension is non-increasing over laps** whose founded
sets grow. -/
theorem lapTension_antitone [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p] [Fintype o]
    (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t)
    {F : ℕ → Finset p} (hF : Monotone F) : Antitone fun k => lapTension A Cand Y w (F k) :=
  fun _ _ hkj => lapTension_le A Cand Y hw (hF hkj)

/-- [proved-standard; formal-checked] **A lap rule read off the founded set has a fixed point that
holds**: when each lap's founded set is a function of the last one (a reread at one constitution
meets the same moments) and one lap founds nothing, every later lap founds nothing. -/
theorem lap_fixed_point {α : Type*} (step : α → α) (F : ℕ → α) (hF : ∀ k, F (k + 1) = step (F k))
    {k₀ : ℕ} (hfix : step (F k₀) = F k₀) : ∀ j, k₀ ≤ j → F j = F k₀ := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => rfl
  | succ j _ ih => rw [hF, ih, hfix]

/-- [proved-standard; formal-checked] At the fixed point the tension stands at every later lap. -/
theorem lapTension_fixed [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ) (Y : Matrix o ι ℝ)
    (step : Finset p → Finset p) (F : ℕ → Finset p) (hF : ∀ k, F (k + 1) = step (F k))
    {k₀ : ℕ} (hfix : step (F k₀) = F k₀) (j : ℕ) (hj : k₀ ≤ j) :
    lapTension A Cand Y w (F j) = lapTension A Cand Y w (F k₀) := by
  rw [lap_fixed_point step F hF hfix j hj]

/-- [proved-standard; formal-checked] **A candidate with `M = 0` stays unfounded until a face is
added**: at every later lap whose founded set is the one at which its `M` vanished, it founds
nothing. -/
theorem founds_nothing_until_added [Fintype n] [DecidableEq n] [Fintype p] [DecidableEq p]
    [Fintype m] [DecidableEq m] [Fintype o] (A : Matrix n ι ℝ) (Cand : Matrix p ι ℝ)
    (Cf : Matrix m ι ℝ) (Y : Matrix o ι ℝ) (hw : ∀ t, 0 ≤ w t) {F : ℕ → Finset p} {k j : ℕ}
    (hsame : F j = F k)
    (hM : crossRemainder (lapFace A Cand (F k)) Cf Y w
      (pinv (isHermitian_moment (lapFace A Cand (F k)) w)) = 0)
    {GQ : Matrix m m ℝ} (hGQ : IsGInv (faceRemainder (lapFace A Cand (F j)) Cf w
      (pinv (isHermitian_moment (lapFace A Cand (F j)) w))) GQ)
    {G' : Matrix ((n ⊕ p) ⊕ m) ((n ⊕ p) ⊕ m) ℝ}
    (hG' : IsGInv (moment (fromRows (lapFace A Cand (F j)) Cf)
      (fromRows (lapFace A Cand (F j)) Cf) w) G') :
    tension (fromRows (lapFace A Cand (F j)) Cf) Y w G' = lapTension A Cand Y w (F j) := by
  rw [← hsame] at hM
  exact founds_nothing_of_crossRemainder_eq_zero _ Cf Y hw (pinv_isGInv _) hGQ hG' hM

/-! ## 4. The count of foundings -/

/-- [proved-standard; formal-checked] **The foundings are at most `(L₀ − L_floor)/c_min`**: a code
that never rises from lap to lap, falls by at least `c_min` at each founding and stands above
`L_floor` admits at most that many founding laps, in any window of laps. -/
theorem foundings_card_mul_le (L : ℕ → ℝ) (founds : ℕ → Prop) [DecidablePred founds]
    {c Lfloor : ℝ} (hstep : ∀ k, L (k + 1) + (if founds k then c else 0) ≤ L k)
    (hfloor : ∀ k, Lfloor ≤ L k) (K : ℕ) :
    ((range K).filter founds).card * c ≤ L 0 - Lfloor := by
  have hsum : ∀ K, ∑ k ∈ range K, (if founds k then c else 0) ≤ L 0 - L K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ]
      linarith [hstep K]
  have h := hsum K
  rw [← sum_filter, sum_const, nsmul_eq_mul] at h
  linarith [hfloor K]

/-- [proved-standard; formal-checked] The count bound divided by the charge. -/
theorem foundings_card_le (L : ℕ → ℝ) (founds : ℕ → Prop) [DecidablePred founds]
    {c Lfloor : ℝ} (hc : 0 < c) (hstep : ∀ k, L (k + 1) + (if founds k then c else 0) ≤ L k)
    (hfloor : ∀ k, Lfloor ≤ L k) (K : ℕ) :
    (((range K).filter founds).card : ℝ) ≤ (L 0 - Lfloor) / c := by
  rw [le_div_iff₀ hc]
  exact foundings_card_mul_le L founds hstep hfloor K

/-- [proved-standard; formal-checked] **The lap loop stops founding**: under the same hypotheses
only finitely many laps found. -/
theorem foundings_finite (L : ℕ → ℝ) (founds : ℕ → Prop) [DecidablePred founds]
    {c Lfloor : ℝ} (hc : 0 < c) (hstep : ∀ k, L (k + 1) + (if founds k then c else 0) ≤ L k)
    (hfloor : ∀ k, Lfloor ≤ L k) : {k | founds k}.Finite := by
  by_contra hinf
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (⌊(L 0 - Lfloor) / c⌋₊ + 1)
  have hsub : s ⊆ (range (s.sup id + 1)).filter founds := by
    intro k hk
    rw [mem_filter, mem_range]
    exact ⟨Nat.lt_succ_of_le (le_sup (f := id) hk), hs hk⟩
  have h1 := foundings_card_le L founds hc hstep hfloor (s.sup id + 1)
  have h2 : (s.card : ℝ) ≤ (((range (s.sup id + 1)).filter founds).card : ℝ) := by
    exact_mod_cast card_le_card hsub
  rw [hcard] at h2
  have h3 : (L 0 - Lfloor) / c < (⌊(L 0 - Lfloor) / c⌋₊ + 1 : ℕ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  linarith

end Holonics.HNN.LapsByComposition

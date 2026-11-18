import Mathlib

/-!
# Identity is what the modes share: relative phases up to one common turn, ratios up to one common shift

Brandon's lens of November 13 (joined to its owners in the junction record,
`research/records/2026-11-13_THE_TICK_HOLDS_THE_JUNCTIONS_ANCHOR_WITHOUT_ITS_RETURN_…`, §2 to §4), the chord record of
November 10 (`research/records/2026-11-10_A_CHORD_IS_CIRCLES_CLOSING_AT_THEIR_LEAST_COMMON_MULTIPLE_…`, §2.7) and the
cipher record of November 16 (`research/records/2026-11-16_A_CODE_READ_WITHOUT_ITS_KEY_IS_A_CIPHER_…`, §4) say one thing in
three charts: what a receiver can hold of a source is the pattern its modes share, and a change of frame that moves every
mode together is no part of it. This file states that as theorems, with the three joins of the junction record that #410
owes beside it.

[proved-standard; formal-checked] What is proved.

1. **Identity by shared phases and modes** (`shared_relative_iff`): two complex mode vectors have the same relative
   readings `z_i · conj z_j` on every pair of modes exactly when one is the other turned by one common unit phase. The
   pair readings hold every mode's power (`relative_self`) and every phase difference, and they are blind to the common
   turn (`relative_common_phase`). In the real chart the common turn is a half-turn (`shared_products_iff_real`).
2. **Ratios modulo a common shift** (`shared_ratios_iff`): two positive spectra have the same ratio on every pair of lines
   exactly when one is the other scaled by one positive factor (a Doppler shift, a transposition); in the log chart the
   factor is a translation (`log_shift`).
3. **Lines close on cycles** (`lines_sum_zero_on_cycle`): lines that are differences of term values (Ritz) sum to zero
   around every closed walk of transitions.
4. **A merge loses which, never how much** (`merge_inside_level`, `merge_ker_le`, `iterate_merge_inside_level`): if a map
   conserves a quantity, any two states it merges have one value of that quantity, so every fibre of a merge lies inside
   one level set of every conserved quantity (the junction record, §2; atlas `standing.merge-inside-conserved-level`).
5. **What a place carries is bounded by its state's surprise to its reader** (`joint_le_marginal`, `worth_le_surprise`):
   for any joint law, `ln(p(y|z)/p(y)) ≤ −ln p(z)` (atlas `landmark.pin-worth-surprise`, `landmark.carry-worth-state`),
   with the witness that attains it (`fair_bit_worth`): a row whose state is a far fair bit is worth `ln 2` to a reader
   of that bit, while a constant symbol at its place has no news (`constant_symbol_no_news`).
6. **Two receipts of one source read their paths with the source absent** (`cross_relation`): for commuting kernels,
   `K₂ (K₁ s) = K₁ (K₂ s)` (atlas `receipt.two-kernel-cross-relation`).
7. **More receivers, a finer kernel** (`familyKer_antitone`, `familyQuotient_surjective`): for receiver families
   `ℛ₁ ⊆ ℛ₂`, the kernel of `ℛ₂` lies inside the kernel of `ℛ₁`, and the retained quotient under `ℛ₂` maps onto the one
   under `ℛ₁` (atlas `compression.receiver-family-kernel-antitone`).

Limits. Statement 1 is the finite-dimensional algebra of the reduced space (the relative phases); it does not construct
the moment map or its level sets (`frame.moment-map-loudness-colour` keeps Needham and Shonkwiler's theorem as the
literature's). Statement 3 is the direction from term values to closure; the converse (a family of ratios whose every
cycle closes is one law's) is `aeon.kolmogorov-converse` in its owner. Statement 5 is stated on a finite joint law given
as nonnegative weights; conditioning on a context is the same statement on the law conditioned.

The computational object is the helical pair interaction: a relative reading is a pair's face, the common turn is the
receiver's gauge, and a ratio is carried as its undivided pair. Of the winding guide's six general objects this touches
the pair (the relative reading) and faces and placement (what a change of frame keeps); the helix, cell holonomy, tube
and tower thread stay attached.

Consumers: #410's box "a merge's fibres and a row's worth"; the atlas rows named above; `holon.song-is-a-family`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.SharedModes

open Complex ComplexConjugate

/-! ## 1. Identity by shared phases and modes -/

section Relative

variable {ι : Type*}

/-- [definition] **The relative reading of a pair of modes**: `z_i · conj z_j`, of size `|z_i||z_j|` and phase the
difference of the two modes' phases. On the diagonal it is a mode's power. -/
def relative (z : ι → ℂ) (i j : ι) : ℂ := z i * conj (z j)

/-- [proved-standard] On the diagonal the relative reading is the mode's power. -/
theorem relative_self (z : ι → ℂ) (i : ι) : relative z i i = (Complex.normSq (z i) : ℂ) := by
  unfold relative
  rw [Complex.mul_conj]

/-- [proved-standard] **A common turn is invisible to every pair**: turning every mode by one unit phase leaves every
relative reading where it was. -/
theorem relative_common_phase (z : ι → ℂ) {u : ℂ} (hu : ‖u‖ = 1) (i j : ι) :
    relative (fun k => u * z k) i j = relative z i j := by
  unfold relative
  have h : u * conj u = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
  rw [map_mul]
  calc u * z i * (conj u * conj (z j)) = (u * conj u) * (z i * conj (z j)) := by ring
    _ = z i * conj (z j) := by rw [h, one_mul]

/-- [proved-standard] **Identity by shared phases and modes**: two mode vectors share every relative reading exactly
when one is the other turned by one common unit phase. What the pairs hold is the whole vector but for the receiver's
own gauge. -/
theorem shared_relative_iff (z w : ι → ℂ) :
    (∀ i j, relative w i j = relative z i j) ↔ ∃ u : ℂ, ‖u‖ = 1 ∧ ∀ i, w i = u * z i := by
  constructor
  · intro h
    by_cases hz : ∀ i, z i = 0
    · refine ⟨1, by simp, fun i => ?_⟩
      have := h i i
      unfold relative at this
      rw [hz i, zero_mul, Complex.mul_conj] at this
      have h0 : Complex.normSq (w i) = 0 := by exact_mod_cast this
      rw [Complex.normSq_eq_zero.mp h0, hz i, mul_zero]
    · push Not at hz
      obtain ⟨j, hj⟩ := hz
      have hjj := h j j
      unfold relative at hjj
      rw [Complex.mul_conj, Complex.mul_conj] at hjj
      have hn : Complex.normSq (w j) = Complex.normSq (z j) := by exact_mod_cast hjj
      have hwj : w j ≠ 0 := by
        intro h0
        rw [h0, Complex.normSq_zero] at hn
        exact hj (Complex.normSq_eq_zero.mp hn.symm)
      refine ⟨w j / z j, ?_, fun i => ?_⟩
      · rw [norm_div]
        have : ‖w j‖ = ‖z j‖ := by
          have h1 : ‖w j‖ ^ 2 = ‖z j‖ ^ 2 := by
            rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hn]
          exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h1
        rw [this, div_self (norm_ne_zero_iff.mpr hj)]
      · have hij := h i j
        unfold relative at hij
        have hcw : conj (w j) ≠ 0 := by simpa using hwj
        have h1 : w i = z i * conj (z j) / conj (w j) := by
          field_simp
          exact hij
        have h2 : conj (z j) / conj (w j) = w j / z j := by
          rw [div_eq_div_iff hcw hj, mul_comm (conj (z j)) (z j), Complex.mul_conj, Complex.mul_conj, hn]
        rw [h1, mul_div_assoc, h2]; ring
  · rintro ⟨u, hu, hw⟩ i j
    have : w = fun k => u * z k := funext hw
    rw [this]
    exact relative_common_phase z hu i j

/-- [proved-standard] **The real chart keeps a half-turn of gauge**: two real mode vectors share every pair product
exactly when they are equal or one is the other's half-turn. -/
theorem shared_products_iff_real (z w : ι → ℝ) :
    (∀ i j, w i * w j = z i * z j) ↔ (∀ i, w i = z i) ∨ (∀ i, w i = -z i) := by
  constructor
  · intro h
    by_cases hz : ∀ i, z i = 0
    · left
      intro i
      have := h i i
      rw [hz i, mul_zero] at this
      rw [hz i]
      exact mul_self_eq_zero.mp this
    · push Not at hz
      obtain ⟨j, hj⟩ := hz
      have hjj := h j j
      rcases mul_self_eq_mul_self_iff.mp hjj with hw | hw
      · left
        intro i
        have := h i j
        rw [hw] at this
        exact mul_right_cancel₀ hj this
      · right
        intro i
        have := h i j
        rw [hw] at this
        have h3 : -w i * z j = z i * z j := by rw [← this]; ring
        have := mul_right_cancel₀ hj h3
        linarith
  · rintro (h | h) i j
    · rw [h i, h j]
    · rw [h i, h j]; ring

end Relative

/-! ## 2. Ratios modulo a common shift -/

section Ratios

variable {ι : Type*}

/-- [proved-standard] **Identity is a pattern of ratios modulo a common shift**: two positive spectra have the same
ratio on every pair of lines exactly when one is the other scaled by one positive factor. The factor is the state of
motion (a Doppler shift) or the key (a transposition); the ratios are the species. -/
theorem shared_ratios_iff (f g : ι → ℝ) (hf : ∀ i, 0 < f i) (hg : ∀ i, 0 < g i) :
    (∀ i j, g i / g j = f i / f j) ↔ ∃ k : ℝ, 0 < k ∧ ∀ i, g i = k * f i := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty ι with hι | ⟨⟨j⟩⟩
    · exact ⟨1, one_pos, fun i => (hι.false i).elim⟩
    · refine ⟨g j / f j, div_pos (hg j) (hf j), fun i => ?_⟩
      have hij := h i j
      have hgj := (hg j).ne'
      have hfj := (hf j).ne'
      field_simp at hij ⊢
      linarith
  · rintro ⟨k, hk, h⟩ i j
    rw [h i, h j]
    have hfj := (hf j).ne'
    have hk' := hk.ne'
    field_simp

/-- [proved-standard] In the log chart a common factor is a translation: every line moves by `log k`, so every
interval between lines stays. -/
theorem log_shift (f : ι → ℝ) (hf : ∀ i, 0 < f i) {k : ℝ} (hk : 0 < k) (i : ι) :
    Real.log (k * f i) = Real.log k + Real.log (f i) :=
  Real.log_mul hk.ne' (hf i).ne'

/-- [proved-standard] The interval between two lines in the log chart is untouched by a common factor. -/
theorem log_interval_invariant (f : ι → ℝ) (hf : ∀ i, 0 < f i) {k : ℝ} (hk : 0 < k) (i j : ι) :
    Real.log (k * f i) - Real.log (k * f j) = Real.log (f i) - Real.log (f j) := by
  rw [log_shift f hf hk i, log_shift f hf hk j]; ring

end Ratios

/-! ## 3. Lines close on cycles -/

/-- [proved-standard] **Ritz's combination on a closed walk**: lines that are differences of term values sum to zero
around every closed walk of transitions, so the lines of a spectrum are a cochain that closes on every cycle. -/
theorem lines_sum_zero_on_cycle {ι A : Type*} [AddCommGroup A] (T : ι → A) (c : ℕ → ι) (n : ℕ)
    (hclosed : c n = c 0) :
    ∑ k ∈ Finset.range n, (T (c (k + 1)) - T (c k)) = 0 := by
  rw [Finset.sum_range_sub (fun k => T (c k)) n, hclosed, sub_self]

/-! ## 4. A merge loses which, never how much -/

section Merge

variable {X Q : Type*}

/-- [proved-derived] **A merge's fibres lie inside the level sets of what it conserves**: if `Φ` conserves `q` and
merges `a` and `b`, then `q a = q b`. What the merge loses is which state it was, never how much of `q` it held. -/
theorem merge_inside_level (Φ : X → X) (q : X → Q) (hq : ∀ x, q (Φ x) = q x) {a b : X}
    (h : Φ a = Φ b) : q a = q b := by
  rw [← hq a, ← hq b, h]

/-- [proved-derived] The same as an order of partitions: the kernel of a merge refines the kernel of every quantity it
conserves. -/
theorem merge_ker_le (Φ : X → X) (q : X → Q) (hq : ∀ x, q (Φ x) = q x) :
    Setoid.ker Φ ≤ Setoid.ker q := fun _ _ h => merge_inside_level Φ q hq h

/-- [proved-derived] A conserved quantity is conserved along the whole orbit. -/
theorem conserved_iterate (Φ : X → X) (q : X → Q) (hq : ∀ x, q (Φ x) = q x) (n : ℕ) (x : X) :
    q (Φ^[n] x) = q x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, ih, hq]

/-- [proved-derived] States merged after any number of steps still share every conserved quantity: the level outlives
the merge at every length. -/
theorem iterate_merge_inside_level (Φ : X → X) (q : X → Q) (hq : ∀ x, q (Φ x) = q x) (n : ℕ)
    {a b : X} (h : Φ^[n] a = Φ^[n] b) : q a = q b := by
  rw [← conserved_iterate Φ q hq n a, ← conserved_iterate Φ q hq n b, h]

end Merge

/-! ## 5. What a place carries is bounded by its state's surprise to its reader -/

section Worth

variable {Z Y : Type*} [Fintype Z] [Fintype Y]

/-- [definition] The marginal of the target under a joint weight. -/
def marginalTarget (p : Z → Y → ℝ) (y : Y) : ℝ := ∑ z, p z y

/-- [definition] The marginal of the row's state under a joint weight. -/
def marginalState (p : Z → Y → ℝ) (z : Z) : ℝ := ∑ y, p z y

omit [Fintype Y] in
/-- [proved-derived] One term of a sum of nonnegative terms: `p(z, y) ≤ p(y)`. -/
theorem joint_le_marginal (p : Z → Y → ℝ) (hp : ∀ z y, 0 ≤ p z y) (z : Z) (y : Y) :
    p z y ≤ marginalTarget p y :=
  Finset.single_le_sum (f := fun z => p z y) (fun z _ => hp z y) (Finset.mem_univ z)

/-- [proved-derived] **A row's worth to a reader is bounded by the surprise of the row's state to that reader**: for
any joint law of a state `z` and a target `y`, `ln(p(y|z)/p(y)) ≤ −ln p(z)`, where `p(y|z) = p(z, y)/p(z)`. A state that
was certain to its reader passes nothing on. -/
theorem worth_le_surprise (p : Z → Y → ℝ) (hp : ∀ z y, 0 ≤ p z y) (z : Z) (y : Y)
    (hzy : 0 < p z y) :
    Real.log ((p z y / marginalState p z) / marginalTarget p y) ≤ -Real.log (marginalState p z) := by
  have hy : 0 < marginalTarget p y := lt_of_lt_of_le hzy (joint_le_marginal p hp z y)
  have hz : 0 < marginalState p z :=
    lt_of_lt_of_le hzy
      (Finset.single_le_sum (f := fun y => p z y) (fun y _ => hp z y) (Finset.mem_univ y))
  rw [← Real.log_inv]
  apply Real.log_le_log (by positivity)
  rw [div_div, div_le_iff₀ (by positivity)]
  calc p z y ≤ marginalTarget p y := joint_le_marginal p hp z y
    _ = (marginalState p z)⁻¹ * (marginalState p z * marginalTarget p y) := by
        field_simp

/-- [definition] The witness: a row's state and a reader's target are one far fair bit. -/
noncomputable def fairBit (z y : Bool) : ℝ := if z = y then 1 / 2 else 0

/-- [proved-derived] **The witness attains the bound**: where a row's state is a fair bit and the target is that bit,
the row is worth `ln 2` to the reader, which is the surprise of the row's state. -/
theorem fair_bit_worth (b : Bool) :
    Real.log ((fairBit b b / marginalState fairBit b) / marginalTarget fairBit b) = Real.log 2 ∧
      -Real.log (marginalState fairBit b) = Real.log 2 := by
  have hs : marginalState fairBit b = 1 / 2 := by
    cases b <;> simp [marginalState, fairBit]
  have ht : marginalTarget fairBit b = 1 / 2 := by
    cases b <;> simp [marginalTarget, fairBit]
  have hbb : fairBit b b = 1 / 2 := by simp [fairBit]
  rw [hs, ht, hbb]
  constructor
  · norm_num
  · rw [← Real.log_inv]; norm_num

/-- [proved-derived] **A place is never pruned by its own news**: a symbol that is constant at its place has surprise
zero, so the bound read with the place's symbol as the pin allows it no worth, while the row at that place can carry
the fair bit of `fair_bit_worth`. The bound that holds is on the row's state. -/
theorem constant_symbol_no_news : -Real.log (1 : ℝ) = 0 ∧ (0 : ℝ) < Real.log 2 :=
  ⟨by simp, Real.log_pos (by norm_num)⟩

end Worth

/-! ## 6. Two receipts of one source -/

/-- [proved-standard] **The cross relation**: two receipts `r₁ = K₁ s` and `r₂ = K₂ s` of one source through
commuting kernels satisfy `K₂ r₁ = K₁ r₂`, an identity in which the source does not appear. The pair of receipts
constrains the two paths with the source absent. -/
theorem cross_relation {M S : Type*} [Monoid M] [MulAction M S] (K₁ K₂ : M) (hK : Commute K₁ K₂)
    (s : S) : K₂ • (K₁ • s) = K₁ • (K₂ • s) := by
  rw [← mul_smul, ← mul_smul, hK.eq]

/-! ## 7. More receivers, a finer kernel -/

section Family

variable {X R : Type*} {V : R → Type*}

/-- [definition] **The kernel of a receiver family**: two states are merged when no receiver of the family tells them
apart. -/
def familyKer (read : ∀ r, X → V r) (ℛ : Set R) : Setoid X where
  r x y := ∀ r ∈ ℛ, read r x = read r y
  iseqv :=
    ⟨fun _ _ _ => rfl, fun h r hr => (h r hr).symm, fun h₁ h₂ r hr => (h₁ r hr).trans (h₂ r hr)⟩

/-- [proved-derived] **A larger family has a finer kernel**: `ℛ₁ ⊆ ℛ₂` gives `ker ℛ₂ ≤ ker ℛ₁`. -/
theorem familyKer_antitone (read : ∀ r, X → V r) {ℛ₁ ℛ₂ : Set R} (h : ℛ₁ ⊆ ℛ₂) :
    familyKer read ℛ₂ ≤ familyKer read ℛ₁ := fun _ _ hxy r hr => hxy r (h hr)

/-- [definition] The map between retained quotients that forgets the added receivers. -/
def familyQuotientMap (read : ∀ r, X → V r) {ℛ₁ ℛ₂ : Set R} (h : ℛ₁ ⊆ ℛ₂) :
    Quotient (familyKer read ℛ₂) → Quotient (familyKer read ℛ₁) :=
  Quotient.map' id (fun _ _ hxy => familyKer_antitone read h hxy)

/-- [proved-derived] **The retained quotient under the larger family maps onto the one under the smaller**: a new
medium adds receivers, and retention gains only what the old receivers could not tell apart. -/
theorem familyQuotient_surjective (read : ∀ r, X → V r) {ℛ₁ ℛ₂ : Set R} (h : ℛ₁ ⊆ ℛ₂) :
    Function.Surjective (familyQuotientMap read h) := by
  intro q
  induction q using Quotient.inductionOn' with
  | h x => exact ⟨Quotient.mk'' x, rfl⟩

/-- [proved-derived] Each receiver of the family reads the retained quotient: the quotient is sufficient for the
family that defines it. -/
theorem family_reads_quotient (read : ∀ r, X → V r) (ℛ : Set R) {r : R} (hr : r ∈ ℛ) :
    ∃ f : Quotient (familyKer read ℛ) → V r, ∀ x, f (Quotient.mk'' x) = read r x :=
  ⟨Quotient.lift (s := familyKer read ℛ) (read r) (fun _ _ hxy => hxy r hr), fun _ => rfl⟩

end Family

end Holonics.Foundation.SharedModes

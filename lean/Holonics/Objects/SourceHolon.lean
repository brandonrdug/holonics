import Holonics.Transport.SourceMoment
import Holonics.Foundation.Standing
import Holonics.Foundation.CausalChord
import Holonics.Foundation.FractalPacking
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# The source Holon: phase-carried moments with ring clocks, offsets, standing, chord and address

[definition] Objects 3 and 6 of `docs/ELEMENTARY_OBJECTS.md`, continuing
`Transport/SourceMoment`. A source passage enters a fixed machine of generator rings as
phase-carried moments `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E_g(u_k)`; its oriented pair moments are
`C_gh(δ) = Σ_k v_g(k) ⊗ v_h(k+δ)`, `v_g(k) = Ĝ_g(τ_g(k)) E_g(u_k)`. The owner proved the
single-clock closed form, the tape-free position adjoint, the `δ = 1` separator and the
receiver-history descent. This module adds the remaining laws of the machine contract.

[proved-derived; formal-checked] What is proved.

1. **Per-ring clocks.** A `ClockedRing` advances by `U_g^(c_g(u))` per letter, so its clock time
   is `τ_g = Σ c_g`. Its moment has the closed form `Σ_k U_g^(τ_g(n) − τ_g(k+1)) I_g E_g(u_k)`
   (`ClockedRing.moment_closed_form`); the unit clock is the owner's moment
   (`moment_unit_clock`); a machine of rings advances ring by ring, each on its own clock
   (`jointMoment_append_one`). Witness: the same quarter-turn read under two clocks returns
   `(0,1)` and `(1,0)` on one source (`clock_changes_the_moment`).
2. **The `Ĝ⁻¹` form.** For an invertible advance, `m = U^(n−1) Σ_k U^(−k) I E(u_k)`
   (`moment_eq_receivingPhase_sourceFrame`): increments are carried back to the source phase and
   summed (`sourceFrame_append_one` — no earlier value is advanced), and the receiving phase
   `U^(n−1)` is applied once at read time.
3. **The moment is the minimal standing of the append action.** The future after a word is affine
   in the moment, `m(l ++ w) = U^|w| m(l) + m(w)` (`moment_append`); the moment is a
   `Standing.StandingLaw` whose receivers are all linear readings after every further word,
   reopened by the induced generator `U_u(m) = U m + I E u` (`momentStanding`); over a field two
   sources have identical futures for all linear readings exactly when their moments agree
   (`moment_eq_iff_futureAgreement`; minimal for that family only). For the native receiver — a
   fixed projection `P` read after the word — futures agree iff `P U^k (m − m') = 0` for every `k`
   (`native_futureAgreement_iff`): the moment is minimal exactly when `(U, P)` is observable, as for
   the quarter turn read by `fst` (`observable_native_minimal`), and not for the identity advance
   (`unobservable_native_not_minimal`). No letter list is retained.
4. **Offset moments at every offset.** `offsetMomentAt δ` is `C(δ)` with phased values
   `v(k) = U^k I E(u_k)`. For every `δ ≥ 1`, the sources `a 0^(δ−1) b` and `b 0^(δ−1) a` have
   equal moments under the identity advance and equal `C(δ')` for every `δ' ≠ δ`, and `C(δ)`
   separates them (`offset_separates_exactly_at_its_offset`): each offset is a distinct separator.
5. **The z-transform is a causal-chord transfer.** `(X − U) Σ_(k<N) X^(N−1−k) U^k = X^N − U^N`
   (`charmatrix_mul_truncatedResolvent`), hence for a `CausalChord.Linearization` `(U, I, C)`,
   `X^N · num = den · Σ_(k<N) X^(N−1−k) (C U^k I) + C adj(X − U) U^N I`
   (`numerator_expansion`): the transfer `C (zI − U)⁻¹ I` expands in the Markov parameters
   `C U^k I`, which are the moments of an impulse source `e 0^k` read by `C` (`impulse_moment`).
6. **The address.** For the contracting affine reader `x ↦ x/3`, `left ↦ 0`, `right ↦ 2/3`, the
   moment of a restriction word is the lower end of its `FractalPacking` cell:
   `descend w root = [m(w), m(w) + 3^(−|w|)]` (`descend_eq_moment`). Contrapositively, no
   identity-advance machine realizes the address (`no_identity_advance_realizes_the_address`),
   because it would merge `[left, right]` and `[right, left]`, which
   `restriction_word_cannot_collapse_to_a_multiset` separates.

[open] Offsets between distinct rings with distinct clocks (`C_gh(δ)` for `g ≠ h` in clock time
rather than letter index), the adjoint of the offset moments, and the equality of the RatFunc
transfer with the formal Laurent series of the impulse moments are not stated here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Objects.SourceHolon

open Holonics
open Holonics.Foundation.Chronology
open Holonics.Transport.SourceMoment
open Holonics.Foundation.Standing
open Holonics.Foundation.CausalRelevance.NonLinear
open scoped TensorProduct

/-! ## 1. Per-ring clocks -/

section Clocks

variable {R : Type*} [CommRing R]
variable {X S Letter : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]

/-- [definition] A ring with its own clock: its advance `U_g`, injection `I_g`, encoder `E_g` and
the number of ticks `c_g(u)` a letter advances it. -/
structure ClockedRing (R X S Letter : Type*) [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup S] [Module R S] where
  advance : S →ₗ[R] S
  inject : X →ₗ[R] S
  encode : Letter → X
  clock : Letter → ℕ

namespace ClockedRing

variable (M : ClockedRing R X S Letter)

/-- [definition] The ring's moment, by its one-step law `m⁺ = U^(c(u)) m + I E(u)`. -/
def moment (l : List Letter) : S :=
  l.foldl (fun s u => (M.advance ^ M.clock u) s + M.inject (M.encode u)) 0

/-- [definition] The ring-clock time elapsed after position `k`: `τ(n) − τ(k+1)`. -/
def after (l : List Letter) (k : ℕ) : ℕ := ((l.drop (k + 1)).map M.clock).sum

/-- [definition] The one-step law of the clocked ring. -/
theorem moment_append_one (l : List Letter) (u : Letter) :
    M.moment (l ++ [u]) = (M.advance ^ M.clock u) (M.moment l) + M.inject (M.encode u) := by
  simp [moment, List.foldl_append]

/-- [proved-derived; formal-checked] **Closed form with a ring clock:**
`m_g = Σ_k U_g^(τ_g(n) − τ_g(k+1)) I_g E_g(u_k)`. -/
theorem moment_closed_form (l : List Letter) :
    M.moment l = ∑ k ∈ Finset.range l.length,
      (M.advance ^ M.after l k) ((l.map fun u => M.inject (M.encode u)).getD k 0) := by
  induction l using List.reverseRecOn with
  | nil => simp [moment]
  | append_singleton l u ih =>
      rw [moment_append_one, ih, map_sum, List.length_append, List.length_singleton,
        Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < l.length := Finset.mem_range.mp hk
        have hafter : M.after (l ++ [u]) k = M.clock u + M.after l k := by
          simp only [after, List.drop_append_of_le_length (Nat.succ_le_of_lt hk'),
            List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
          ring
        have hget : ((l ++ [u]).map fun u => M.inject (M.encode u)).getD k 0 =
            (l.map fun u => M.inject (M.encode u)).getD k 0 := by
          rw [List.map_append, List.getD_append _ _ _ _ (by simpa using hk')]
        rw [hafter, hget, pow_add, Module.End.mul_apply]
      · simp [after]

/-- [proved-derived; formal-checked] With the unit clock the ring moment is the owner's moment:
`MomentMachine.moment` is the one-tick special case. -/
theorem moment_unit_clock (h : ∀ u, M.clock u = 1) (l : List Letter) :
    M.moment l = (⟨M.advance, M.inject, M.encode⟩ : MomentMachine R X S Letter).moment l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l u ih =>
      rw [moment_append_one, MomentMachine.moment_append_one, ih, h u, pow_one]

end ClockedRing

/-- [definition] **A machine of rings, each with its own clock.** The joint moment is the family of
ring moments; its state has one component per ring, whatever the source length. -/
def jointMoment {G : Type*} {S' : G → Type*} [∀ g, AddCommGroup (S' g)] [∀ g, Module R (S' g)]
    (rings : ∀ g, ClockedRing R X (S' g) Letter) (l : List Letter) : ∀ g, S' g :=
  fun g => (rings g).moment l

/-- [proved-derived; formal-checked] The joint moment advances ring by ring, each by its own
clock: `m_g⁺ = U_g^(c_g(u)) m_g + I_g E_g(u)`. -/
theorem jointMoment_append_one {G : Type*} {S' : G → Type*} [∀ g, AddCommGroup (S' g)]
    [∀ g, Module R (S' g)] (rings : ∀ g, ClockedRing R X (S' g) Letter) (l : List Letter)
    (u : Letter) (g : G) :
    jointMoment rings (l ++ [u]) g =
      ((rings g).advance ^ (rings g).clock u) (jointMoment rings l g) +
        (rings g).inject ((rings g).encode u) :=
  (rings g).moment_append_one l u

end Clocks

/-- [definition] The quarter-turn ring read on every letter. -/
def everyTick : ClockedRing ℚ (ℚ × ℚ) (ℚ × ℚ) Bool where
  advance := MomentMachine.quarterTurn
  inject := LinearMap.id
  encode b := if b then (1, 0) else (0, 0)
  clock _ := 1

/-- [definition] The same ring whose clock ticks only on `true`. -/
def trueTick : ClockedRing ℚ (ℚ × ℚ) (ℚ × ℚ) Bool where
  advance := MomentMachine.quarterTurn
  inject := LinearMap.id
  encode b := if b then (1, 0) else (0, 0)
  clock b := if b then 1 else 0

/-- [proved-derived; formal-checked] **Witness: the ring clock is part of the phase.** The same
advance and encoder read `[true, false]` as `(0, 1)` under the every-letter clock and as `(1, 0)`
under the clock that does not tick on `false`. -/
theorem clock_changes_the_moment :
    everyTick.moment [true, false] = (0, 1) ∧ trueTick.moment [true, false] = (1, 0) := by
  constructor <;> simp [ClockedRing.moment, everyTick, trueTick, MomentMachine.quarterTurn]

/-! ## 2. The `Ĝ⁻¹` form: accumulation in the source frame, reading at the receiving phase -/

section Inverse

variable {R : Type*} [CommRing R]
variable {X S Letter : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]
variable (M : MomentMachine R X S Letter)

/-- [definition] The source-frame moment `m̃ = Σ_k U^(−k) I E(u_k)` of an invertible advance: each
increment carried back to the source phase by `Ĝ(τ(k))⁻¹`. -/
def sourceFrame (U : (Module.End R S)ˣ) (l : List Letter) : S :=
  ∑ k ∈ Finset.range l.length,
    ((U ^ (-(k : ℤ)) : (Module.End R S)ˣ) : Module.End R S) (M.inject ((l.map M.encode).getD k 0))

/-- [proved-derived; formal-checked] **In the source frame the accumulation is a plain sum**: a new
letter adds its increment carried back by `U^(−n)`; no earlier value is advanced. -/
theorem sourceFrame_append_one (U : (Module.End R S)ˣ) (l : List Letter) (u : Letter) :
    sourceFrame M U (l ++ [u]) = sourceFrame M U l +
      ((U ^ (-(l.length : ℤ)) : (Module.End R S)ˣ) : Module.End R S) (M.inject (M.encode u)) := by
  unfold sourceFrame
  rw [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k < l.length := Finset.mem_range.mp hk
    rw [List.map_append, List.getD_append _ _ _ _ (by simpa using hk')]
  · simp [List.getD_eq_getElem?_getD]

/-- [proved-derived; formal-checked] **The `Ĝ⁻¹` form.** For an invertible advance `U` and a
nonempty source of length `n`, `m = U^(n−1) Σ_k U^(−k) I E(u_k)`: the moment is the source-frame
sum read at the receiving phase `U^(n−1)`. -/
theorem moment_eq_receivingPhase_sourceFrame (U : (Module.End R S)ˣ)
    (hU : M.advance = (U : Module.End R S)) (l : List Letter) :
    M.moment l =
      ((U ^ ((l.length : ℤ) - 1) : (Module.End R S)ˣ) : Module.End R S) (sourceFrame M U l) := by
  rw [M.moment_closed_form, sourceFrame, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < l.length := Finset.mem_range.mp hk
  rw [← Module.End.mul_apply, ← Units.val_mul, ← zpow_add,
    show (l.length : ℤ) - 1 + -(k : ℤ) = ((l.length - 1 - k : ℕ) : ℤ) by omega, zpow_natCast,
    Units.val_pow_eq_pow_val, ← hU]

end Inverse

/-! ## 3. The moment is the minimal standing of the append action -/

section Standing

variable {R : Type*} [CommRing R]
variable {X S Letter : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]
variable (M : MomentMachine R X S Letter)

/-- [proved-derived; formal-checked] **The future after a word is affine in the moment**:
`m(l ++ w) = U^|w| m(l) + m(w)`. -/
theorem moment_append (l w : List Letter) :
    M.moment (l ++ w) = (M.advance ^ w.length) (M.moment l) + M.moment w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w u ih =>
      rw [← List.append_assoc, M.moment_append_one, ih, M.moment_append_one, map_add,
        List.length_append, List.length_singleton, pow_succ', Module.End.mul_apply]
      abel

/-- [proved-derived; formal-checked] **The moment is a `StandingLaw` for the append action.**
Receivers are the linear readings of the moment; the future reading after a word is reopened from
the moment alone by the induced quotient generator `U_u(m) = U m + I E u` — the per-step law,
not a record of the letters. -/
def momentStanding : StandingLaw Letter (Module.Dual R S) (List Letter) S R where
  transport := appendLetter
  observe g l := g (M.moment l)
  retain := M.moment
  reopen g word m := g (transportWord M.momentStep word m)
  sufficient g word l := by
    rw [generatorEquivarianceExtendsToEveryTransportWord appendLetter M.momentStep M.moment
      (fun u l => M.moment_append_one l u) word l]

omit [AddCommGroup X] [Module R X] in
/-- [proved-derived; formal-checked] Over a field, for the receiver family of *all* linear readings
of the moment after every word, futures agree exactly when moments agree. This is minimality for
that family only: the family was chosen to read the moment, so the statement is close to
definitional. Minimality for the native receiver family — a fixed projection read after the word —
holds exactly under observability (`native_futureAgreement_iff`, `observable_native_minimal`,
`unobservable_native_not_minimal`). -/
theorem moment_eq_iff_futureAgreement {K : Type*} [Field K] {X' S' : Type*} [AddCommGroup X']
    [Module K X'] [AddCommGroup S'] [Module K S'] (M : MomentMachine K X' S' Letter)
    (l l' : List Letter) :
    M.moment l = M.moment l' ↔
      futureAgreement (momentStanding M).observe (momentStanding M).transport l l' := by
  constructor
  · intro h; exact (momentStanding M).futureAgreement_of_retain_eq h
  · intro h
    have h0 : ∀ g : Module.Dual K S', g (M.moment l - M.moment l') = 0 := by
      intro g
      have := h g []
      simp only [transportWord_nil, momentStanding] at this
      rw [map_sub, this, sub_self]
    exact sub_eq_zero.mp ((Module.forall_dual_apply_eq_zero_iff K _).mp h0)

/-! ### The native receiver: a fixed projection after the word -/

omit [Module R X] in
theorem transportWord_appendLetter (word l : List Letter) :
    transportWord appendLetter word l = l ++ word.reverse := by
  induction word with
  | nil => simp
  | cons u word ih => simp [ih, appendLetter]

/-- [proved-derived; formal-checked] **Future agreement for the native receiver.** Reading a fixed
linear projection `P` of the moment after every further word, two sources agree exactly when
`P U^k (m − m')` vanishes for every `k`: the minimal standing is the moment modulo the
observability kernel of `(U, P)`. -/
theorem native_futureAgreement_iff [Nonempty Letter] {Y : Type*} [AddCommGroup Y] [Module R Y]
    (P : S →ₗ[R] Y) (l l' : List Letter) :
    futureAgreement (fun (_ : Unit) l => P (M.moment l)) appendLetter l l' ↔
      ∀ k : ℕ, P ((M.advance ^ k) (M.moment l - M.moment l')) = 0 := by
  constructor
  · intro h k
    obtain ⟨a⟩ := (inferInstance : Nonempty Letter)
    have := h () (List.replicate k a)
    simp only [transportWord_appendLetter, List.reverse_replicate, moment_append,
      List.length_replicate] at this
    rw [map_sub, map_sub, sub_eq_zero]
    have h2 := congrArg (fun y => y - P (M.moment (List.replicate k a))) this
    simpa [map_add] using h2
  · intro h _ word
    simp only [transportWord_appendLetter, moment_append, map_add, List.length_reverse]
    have := h word.length
    rw [map_sub, map_sub, sub_eq_zero] at this
    rw [this]

end Standing

/-- [proved-derived; formal-checked] **Observable: the moment is minimal.** The quarter-turn rotor
read by the first coordinate: futures agree exactly when moments agree. -/
theorem observable_native_minimal (l l' : List Bool) :
    futureAgreement (fun (_ : Unit) l => (LinearMap.fst ℚ ℚ ℚ) (MomentMachine.rotor.moment l))
      appendLetter l l' ↔ MomentMachine.rotor.moment l = MomentMachine.rotor.moment l' := by
  rw [native_futureAgreement_iff]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    rw [← sub_eq_zero]
    generalize MomentMachine.rotor.moment l - MomentMachine.rotor.moment l' = d at h0 h1
    simp [MomentMachine.rotor, MomentMachine.quarterTurn] at h0 h1
    ext
    · simpa using h0
    · simpa using h1
  · intro h k; rw [h, sub_self, map_zero, map_zero]

/-- [definition] The identity-advance reader whose `true` letter moves only the unread coordinate. -/
def hiddenReader : MomentMachine ℚ (ℚ × ℚ) (ℚ × ℚ) Bool where
  advance := 1
  inject := LinearMap.id
  encode b := if b then (0, 1) else (0, 0)

/-- [counterexample; formal-checked] **Unobservable: the moment is not minimal.** `[true]` and
`[]` have different moments but agree for the first-coordinate reader after every word. -/
theorem unobservable_native_not_minimal :
    hiddenReader.moment [true] ≠ hiddenReader.moment [] ∧
      futureAgreement (fun (_ : Unit) l => (LinearMap.fst ℚ ℚ ℚ) (hiddenReader.moment l))
        appendLetter [true] [] := by
  have h1 : hiddenReader.moment [true] = (0, 1) := by
    have := hiddenReader.moment_append_one [] true
    simpa [hiddenReader] using this
  refine ⟨by rw [h1]; simp, (native_futureAgreement_iff _ _ _ _).mpr fun k => ?_⟩
  rw [h1]
  simp [hiddenReader]

/-! ## 4. Oriented offset moments at every offset -/

section Offsets

variable {R : Type*} [CommRing R]
variable {X S Letter : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]
variable (M : MomentMachine R X S Letter)

/-- [definition] The phased value `v(k) = Ĝ(τ(k)) E(u_k) = U^k I E(u_k)`. -/
def phased (l : List Letter) (k : ℕ) : S := (M.advance ^ k) (M.inject ((l.map M.encode).getD k 0))

/-- [definition] **The oriented offset moment** `C(δ) = Σ_k v(k) ⊗ v(k+δ)` over the pairs of the
source at separation `δ`. -/
def offsetMomentAt (δ : ℕ) (l : List Letter) : S ⊗[R] S :=
  ∑ k ∈ Finset.range (l.length - δ), phased M l k ⊗ₜ[R] phased M l (k + δ)

end Offsets

/-- [definition] The identity-advance reader on `ℚ²`. -/
def plainReader : MomentMachine ℚ (ℚ × ℚ) (ℚ × ℚ) (ℚ × ℚ) where
  advance := LinearMap.id
  inject := LinearMap.id
  encode := id

/-- [definition] `a = (1,0)`, `b = (0,1)`. -/
def ea : ℚ × ℚ := (1, 0)
def eb : ℚ × ℚ := (0, 1)

/-- [definition] The source `a, 0^(δ−1), b`. -/
def srcA (δ : ℕ) : List (ℚ × ℚ) := ea :: (List.replicate (δ - 1) 0 ++ [eb])

/-- [definition] The source `b, 0^(δ−1), a`. -/
def srcB (δ : ℕ) : List (ℚ × ℚ) := eb :: (List.replicate (δ - 1) 0 ++ [ea])

/-- [definition] The values of `x, 0^(δ−1), y` by position. -/
def seq (x y : ℚ × ℚ) (δ k : ℕ) : ℚ × ℚ := if k = 0 then x else if k = δ then y else 0

theorem getD_src (x y : ℚ × ℚ) {δ : ℕ} (hδ : 1 ≤ δ) (k : ℕ) :
    (x :: (List.replicate (δ - 1) 0 ++ [y])).getD k 0 = seq x y δ k := by
  rcases k with _ | k
  · simp [seq]
  · simp only [List.getD_cons_succ, seq, Nat.succ_ne_zero, if_false]
    by_cases hk : k < δ - 1
    · rw [List.getD_append _ _ _ _ (by simpa using hk)]
      have : k + 1 ≠ δ := by omega
      simp [this, List.getD_eq_getElem?_getD, hk]
    · rw [List.getD_append_right _ _ _ _ (by simpa using hk)]
      simp only [List.length_replicate]
      by_cases hkδ : k + 1 = δ
      · have : k - (δ - 1) = 0 := by omega
        simp [hkδ, this]
      · have : k - (δ - 1) ≠ 0 := by omega
        rw [if_neg hkδ]
        simp [List.getD_eq_getElem?_getD, this]

theorem phased_src (x y : ℚ × ℚ) {δ : ℕ} (hδ : 1 ≤ δ) (k : ℕ) :
    phased plainReader (x :: (List.replicate (δ - 1) 0 ++ [y])) k = seq x y δ k := by
  simp only [phased, plainReader]
  rw [List.map_id, getD_src x y hδ k]
  rw [show (LinearMap.id : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ)) = 1 from rfl, one_pow]
  rfl

theorem length_src (x y : ℚ × ℚ) {δ : ℕ} (hδ : 1 ≤ δ) :
    (x :: (List.replicate (δ - 1) 0 ++ [y])).length = δ + 1 := by
  simp; omega

/-- [definition] The bilinear reading `x ⊗ y ↦ x₁ y₂`, which sees orientation. -/
def crossReading : (ℚ × ℚ) ⊗[ℚ] (ℚ × ℚ) →ₗ[ℚ] ℚ :=
  TensorProduct.lift (LinearMap.mk₂ ℚ (fun x y : ℚ × ℚ => x.1 * y.2)
    (fun _ _ _ => by simp [add_mul]) (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp; ring))

theorem ea_tmul_eb_ne : ea ⊗ₜ[ℚ] eb ≠ eb ⊗ₜ[ℚ] ea := by
  intro h
  have := congrArg crossReading h
  simp [crossReading, ea, eb] at this

theorem offset_src (x y : ℚ × ℚ) {δ δ' : ℕ} (hδ : 1 ≤ δ) :
    offsetMomentAt plainReader δ' (x :: (List.replicate (δ - 1) 0 ++ [y])) =
      ∑ k ∈ Finset.range (δ + 1 - δ'), seq x y δ k ⊗ₜ[ℚ] seq x y δ (k + δ') := by
  simp only [offsetMomentAt, length_src x y hδ, phased_src x y hδ]

/-- [proved-derived; formal-checked] **Every offset is needed.** For every `δ ≥ 1`, the sources
`a 0^(δ−1) b` and `b 0^(δ−1) a` have equal moments under the identity advance and equal oriented
offset moments at every offset `δ' ≠ δ`, and the offset moment `C(δ)` alone separates them. -/
theorem offset_separates_exactly_at_its_offset {δ : ℕ} (hδ : 1 ≤ δ) :
    plainReader.moment (srcA δ) = plainReader.moment (srcB δ) ∧
      offsetMomentAt plainReader δ (srcA δ) ≠ offsetMomentAt plainReader δ (srcB δ) ∧
      ∀ δ', δ' ≠ δ →
        offsetMomentAt plainReader δ' (srcA δ) = offsetMomentAt plainReader δ' (srcB δ) := by
  refine ⟨?_, ?_, ?_⟩
  · apply plainReader.identity_advance_merges_permutations rfl
    have h1 : List.Perm (srcA δ) (eb :: ea :: List.replicate (δ - 1) 0) := by
      rw [srcA, ← List.cons_append]; exact List.perm_append_singleton _ _
    have h2 : List.Perm (srcB δ) (eb :: ea :: List.replicate (δ - 1) 0) :=
      List.Perm.cons _ (List.perm_append_singleton _ _)
    exact h1.trans h2.symm
  · rw [srcA, srcB, offset_src _ _ hδ, offset_src _ _ hδ, Nat.add_sub_cancel_left,
      Finset.sum_range_one, Finset.sum_range_one]
    have h0 : δ ≠ 0 := by omega
    simp only [seq, if_true, zero_add, if_neg h0]
    exact ea_tmul_eb_ne
  · intro δ' hne
    rw [srcA, srcB, offset_src _ _ hδ, offset_src _ _ hδ]
    rcases Nat.eq_zero_or_pos δ' with h0 | hpos
    · subst h0
      have hδ0 : (0 : ℕ) ≠ δ := by omega
      simp only [Nat.sub_zero, add_zero]
      rw [Finset.sum_eq_add 0 δ hδ0 (fun c _ hc => by simp [seq, hc.1, hc.2])
          (fun h => by simp at h) (fun h => by simp at h),
        Finset.sum_eq_add 0 δ hδ0 (fun c _ hc => by simp [seq, hc.1, hc.2])
          (fun h => by simp at h) (fun h => by simp at h)]
      simp only [seq, if_true, if_neg hδ0.symm]
      exact add_comm _ _
    · have hzero : ∀ x y : ℚ × ℚ, ∀ k ∈ Finset.range (δ + 1 - δ'),
          seq x y δ k ⊗ₜ[ℚ] seq x y δ (k + δ') = 0 := by
        intro x y k hk
        have hk' : k < δ + 1 - δ' := Finset.mem_range.mp hk
        by_cases hk0 : k = 0
        · subst hk0
          have h1 : δ' ≠ 0 := by omega
          simp [seq, h1, hne]
        · have hkδ : k ≠ δ := by omega
          simp [seq, hk0, hkδ]
      rw [Finset.sum_eq_zero (hzero _ _), Finset.sum_eq_zero (hzero _ _)]

/-! ## 5. The z-transform of the moment is a causal-chord transfer -/

section Chord

open Matrix Polynomial Foundation.CausalChord

variable {K : Type*} [Field K] {n m p : ℕ}

/-- [proved-derived; formal-checked] **The truncated resolvent.**
`(X − U) · Σ_(k<N) X^(N−1−k) U^k = X^N − U^N` over `K[X]`: the finite form of
`(zI − U)⁻¹ = Σ_k U^k z^(−k−1)`. -/
theorem charmatrix_mul_truncatedResolvent (U : Matrix (Fin n) (Fin n) K) (N : ℕ) :
    charmatrix U * ∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) • (U ^ k).map C =
      (X ^ N : K[X]) • (1 : Matrix (Fin n) (Fin n) K[X]) - (U ^ N).map C := by
  have hchar : charmatrix U = (X : K[X]) • (1 : Matrix (Fin n) (Fin n) K[X]) - U.map C := by
    rw [charmatrix, Matrix.scalar_apply, ← smul_one_eq_diagonal]
    rfl
  induction N with
  | zero => simp
  | succ N ih =>
      have hsplit : ∑ k ∈ Finset.range (N + 1), (X ^ (N + 1 - 1 - k) : K[X]) • (U ^ k).map C =
          (X : K[X]) • ∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) • (U ^ k).map C +
            (U ^ N).map C := by
        rw [Finset.sum_range_succ, Finset.smul_sum]
        congr 1
        · refine Finset.sum_congr rfl fun k hk => ?_
          have hk' : k < N := Finset.mem_range.mp hk
          rw [smul_smul, ← pow_succ']
          congr 2
          omega
        · simp
      rw [hsplit, Matrix.mul_add, Matrix.mul_smul, ih, hchar, Matrix.sub_mul, Matrix.smul_mul,
        Matrix.one_mul, ← Matrix.map_mul, ← pow_succ']
      rw [smul_sub, smul_smul, ← pow_succ']
      abel

/-- [proved-derived; formal-checked] **The transfer expands in the impulse moments.** For a
`CausalChord.Linearization` `(U, I, C)` and every horizon `N`,
`X^N · num = den · Σ_(k<N) X^(N−1−k) (C U^k I) + C adj(X − U) U^N I`: dividing by `den · X^N`,
`C (zI − U)⁻¹ I = Σ_(k<N) (C U^k I) z^(−k−1) + O(z^(−N−1))`. The coefficients `C U^k I` are the
moments of an impulse (`impulse_moment`). -/
theorem numerator_expansion (L : Linearization K n m p) (N : ℕ) :
    (X ^ N : K[X]) • L.numerator =
      L.denominator • (∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) •
          (L.readout * L.state ^ k * L.excitation).map C) +
        L.readout.map C * (charmatrix L.state).adjugate * (L.state ^ N * L.excitation).map C := by
  have hres := charmatrix_mul_truncatedResolvent L.state N
  have hadj : (charmatrix L.state).adjugate * charmatrix L.state = L.denominator • 1 := by
    rw [Matrix.adjugate_mul, Linearization.denominator, Matrix.charpoly]
  have key : (X ^ N : K[X]) • (charmatrix L.state).adjugate =
      L.denominator • ∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) • (L.state ^ k).map C +
        (charmatrix L.state).adjugate * (L.state ^ N).map C := by
    have h2 : (charmatrix L.state).adjugate * (charmatrix L.state *
        ∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) • (L.state ^ k).map C) =
        (charmatrix L.state).adjugate * ((X ^ N : K[X]) • 1 - (L.state ^ N).map C) := by
      rw [hres]
    rw [← Matrix.mul_assoc, hadj, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_one] at h2
    rw [h2]; abel
  have hnum : (X ^ N : K[X]) • L.numerator =
      L.readout.map C * ((X ^ N : K[X]) • (charmatrix L.state).adjugate) * L.excitation.map C := by
    rw [Linearization.numerator, Matrix.mul_smul, Matrix.smul_mul]
  have hsum : L.readout.map C *
      (∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) • (L.state ^ k).map C) *
        L.excitation.map C =
      ∑ k ∈ Finset.range N, (X ^ (N - 1 - k) : K[X]) •
        (L.readout * L.state ^ k * L.excitation).map C := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.map_mul, Matrix.map_mul]
  have htail : L.readout.map C * ((charmatrix L.state).adjugate * (L.state ^ N).map C) *
      L.excitation.map C =
      L.readout.map C * (charmatrix L.state).adjugate * (L.state ^ N * L.excitation).map C := by
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hnum, key, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, hsum, htail]

/-- [definition] The matrix reader of a linearization's state and excitation: advance `U`,
injection `I`, identity encoder on excitation values. -/
def matrixReader (U : Matrix (Fin n) (Fin n) K) (I : Matrix (Fin n) (Fin m) K) :
    MomentMachine K (Fin m → K) (Fin n → K) (Fin m → K) where
  advance := Matrix.mulVecLin U
  inject := Matrix.mulVecLin I
  encode := id

theorem mulVecLin_pow_apply (U : Matrix (Fin n) (Fin n) K) (k : ℕ) (v : Fin n → K) :
    (Matrix.mulVecLin U ^ k) v = (U ^ k) *ᵥ v := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', ← Matrix.mulVec_mulVec]
      rfl

theorem moment_replicate_zero (M : MomentMachine K (Fin m → K) (Fin n → K) (Fin m → K))
    (hE : M.encode = id) (k : ℕ) : M.moment (List.replicate k 0) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ', M.moment_append_one, ih, hE]
      simp

/-- [proved-derived; formal-checked] **The impulse moment.** The source `e, 0^k` has moment
`U^k I e`; read by `C` it is the Markov parameter `(C U^k I) e`, the `k`-th coefficient of the
transfer expansion. -/
theorem impulse_moment (U : Matrix (Fin n) (Fin n) K) (I : Matrix (Fin n) (Fin m) K)
    (C' : Matrix (Fin p) (Fin n) K) (e : Fin m → K) (k : ℕ) :
    (matrixReader U I).moment (e :: List.replicate k 0) = (U ^ k * I) *ᵥ e ∧
      C' *ᵥ (matrixReader U I).moment (e :: List.replicate k 0) = (C' * U ^ k * I) *ᵥ e := by
  have h1 : (matrixReader U I).moment [e] = I *ᵥ e := by
    have := (matrixReader U I).moment_append_one [] e
    simpa [matrixReader] using this
  have hm : (matrixReader U I).moment (e :: List.replicate k 0) = (U ^ k * I) *ᵥ e := by
    have := (matrixReader U I).moment_append_one
    rw [show e :: List.replicate k 0 = [e] ++ List.replicate k 0 from rfl, moment_append, h1,
      moment_replicate_zero _ rfl, add_zero, List.length_replicate]
    change (Matrix.mulVecLin U ^ k) (I *ᵥ e) = _
    rw [mulVecLin_pow_apply, Matrix.mulVec_mulVec]
  refine ⟨hm, ?_⟩
  rw [hm, Matrix.mulVec_mulVec, Matrix.mul_assoc]

end Chord

/-! ## 6. The moment of a contracting affine advance is a fractal address -/

section Address

open Foundation.FractalPacking

/-- [definition] The Cantor reader: advance `x ↦ x/3`, encoder `left ↦ 0`, `right ↦ 2/3`. -/
def cantorReader : MomentMachine ℚ ℚ ℚ Hand where
  advance := (1 / 3 : ℚ) • LinearMap.id
  inject := LinearMap.id
  encode h := match h with
    | .left => 0
    | .right => 2 / 3

theorem cantor_advance_pow (k : ℕ) (x : ℚ) : (cantorReader.advance ^ k) x = (1 / 3 : ℚ) ^ k * x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      simp [cantorReader]
      ring

theorem moment_cons {R X S Letter : Type*} [CommRing R] [AddCommGroup X] [Module R X]
    [AddCommGroup S] [Module R S] (M : MomentMachine R X S Letter) (u : Letter) (w : List Letter) :
    M.moment (u :: w) = (M.advance ^ w.length) (M.inject (M.encode u)) + M.moment w := by
  have h1 : M.moment [u] = M.inject (M.encode u) := by
    have := M.moment_append_one [] u
    simpa using this
  rw [show u :: w = [u] ++ w from rfl, moment_append, h1]

/-- [proved-derived; formal-checked] **The moment is the address.** For every restriction word,
`descend w root = [m(w), m(w) + 3^(−|w|)]`: the Cantor reader's moment of the word, read in list
order, is the lower end of the addressed cell. The first source letter is the finest scale. -/
theorem descend_eq_moment (w : List Hand) :
    descend w root = ⟨cantorReader.moment w, cantorReader.moment w + (1 / 3 : ℚ) ^ w.length⟩ := by
  induction w with
  | nil => simp [descend, root]
  | cons h w ih =>
      rw [descend, ih, moment_cons, cantor_advance_pow, List.length_cons]
      cases h
      · simp only [child, leftChild, Cell.width, cantorReader]
        congr 1
        · simp
        · simp; ring
      · simp only [child, rightChild, Cell.width, cantorReader]
        congr 1
        · simp; ring
        · simp; ring

/-- [proved-derived; formal-checked] **No identity-advance moment realizes the address.** An
identity advance merges every permutation (`identity_advance_merges_permutations`); a reader
factoring the address through such a moment would give `descend [left, right] root =
descend [right, left] root`, contradicting `restriction_word_cannot_collapse_to_a_multiset`. -/
theorem no_identity_advance_realizes_the_address {R X S : Type*} [CommRing R] [AddCommGroup X]
    [Module R X] [AddCommGroup S] [Module R S] :
    ¬ ∃ (M : MomentMachine R X S Hand) (read : S → Cell),
      M.advance = 1 ∧ ∀ w, read (M.moment w) = descend w root := by
  rintro ⟨M, read, h1, hread⟩
  apply restriction_word_cannot_collapse_to_a_multiset
  rw [← hread, ← hread, M.identity_advance_merges_permutations h1 (List.Perm.swap _ _ [])]

/-- [proved-derived; formal-checked] The Cantor reader's advance is not the identity, and it
separates the two orders exactly as the address does. -/
theorem cantor_separates_the_orders :
    cantorReader.moment [.left, .right] ≠ cantorReader.moment [.right, .left] := by
  intro h
  exact restriction_word_cannot_collapse_to_a_multiset (by
    rw [descend_eq_moment, descend_eq_moment, h]; rfl)

end Address

section Audit
#print axioms ClockedRing.moment_closed_form
#print axioms ClockedRing.moment_unit_clock
#print axioms jointMoment_append_one
#print axioms clock_changes_the_moment
#print axioms sourceFrame_append_one
#print axioms moment_eq_receivingPhase_sourceFrame
#print axioms moment_append
#print axioms momentStanding
#print axioms moment_eq_iff_futureAgreement
#print axioms native_futureAgreement_iff
#print axioms observable_native_minimal
#print axioms unobservable_native_not_minimal
#print axioms offset_separates_exactly_at_its_offset
#print axioms charmatrix_mul_truncatedResolvent
#print axioms numerator_expansion
#print axioms impulse_moment
#print axioms descend_eq_moment
#print axioms no_identity_advance_realizes_the_address
#print axioms cantor_separates_the_orders
end Audit

end Holonics.Objects.SourceHolon

import Holonics.Objects.SourceHolon
import Holonics.Objects.SourcePorts
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators

/-!
# HNN.Moment: selective stepping on closing rings, the phase-binned moment and its capacity

[definition] Rebuild step 4, campaign 1, law 3 (`docs/plans/THE_REBUILD.md`, "Step 4 design",
table (b) row 3). A source passage enters the HNN as **phase-binned counts** on closing rotor rings.
The rings are indexed by `ℕ` in the declared carry order `0 → 1 → …`; ring `g` has period `d_g`,
a lock `N_g` of residues and the exterior port chart `port_g(x) = code(x) mod d_g`, which is known
before any key is located. On each source cell `x` ring `g` advances

```text
c_g(x) = [port_g(x) ∈ N_g]      plus the carry of its predecessor:   carryIn_(g+1) = ⌊τ'_g / d_g⌋ − ⌊τ_g / d_g⌋
```

the odometer carry of ring `g`'s wraps (`SelectiveDecl.carryIn`; it equals the wrap indicator when
every period is at least `2`, `carryIn_le_one`). On a closing ring (`P^d = 1`) the source moment
`m̃ = Σ_k P^(−τ_k) I E x_k` is carried by the counts `M c a = #{k | τ_k ≡ c, u_k = a}`.

[proved-derived; formal-checked] What is proved.

1. **Selective position (R3 K1).** Ring `g`'s step count over any cell list depends only on the
   cells, the declared locks and the phase classes of the rings before `g`
   (`selective_position`): never on ring `g`'s own key, on later rings, or on earlier rings'
   windings. So the rotor position is `key_g + steps_g(k)`. Every carry is at most one when every
   period is at least two (`carryIn_le_one`), so a ring moves at most two ticks per cell
   (`advance_le_two`). Witnesses: an Enigma notch law that reads the ring's own position makes the
   steps depend on its key (`notch_steps_depend_on_own_key`), and ring `1`'s steps depend on ring
   `0`'s phase class (`earlier_phase_class_is_load_bearing`).
2. **Phase binning is exact on a closing ring (§8.5).** For `P^d = 1`,
   `Σ_k P^(−τ_k) I x_k = Σ_(c<d) P^(−c) I h_c` with `h_c = Σ_(τ_k ≡ c) x_k`
   (`closingRing_moment_is_phaseBinned`). Witness: for the non-closing doubling advance the bins do
   not carry the moment (`nonclosing_binning_fails`).
3. **The moment is the contraction of the counts with the encoder.** For every linear `E`,
   `m̃(E) = Σ_c Σ_a M c a • P^(−c) I (E e_a)` (`encoderMoment_contract`); the encoder covector is
   the same linear map for every `g`, and two streams with equal counts, of any order or length,
   have equal encoder covectors (`encoder_covector_tape_free`). The offset counts
   `C δ c a b` are computed without any encoder and every pair port reads the offset contribution
   through them (`exteriorOffset_independent_of_E`). At the open, the receiving-phase reading
   `P^T m̃` is the `Objects/SourceHolon.ClockedRing` moment of the cells with their increments as
   clocks (`open_eq_clockedRing_moment`, composing `ClockedRing.moment_closed_form`).
4. **Descent.** The fixed-size stream state (lift point, phase-binned counts on the source rings,
   offset counts, the window of the last `max Δ` cells) is a
   `Foundation/ReceiverHistoryCompression` for the append action (`selectiveClock_stream_descent`),
   and the source moment of a source ring is read off its counts alone
   (`binsMoment_stream`).
5. **Capacity (R2 H1, R3 H1).** After `n` cells the persisting source state takes at most
   `N(n) = |A|^(max Δ) · ∏_g (2n + d_g) · ∏_(g∈𝒮) [C(n + d_g|A| − 1, d_g|A| − 1) ·
   ∏_(δ∈Δ) C(n − δ + d_g|A|² − 1, d_g|A|² − 1)]` values; where `N(n) < |A|^n` the source → state
   map on `A^n` is not injective (`moment_capacity`), and once that holds at a crossover `n*` past
   `max Δ` it holds at every later `n`, because `N` is log-concave there
   (`capacityBound_logConcave`, `capacity_persists`).
6. **The directed-contrast law** moved from the retired `Transport/GeneratorSourceEpisode`
   (review B5, F6): kinds and multiplicity are kept (`pooledContrast_zero_of_absent_kind`,
   `repeated_contact_doubles_its_contrast`), and the pullback is the genuine incidence adjoint of
   the pooled contrast (`pooledContrast_pairing_adjoint`).

[open] The moment quotient `V_m` against the admitted receivers (campaign 3), offsets between
distinct rings in clock time, and the moment's exact dense code as a reading are not stated here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Moment

open Holonics
open Holonics.Foundation.Chronology
open Holonics.Foundation.LineageCompression
open Holonics.Transport.SourceMoment
open Holonics.Objects.SourceHolon

/-! ## 1. The selective stepping machine -/

/-- [definition] **A declaration of closing rotor rings in carry order.** Ring `g` has period
`period g`, lock `lock g` (a set of residues of its port chart) and reads the cell's exterior code
through the port chart `code x mod period g`. -/
structure SelectiveDecl (Cell : Type*) where
  period : ℕ → ℕ
  lock : ℕ → Finset ℕ
  code : Cell → ℕ

namespace SelectiveDecl

variable {Cell : Type*} (D : SelectiveDecl Cell)

/-- [definition] The port chart `port_g(x) = code(x) mod d_g`: an exterior residue face, known
before any key is located. -/
def port (g : ℕ) (x : Cell) : ℕ := D.code x % D.period g

/-- [definition] The cell fits ring `g`'s lock. -/
def Fits (g : ℕ) (x : Cell) : Prop := D.port g x ∈ D.lock g

instance (g : ℕ) (x : Cell) : Decidable (D.Fits g x) := by unfold Fits; infer_instance

/-- [definition] The selective step `c_g(x) = [port_g(x) ∈ N_g]`. -/
def step (g : ℕ) (x : Cell) : ℕ := if D.Fits g x then 1 else 0

/-- [definition] **The carry into ring `g`**: the number of wraps of ring `g − 1` on this cell, the
odometer carry `⌊τ'/d⌋ − ⌊τ/d⌋` of the predecessor. Ring `0` receives none. -/
def carryIn (x : Cell) (τ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | g + 1 => (τ g + D.step g x + carryIn x τ g) / D.period g - τ g / D.period g

/-- [definition] **One source cell advances every ring**: `τ_g ← τ_g + c_g(x) + carry_g`. -/
def advance (x : Cell) (τ : ℕ → ℕ) : ℕ → ℕ := fun g => τ g + D.step g x + D.carryIn x τ g

/-- [definition] The lift point after a list of cells, from the initial configuration `τ`. -/
def run (cells : List Cell) (τ : ℕ → ℕ) : ℕ → ℕ :=
  cells.foldl (fun τ x => D.advance x τ) τ

@[simp] theorem run_nil (τ : ℕ → ℕ) : D.run [] τ = τ := rfl

@[simp] theorem run_cons (x : Cell) (cells : List Cell) (τ : ℕ → ℕ) :
    D.run (x :: cells) τ = D.run cells (D.advance x τ) := rfl

theorem run_append_one (cells : List Cell) (x : Cell) (τ : ℕ → ℕ) :
    D.run (cells ++ [x]) τ = D.advance x (D.run cells τ) := by
  simp [run, List.foldl_append]

theorem step_le_one (g : ℕ) (x : Cell) : D.step g x ≤ 1 := by
  unfold step; split_ifs <;> omega

/-- The wraps of a ring advanced by `i` from `t` depend only on its phase class:
`(t + i)/d − t/d = (t % d + i)/d`. -/
theorem wraps_eq_phase (t i d : ℕ) : (t + i) / d - t / d = (t % d + i) / d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have h : t + i = t % d + i + d * (t / d) := by
      have := Nat.mod_add_div t d; omega
    rw [h, Nat.add_mul_div_left _ _ hd, Nat.add_sub_cancel]

theorem carryIn_succ_eq_phase (x : Cell) (τ : ℕ → ℕ) (g : ℕ) :
    D.carryIn x τ (g + 1) = (τ g % D.period g + (D.step g x + D.carryIn x τ g)) / D.period g := by
  rw [carryIn, ← wraps_eq_phase, add_assoc]

/-- [proved-derived; formal-checked] **The carry reads only phase classes.** Two lift points with
equal phase classes on every ring before `g` send the same carry into ring `g`. -/
theorem carryIn_congr (x : Cell) {τ σ : ℕ → ℕ} :
    ∀ g, (∀ h < g, τ h % D.period h = σ h % D.period h) →
      D.carryIn x τ g = D.carryIn x σ g
  | 0, _ => rfl
  | g + 1, hphase => by
      rw [carryIn_succ_eq_phase, carryIn_succ_eq_phase, hphase g (Nat.lt_succ_self g),
        carryIn_congr x g fun h hh => hphase h (Nat.lt_succ_of_lt hh)]

/-- [proved-derived; formal-checked] **Every carry is at most one** when every period is at least
two: the carry is then the wrap indicator of the predecessor. -/
theorem carryIn_le_one (hd : ∀ g, 2 ≤ D.period g) (x : Cell) (τ : ℕ → ℕ) :
    ∀ g, D.carryIn x τ g ≤ 1
  | 0 => by simp [carryIn]
  | g + 1 => by
      rw [carryIn_succ_eq_phase]
      have hc := carryIn_le_one hd x τ g
      have hs := D.step_le_one g x
      have hdg := hd g
      have hm := Nat.mod_lt (τ g) (by omega : 0 < D.period g)
      rw [Nat.div_le_iff_le_mul_add_pred (by omega)]
      omega

/-- [proved-derived; formal-checked] A ring moves at most two ticks per cell. -/
theorem advance_le_two (hd : ∀ g, 2 ≤ D.period g) (x : Cell) (τ : ℕ → ℕ) (g : ℕ) :
    τ g ≤ D.advance x τ g ∧ D.advance x τ g ≤ τ g + 2 := by
  have := D.carryIn_le_one hd x τ g
  have := D.step_le_one g x
  unfold advance; omega

theorem le_advance (x : Cell) (τ : ℕ → ℕ) (g : ℕ) : τ g ≤ D.advance x τ g := by
  unfold advance; omega

theorem le_run (cells : List Cell) (τ : ℕ → ℕ) (g : ℕ) : τ g ≤ D.run cells τ g := by
  induction cells generalizing τ with
  | nil => exact le_rfl
  | cons x cells ih => exact (D.le_advance x τ g).trans (ih _)

/-- [proved-derived; formal-checked] Over `n` cells a ring moves at most `2n` ticks (every period
at least two). -/
theorem run_le (hd : ∀ g, 2 ≤ D.period g) (cells : List Cell) (τ : ℕ → ℕ) (g : ℕ) :
    D.run cells τ g ≤ τ g + 2 * cells.length := by
  induction cells generalizing τ with
  | nil => simp
  | cons x cells ih =>
      have h1 := ih (D.advance x τ)
      have h2 := (D.advance_le_two hd x τ g).2
      simp only [run_cons, List.length_cons]
      omega

/-- The per-cell advance keeps equal phase classes on every ring before `g`, and moves ring `g` by
the same number of ticks. -/
theorem advance_congr (x : Cell) {τ σ : ℕ → ℕ} (g : ℕ)
    (hphase : ∀ h < g, τ h % D.period h = σ h % D.period h) :
    (∀ h < g, D.advance x τ h % D.period h = D.advance x σ h % D.period h) ∧
      D.advance x τ g - τ g = D.advance x σ g - σ g := by
  refine ⟨fun h hh => ?_, ?_⟩
  · have hc := D.carryIn_congr x h fun h' hh' => hphase h' (hh'.trans hh)
    simp only [advance, hc]
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_mod (τ h), Nat.add_mod (σ h), hphase h hh]
  · have hc := D.carryIn_congr x g hphase
    simp only [advance, hc]
    omega

/-- [proved-derived; formal-checked] **Selective position (R3 K1).** If two initial configurations
have equal phase classes on every ring before `g`, then for every list of cells ring `g` takes the
same number of steps. Ring `g`'s steps never depend on its own key, on later rings, or on the
windings of earlier rings; its rotor position after the cells is `key_g + steps_g`. -/
theorem selective_position (cells : List Cell) {τ σ : ℕ → ℕ} (g : ℕ)
    (hphase : ∀ h < g, τ h % D.period h = σ h % D.period h) :
    D.run cells τ g - τ g = D.run cells σ g - σ g := by
  induction cells generalizing τ σ with
  | nil => simp
  | cons x cells ih =>
      obtain ⟨hphase', hstep⟩ := D.advance_congr x g hphase
      have hrec := ih hphase'
      have h1 := D.le_run cells (D.advance x τ) g
      have h2 := D.le_run cells (D.advance x σ) g
      have h3 := D.le_advance x τ g
      have h4 := D.le_advance x σ g
      simp only [run_cons]
      omega

/-- [proved-derived; formal-checked] The rotor position is the key plus steps independent of it:
`τ_g(k) = key_g + steps_g(k)`, the same steps for every key of ring `g`. -/
theorem position_eq_key_add_steps (cells : List Cell) (τ : ℕ → ℕ) (g key : ℕ) :
    D.run cells (Function.update τ g key) g =
      key + (D.run cells τ g - τ g) := by
  have h := D.selective_position cells (τ := Function.update τ g key) (σ := τ) g
    (fun h hh => by rw [Function.update_of_ne (Nat.ne_of_lt hh)])
  have hle := D.le_run cells (Function.update τ g key) g
  simp only [Function.update_self] at h hle
  omega

/-- [proved-derived; formal-checked] **A ring with an empty lock steps only by carry**
(campaign 1's ring `3`): its carry-out, the aeon boundary, comes once per turn of the chain. -/
theorem emptyLock_steps_only_by_carry (x : Cell) (τ : ℕ → ℕ) (g : ℕ) (hg : D.lock g = ∅) :
    D.advance x τ g = τ g + D.carryIn x τ g := by
  simp [advance, step, Fits, hg]

end SelectiveDecl

/-! ### Witnesses for the load-bearing hypotheses -/

/-- [definition] The Enigma notch law on one ring: step when the ring's own **position** sits in
the lock. It is not the HNN law; it is the witness that the lock must read the input's port class. -/
def notchAdvance (d : ℕ) (lock : Finset ℕ) (τ : ℕ) : ℕ := if τ % d ∈ lock then τ + 1 else τ

/-- [counterexample; formal-checked] **A notch law reads the key.** With period `5` and lock `{0}`,
one cell steps the ring from key `0` and not from key `1`: the step count depends on the ring's own
key, so its key could not be located from the cells alone. -/
theorem notch_steps_depend_on_own_key :
    notchAdvance 5 {0} 0 - 0 ≠ notchAdvance 5 {0} 1 - 1 := by decide

/-- [definition] A two-ring declaration: ring `0` of period `2` whose lock every cell fits, ring `1`
of period `5` whose lock no cell fits. -/
def twoRing : SelectiveDecl Unit where
  period g := if g = 0 then 2 else 5
  lock g := if g = 0 then {0, 1} else ∅
  code _ := 0

/-- [counterexample; formal-checked] **The earlier phase class is load-bearing.** Ring `1`'s step on
one cell depends on ring `0`'s phase class: from ring `0` at phase `1` it wraps and carries into
ring `1`; from phase `0` it does not. -/
theorem earlier_phase_class_is_load_bearing :
    twoRing.run [()] (fun _ => 1) 1 - 1 ≠ twoRing.run [()] (fun _ => 0) 1 - 0 := by
  simp [SelectiveDecl.run, SelectiveDecl.advance, SelectiveDecl.carryIn, SelectiveDecl.step,
    SelectiveDecl.Fits, SelectiveDecl.port, twoRing]

/-! ## 2. The phase-binned moment on a closing ring -/

section Binning

variable {R : Type*} [CommRing R]
variable {X S : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]

/-- [definition] The source-frame phase transport `P^(−c)` of the ring's navigator, as an
endomorphism. -/
def back (P : (Module.End R S)ˣ) (c : ℕ) : Module.End R S :=
  ((P ^ (-(c : ℤ)) : (Module.End R S)ˣ) : Module.End R S)

/-- [definition] **The source moment** `m̃ = Σ_(k<n) P^(−τ_k) I x_k` of encoded cells `x_k`, each
carried back from the ring position `τ_k` it met (`Objects/SourceHolon.sourceFrame` with a ring
clock in place of the letter index). -/
def sourceMoment (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (x : ℕ → X) (τ : ℕ → ℕ) (n : ℕ) : S :=
  ∑ k ∈ Finset.range n, back P (τ k) (I (x k))

/-- [definition] The phase bin `h_c = Σ_(k<n, τ_k ≡ c mod d) x_k`. -/
def phaseBin (x : ℕ → X) (τ : ℕ → ℕ) (d n c : ℕ) : X :=
  ∑ k ∈ (Finset.range n).filter (fun k => τ k % d = c), x k

/-- [definition] The binned moment `Σ_(c<d) P^(−c) I h_c`. -/
def binnedMoment (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (x : ℕ → X) (τ : ℕ → ℕ)
    (d n : ℕ) : S :=
  ∑ c ∈ Finset.range d, back P c (I (phaseBin x τ d n c))

/-- [proved-derived; formal-checked] On a closing ring (`P^d = 1`) the phase transport reads only
the phase class: `P^(−t) = P^(−(t mod d))`. -/
theorem back_mod {P : (Module.End R S)ˣ} {d : ℕ} (hP : P ^ d = 1) (t : ℕ) :
    back P t = back P (t % d) := by
  unfold back
  congr 1
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, ← Nat.mod_add_div t d, pow_add, pow_mul,
    hP, one_pow, mul_one, Nat.mod_add_div]

/-- [proved-derived; formal-checked] **Phase binning is exact on a closing ring (§8.5).** For
`P^d = 1`, `Σ_k P^(−τ_k) I x_k = Σ_(c<d) P^(−c) I h_c`: the moment is carried by the `d` phase
bins, whatever the clocks. -/
theorem closingRing_moment_is_phaseBinned {P : (Module.End R S)ˣ} {d : ℕ} (hd : 0 < d)
    (hP : P ^ d = 1) (I : X →ₗ[R] S) (x : ℕ → X) (τ : ℕ → ℕ) (n : ℕ) :
    sourceMoment P I x τ n = binnedMoment P I x τ d n := by
  unfold sourceMoment binnedMoment phaseBin
  simp only [map_sum]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.range n) (t := Finset.range d)
    (g := fun k => τ k % d) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd))]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun k hk => ?_
  rw [back_mod hP (τ k), (Finset.mem_filter.mp hk).2]

/-! ### The count contraction -/

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- [definition] The counts of a letter stream `w` over the contributing cells `s`: how many cells
met phase class `c` with letter `l`. No encoder enters. -/
def counts {L : Type*} [DecidableEq L] (w : ℕ → L) (τ : ℕ → ℕ) (d : ℕ) (s : Finset ℕ)
    (c : ℕ) (l : L) : ℕ :=
  ((s.filter fun k => τ k % d = c).filter fun k => w k = l).card

/-- [proved-derived; formal-checked] **The count contraction.** For one-hot cells read through any
linear chart `F`, the phase-carried sum over the contributing cells is the contraction of the
counts with `F`. -/
theorem sum_eq_counts_contract {L : Type*} [Fintype L] [DecidableEq L]
    {P : (Module.End R S)ˣ} {d : ℕ} (hd : 0 < d) (hP : P ^ d = 1) (I : X →ₗ[R] S)
    (F : (L → R) →ₗ[R] X) (w : ℕ → L) (τ : ℕ → ℕ) (s : Finset ℕ) :
    ∑ k ∈ s, back P (τ k) (I (F (Pi.single (w k) 1))) =
      ∑ c ∈ Finset.range d, ∑ l, (counts w τ d s c l : R) • back P c (I (F (Pi.single l 1))) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := Finset.range d)
    (g := fun k => τ k % d) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hd))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_fiberwise (s := s.filter fun k => τ k % d = c) (g := w)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [counts, Finset.cast_card, Finset.sum_smul, one_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_filter, Finset.mem_filter] at hk
  rw [back_mod hP (τ k), hk.1.2, hk.2]

/-- [definition] **The encoder moment** of letters `u_k ∈ A` read as one-hot cells of the exterior
chart through a linear encoder `E`. -/
def encoderMoment (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (E : (A → R) →ₗ[R] X) (u : ℕ → A)
    (τ : ℕ → ℕ) (n : ℕ) : S :=
  sourceMoment P I (fun k => E (Pi.single (u k) 1)) τ n

/-- [proved-derived; formal-checked] **The moment is the contraction of the counts with the
encoder.** For every linear encoder `E`,
`m̃(E) = Σ_(c<d) Σ_a M c a • P^(−c) I (E e_a)` with `M c a = #{k < n | τ_k ≡ c, u_k = a}`. -/
theorem encoderMoment_contract {P : (Module.End R S)ˣ} {d : ℕ} (hd : 0 < d) (hP : P ^ d = 1)
    (I : X →ₗ[R] S) (E : (A → R) →ₗ[R] X) (u : ℕ → A) (τ : ℕ → ℕ) (n : ℕ) :
    encoderMoment P I E u τ n =
      ∑ c ∈ Finset.range d, ∑ a,
        (counts u τ d (Finset.range n) c a : R) • back P c (I (E (Pi.single a 1))) :=
  sum_eq_counts_contract hd hP I E u τ (Finset.range n)

omit [Fintype A] in
theorem encoderMoment_add (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (E δE : (A → R) →ₗ[R] X)
    (u : ℕ → A) (τ : ℕ → ℕ) (n : ℕ) :
    encoderMoment P I (E + δE) u τ n = encoderMoment P I E u τ n + encoderMoment P I δE u τ n := by
  simp only [encoderMoment, sourceMoment, LinearMap.add_apply, map_add, Finset.sum_add_distrib]

/-- [proved-derived; formal-checked] **The encoder covector needs no record of the cells.** For
every covector `g` on the ring: the exact response of `g ∘ m̃` to an encoder change `δE` is
`g (m̃(δE))`; it is the transpose contraction `Σ_c Σ_a M c a · (I* P^(−c)* g)(δE e_a)` of the
counts; and two streams with equal counts, of any order or length, have equal encoder covectors. -/
theorem encoder_covector_tape_free {P : (Module.End R S)ˣ} {d : ℕ} (hd : 0 < d) (hP : P ^ d = 1)
    (I : X →ₗ[R] S) (g : Module.Dual R S) (u u' : ℕ → A) (τ τ' : ℕ → ℕ) (n n' : ℕ)
    (hcounts : ∀ c < d, ∀ a, counts u τ d (Finset.range n) c a =
      counts u' τ' d (Finset.range n') c a) :
    (∀ E δE : (A → R) →ₗ[R] X,
      g (encoderMoment P I (E + δE) u τ n) - g (encoderMoment P I E u τ n) =
        g (encoderMoment P I δE u τ n)) ∧
    (∀ δE : (A → R) →ₗ[R] X, g (encoderMoment P I δE u τ n) =
      ∑ c ∈ Finset.range d, ∑ a, (counts u τ d (Finset.range n) c a : R) *
        (I.dualMap ((back P c).dualMap g)) (δE (Pi.single a 1))) ∧
    (∀ δE : (A → R) →ₗ[R] X,
      g (encoderMoment P I δE u τ n) = g (encoderMoment P I δE u' τ' n')) := by
  refine ⟨fun E δE => by rw [encoderMoment_add, map_add, add_sub_cancel_left], fun δE => ?_,
    fun δE => ?_⟩
  · rw [encoderMoment_contract hd hP, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  · rw [encoderMoment_contract hd hP, encoderMoment_contract hd hP]
    congr 1
    refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun a _ => ?_
    rw [hcounts c (Finset.mem_range.mp hc) a]

/-! ### Offset counts on the exterior pair chart -/

/-- [definition] The offset counts `C δ c a b = #{k < n | δ ≤ k, τ_k ≡ c, u_k = a, u_(k−δ) = b}`,
computed from the cells and clocks alone. -/
def offsetCounts (u : ℕ → A) (τ : ℕ → ℕ) (d n δ c : ℕ) (a b : A) : ℕ :=
  counts (fun k => (u k, u (k - δ))) τ d ((Finset.range n).filter (δ ≤ ·)) c (a, b)

/-- [definition] The offset contribution through a pair port `F` on the exterior pair chart
`A × A → R`: `Σ_(δ ≤ k < n) P^(−τ_k) I F(x_k ⊗ x_(k−δ))`. -/
def offsetContribution (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (F : (A × A → R) →ₗ[R] X)
    (u : ℕ → A) (τ : ℕ → ℕ) (n δ : ℕ) : S :=
  ∑ k ∈ (Finset.range n).filter (δ ≤ ·), back P (τ k) (I (F (Pi.single (u k, u (k - δ)) 1)))

/-- [proved-derived; formal-checked] **The offset counts are independent of every encoder.** For
every linear pair port `F`, the offset contribution is the contraction of the offset counts with
`F`; so two streams with equal offset counts give equal contributions for every `F`, and the
counts stay valid however `E` and `E^(δ)` change. -/
theorem exteriorOffset_independent_of_E {P : (Module.End R S)ˣ} {d : ℕ} (hd : 0 < d)
    (hP : P ^ d = 1) (I : X →ₗ[R] S) (u : ℕ → A) (τ : ℕ → ℕ) (n δ : ℕ) :
    (∀ F : (A × A → R) →ₗ[R] X, offsetContribution P I F u τ n δ =
      ∑ c ∈ Finset.range d, ∑ a, ∑ b,
        (offsetCounts u τ d n δ c a b : R) • back P c (I (F (Pi.single (a, b) 1)))) ∧
    ∀ (u' : ℕ → A) (τ' : ℕ → ℕ) (n' : ℕ),
      (∀ c < d, ∀ a b, offsetCounts u τ d n δ c a b = offsetCounts u' τ' d n' δ c a b) →
        ∀ F : (A × A → R) →ₗ[R] X,
          offsetContribution P I F u τ n δ = offsetContribution P I F u' τ' n' δ := by
  have key : ∀ (u : ℕ → A) (τ : ℕ → ℕ) (n : ℕ) (F : (A × A → R) →ₗ[R] X),
      offsetContribution P I F u τ n δ =
        ∑ c ∈ Finset.range d, ∑ a, ∑ b,
          (offsetCounts u τ d n δ c a b : R) • back P c (I (F (Pi.single (a, b) 1))) := by
    intro u τ n F
    rw [offsetContribution, sum_eq_counts_contract hd hP I F (fun k => (u k, u (k - δ))) τ]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  refine ⟨key u τ n, fun u' τ' n' hcounts F => ?_⟩
  rw [key u τ n F, key u' τ' n' F]
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [hcounts c (Finset.mem_range.mp hc) a b]

end Binning

/-- [definition] The doubling advance on `ℚ`: a non-closing ring. -/
def doubling : (Module.End ℚ ℚ)ˣ where
  val := (2 : ℚ) • LinearMap.id
  inv := (1 / 2 : ℚ) • LinearMap.id
  val_inv := by ext; simp
  inv_val := by ext; simp

/-- [counterexample; formal-checked] **Binning needs a closing ring.** For the doubling advance
(`P^1 ≠ 1`) read with one bin, two cells at positions `0, 1` carry the moment `1 + 1/2`, while their
bin carries `2`: the hypothesis `P^d = 1` of `closingRing_moment_is_phaseBinned` is load-bearing. -/
theorem nonclosing_binning_fails :
    sourceMoment doubling LinearMap.id (fun _ => (1 : ℚ)) id 2 ≠
      binnedMoment doubling LinearMap.id (fun _ => (1 : ℚ)) id 1 2 := by
  simp [sourceMoment, binnedMoment, phaseBin, back, Finset.sum_range_succ, doubling, Nat.mod_one]
  norm_num

/-! ### The open reads the ring-clock moment -/

section Open

variable {R : Type*} [CommRing R]
variable {X S : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]

/-- [definition] The ring position after cell `k` of a list of cells with their tick increments:
the partial sum of increments through `k`. -/
def positionAfter {Letter : Type*} (l : List (Letter × ℕ)) (k : ℕ) : ℕ :=
  ((l.take (k + 1)).map Prod.snd).sum

/-- [proved-derived; formal-checked] **The open reads the ring-clock moment.** Carrying the source
moment from the source frame to the ring's current position `T` (the word's open,
`s_g(0) = P^(τ_g) m̃_g`) gives exactly the `Objects/SourceHolon.ClockedRing` moment of the cells,
each advancing the ring by its own increment (composing `ClockedRing.moment_closed_form`). -/
theorem open_eq_clockedRing_moment {Letter : Type*} (P : (Module.End R S)ˣ) (I : X →ₗ[R] S)
    (E : Letter → X) (l : List (Letter × ℕ)) :
    ((P : Module.End R S) ^ (l.map Prod.snd).sum)
        (sourceMoment P I (fun k => (l.map fun p => E p.1).getD k 0) (positionAfter l) l.length) =
      (⟨P, I, fun p => E p.1, Prod.snd⟩ : ClockedRing R X S (Letter × ℕ)).moment l := by
  rw [ClockedRing.moment_closed_form, sourceMoment, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < l.length := Finset.mem_range.mp hk
  have hsplit : positionAfter l k +
      (⟨P, I, fun p => E p.1, Prod.snd⟩ : ClockedRing R X S (Letter × ℕ)).after l k =
        (l.map Prod.snd).sum := by
    simp only [positionAfter, ClockedRing.after]
    rw [← List.sum_append, ← List.map_append, List.take_append_drop]
  have hget : (l.map fun u => I (E u.1)).getD k 0 = I ((l.map fun p => E p.1).getD k 0) := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk']
  simp only
  rw [hget, back, ← Module.End.mul_apply, ← Units.val_pow_eq_pow_val, ← Units.val_mul,
    ← zpow_natCast, ← zpow_add, ← hsplit]
  congr 2
  rw [show ((positionAfter l k + (⟨P, I, fun p => E p.1, Prod.snd⟩ :
      ClockedRing R X S (Letter × ℕ)).after l k : ℕ) : ℤ) + -(positionAfter l k : ℤ) =
      (((⟨P, I, fun p => E p.1, Prod.snd⟩ : ClockedRing R X S (Letter × ℕ)).after l k : ℕ) : ℤ)
    by push_cast; ring, zpow_natCast, Units.val_pow_eq_pow_val]

end Open

/-! ### Log-concave counts stay below once they fall below -/

/-- [definition] `f` is log-concave from `n₀`: `f(n+2) f(n) ≤ f(n+1)²` for every `n ≥ n₀`. -/
def LogConcaveFrom (n₀ : ℕ) (f : ℕ → ℕ) : Prop := ∀ n, n₀ ≤ n → f (n + 2) * f n ≤ f (n + 1) ^ 2

theorem LogConcaveFrom.mono {n₀ n₁ : ℕ} {f : ℕ → ℕ} (h : n₀ ≤ n₁) (hf : LogConcaveFrom n₀ f) :
    LogConcaveFrom n₁ f := fun n hn => hf n (h.trans hn)

theorem LogConcaveFrom.mul {n₀ : ℕ} {f g : ℕ → ℕ} (hf : LogConcaveFrom n₀ f)
    (hg : LogConcaveFrom n₀ g) : LogConcaveFrom n₀ fun n => f n * g n := fun n hn => by
  calc f (n + 2) * g (n + 2) * (f n * g n) = (f (n + 2) * f n) * (g (n + 2) * g n) := by ring
    _ ≤ f (n + 1) ^ 2 * g (n + 1) ^ 2 := Nat.mul_le_mul (hf n hn) (hg n hn)
    _ = (f (n + 1) * g (n + 1)) ^ 2 := by ring

theorem LogConcaveFrom.prod {ι : Type*} {n₀ : ℕ} (s : Finset ι) (f : ι → ℕ → ℕ)
    (hf : ∀ i ∈ s, LogConcaveFrom n₀ (f i)) : LogConcaveFrom n₀ fun n => ∏ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => intro n _; simp
  | insert i s hi ih =>
      have := (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa [Finset.prod_insert hi] using this

theorem logConcave_const (n₀ c : ℕ) : LogConcaveFrom n₀ fun _ => c := fun _ _ => by
  rw [sq]

theorem logConcave_linear (n₀ a b : ℕ) : LogConcaveFrom n₀ fun n => a * n + b := fun n _ => by
  nlinarith [sq_nonneg a]

/-- [proved-derived; formal-checked] Stars-and-bars counts `C(n + m, m)` are log-concave in `n`:
`C(n+2+m, m) C(n+m, m) ≤ C(n+1+m, m)²`. -/
theorem logConcave_choose (m : ℕ) : LogConcaveFrom 0 fun n => Nat.choose (n + m) m := by
  intro n _
  -- `C(k+1+m, m)·(k+1) = C(k+m, m)·(k+1+m)`
  have step : ∀ k, Nat.choose (k + 1 + m) m * (k + 1) = Nat.choose (k + m) m * (k + 1 + m) := by
    intro k
    have := Nat.choose_mul_succ_eq (k + m) m
    rw [show k + m + 1 = k + 1 + m by ring, show k + 1 + m - m = k + 1 by omega] at this
    linarith
  have h1 := step n
  have h2 := step (n + 1)
  simp only [show n + 1 + 1 = n + 2 by ring] at h2
  have hpos : 0 < Nat.choose (n + 1 + m) m := Nat.choose_pos (by omega)
  have key : Nat.choose (n + 2 + m) m * Nat.choose (n + m) m * ((n + 2) * (n + 1 + m)) ≤
      Nat.choose (n + 1 + m) m ^ 2 * ((n + 2) * (n + 1 + m)) := by
    calc Nat.choose (n + 2 + m) m * Nat.choose (n + m) m * ((n + 2) * (n + 1 + m))
        = (Nat.choose (n + 2 + m) m * (n + 2)) * (Nat.choose (n + m) m * (n + 1 + m)) := by ring
      _ = (Nat.choose (n + 1 + m) m * (n + 1 + 1 + m)) * (Nat.choose (n + 1 + m) m * (n + 1)) := by
          rw [h2, ← h1]
      _ = Nat.choose (n + 1 + m) m ^ 2 * ((n + 2 + m) * (n + 1)) := by ring
      _ ≤ Nat.choose (n + 1 + m) m ^ 2 * ((n + 2) * (n + 1 + m)) :=
          Nat.mul_le_mul_left _ (by nlinarith)
  exact Nat.le_of_mul_le_mul_right key (by positivity)

theorem logConcave_shift {f : ℕ → ℕ} (hf : LogConcaveFrom 0 f) (δ : ℕ) :
    LogConcaveFrom δ fun n => f (n - δ) := fun n hn => by
  have := hf (n - δ) (Nat.zero_le _)
  simpa [show n + 2 - δ = n - δ + 2 by omega, show n + 1 - δ = n - δ + 1 by omega] using this

/-- [proved-derived; formal-checked] **Once below, always below.** A positive sequence log-concave
from `n₀` that falls below `bⁿ` at a first crossing `m > n₀` stays below `bⁿ` at every later `n`. -/
theorem stays_below_of_logConcave {f : ℕ → ℕ} {n₀ b m : ℕ} (hf : LogConcaveFrom n₀ f)
    (hpos : ∀ n, 0 < f n) (hm : n₀ + 1 ≤ m) (hbelow : f m < b ^ m)
    (habove : b ^ (m - 1) ≤ f (m - 1)) : ∀ n, m ≤ n → f n < b ^ n := by
  -- the ratio `f(n+1)/f(n)` stays below `b` from the crossing on
  have hratio : ∀ k, f (m - 1 + k + 1) < b * f (m - 1 + k) := by
    intro k
    induction k with
    | zero =>
        have hb : b ^ m = b * b ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
        simp only [Nat.add_zero, show m - 1 + 1 = m by omega]
        calc f m < b ^ m := hbelow
          _ = b * b ^ (m - 1) := hb
          _ ≤ b * f (m - 1) := Nat.mul_le_mul_left _ habove
    | succ k ih =>
        have hlc := hf (m - 1 + k) (by omega)
        have hp := hpos (m - 1 + k)
        have hp1 := hpos (m - 1 + k + 1)
        rw [show m - 1 + (k + 1) + 1 = m - 1 + k + 2 by ring,
          show m - 1 + (k + 1) = m - 1 + k + 1 by ring]
        have : f (m - 1 + k + 2) * f (m - 1 + k) < b * f (m - 1 + k + 1) * f (m - 1 + k) := by
          calc f (m - 1 + k + 2) * f (m - 1 + k) ≤ f (m - 1 + k + 1) ^ 2 := hlc
            _ = f (m - 1 + k + 1) * f (m - 1 + k + 1) := sq _
            _ < f (m - 1 + k + 1) * (b * f (m - 1 + k)) := Nat.mul_lt_mul_of_pos_left ih hp1
            _ = b * f (m - 1 + k + 1) * f (m - 1 + k) := by ring
        exact Nat.lt_of_mul_lt_mul_right this
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hbelow
  | succ n hmn ih =>
      have h := hratio (n - (m - 1))
      rw [show m - 1 + (n - (m - 1)) = n by omega] at h
      calc f (n + 1) < b * f n := h
        _ ≤ b * b ^ n := Nat.mul_le_mul_left _ ih.le
        _ = b ^ (n + 1) := by rw [pow_succ']

/-- [definition] A count that falls below `2ⁿ` once and rises again: `8ⁿ` except `1` at `n = 2`. -/
def reboundingCount (n : ℕ) : ℕ := if n = 2 then 1 else 8 ^ n

/-- [counterexample; formal-checked] **Log-concavity is load-bearing.** `reboundingCount` crosses
below `2ⁿ` at `n = 2` from `8 ≥ 2` at `n = 1`, yet `512 ≥ 2³` at `n = 3`: without log-concavity a
first crossing does not persist. -/
theorem logConcavity_is_load_bearing :
    2 ^ 1 ≤ reboundingCount 1 ∧ reboundingCount 2 < 2 ^ 2 ∧ ¬ reboundingCount 3 < 2 ^ 3 ∧
      ¬ LogConcaveFrom 0 reboundingCount := by
  refine ⟨by norm_num [reboundingCount], by norm_num [reboundingCount],
    by norm_num [reboundingCount], fun h => ?_⟩
  have := h 1 (Nat.zero_le _)
  norm_num [reboundingCount] at this

/-! ## 3. The stream state and its descent -/

/-- [definition] **A source declaration**: the rings in carry order, the source rings `𝒮` and the
declared offsets `Δ`. The window holds the last `max Δ` cells. -/
structure SourceDecl (A : Type*) extends SelectiveDecl A where
  sources : Finset ℕ
  offsets : Finset ℕ

namespace SourceDecl

variable {A : Type*} (D : SourceDecl A)

/-- [definition] The window length `max Δ`. -/
def windowLength : ℕ := D.offsets.sup id

/-- [definition] **The persisting source state**: the lift point, the phase-binned counts on each
source ring (the multiset of `(phase class, cell)` it met), the offset counts per source ring and
offset (`(phase class, cell, cell δ back)`), and the window of the last `max Δ` cells, most recent
first. Its size does not grow with the passage except through the counts' values. -/
structure StreamState where
  lift : ℕ → ℕ
  bins : (g : ℕ) → Multiset (ZMod (D.period g) × A)
  pairBins : (g : ℕ) → ℕ → Multiset (ZMod (D.period g) × A × A)
  window : List A

variable {D}

/-- [definition] **Ingest one cell**: advance every ring by selective stepping, bin the cell at
each source ring's new phase class, bin the offset pairs the window supplies, and overwrite the
window. The window is a shift register, not an accumulating ring. -/
def ingest (a : A) (s : D.StreamState) : D.StreamState :=
  { lift := D.advance a s.lift
    bins := fun g => if g ∈ D.sources then
        ((D.advance a s.lift g : ZMod (D.period g)), a) ::ₘ s.bins g else s.bins g
    pairBins := fun g δ => if g ∈ D.sources ∧ δ ∈ D.offsets then
        (s.window[δ - 1]?).elim (s.pairBins g δ)
          (fun b => ((D.advance a s.lift g : ZMod (D.period g)), a, b) ::ₘ s.pairBins g δ)
      else s.pairBins g δ
    window := (a :: s.window).take D.windowLength }

variable (D)

/-- [definition] The state at the opening, from the initial configuration `τ⁰`. -/
def initial (τ₀ : ℕ → ℕ) : D.StreamState :=
  { lift := τ₀, bins := fun _ => 0, pairBins := fun _ _ => 0, window := [] }

/-- [definition] The state after a passage. -/
def stream (τ₀ : ℕ → ℕ) (l : List A) : D.StreamState :=
  l.foldl (fun s a => ingest a s) (D.initial τ₀)

variable {D}

theorem stream_append_one (τ₀ : ℕ → ℕ) (l : List A) (a : A) :
    D.stream τ₀ (l ++ [a]) = ingest a (D.stream τ₀ l) := by
  simp [stream, List.foldl_append]

theorem stream_lift (τ₀ : ℕ → ℕ) (l : List A) : (D.stream τ₀ l).lift = D.run l τ₀ := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih => rw [stream_append_one, SelectiveDecl.run_append_one, ← ih]; rfl

/-- A source ring bins each new cell at its new phase class. -/
theorem stream_bins_append_one (τ₀ : ℕ → ℕ) {g : ℕ} (hg : g ∈ D.sources) (l : List A) (a : A) :
    (D.stream τ₀ (l ++ [a])).bins g =
      ((D.advance a (D.run l τ₀) g : ZMod (D.period g)), a) ::ₘ (D.stream τ₀ l).bins g := by
  rw [stream_append_one, ← stream_lift]
  exact if_pos hg

/-- The window is the last `max Δ` cells, most recent first. -/
theorem stream_window (τ₀ : ℕ → ℕ) (l : List A) :
    (D.stream τ₀ l).window = l.reverse.take D.windowLength := by
  induction l using List.reverseRecOn with
  | nil => simp [stream, initial]
  | append_singleton l a ih =>
      rw [stream_append_one]
      change (a :: (D.stream τ₀ l).window).take D.windowLength = _
      rw [ih, List.reverse_append, List.reverse_singleton, List.singleton_append]
      cases D.windowLength with
      | zero => simp
      | succ m => simp [List.take_take]

/-- [proved-derived; formal-checked] **Descent.** The stream state is a receiver-history compression
for the append action: every receiver of the state factors through it, and ingesting a cell is
the induced step (`Foundation/ReceiverHistoryCompression`, as `Transport/SourceMoment.streamDescent`
for the unit clock). No cell list is retained. -/
def selectiveClock_stream_descent {Receiver Face : Type*} (τ₀ : ℕ → ℕ)
    (read : Receiver → D.StreamState → Face) :
    ReceiverHistoryCompression A Receiver (List A) D.StreamState Face where
  present :=
    { quotient := D.stream τ₀
      receiver := fun r l => read r (D.stream τ₀ l)
      factor := read
      exact := fun _ _ => rfl }
  sourceTransport := appendLetter
  quotientTransport := ingest
  generatorExact a l := stream_append_one τ₀ l a

section Reading

variable {R : Type*} [CommRing R]
variable {X S : Type*} [AddCommGroup X] [Module R X] [AddCommGroup S] [Module R S]

/-- [definition] The moment read off a source ring's counts: `Σ_(c,a) P^(−c) I E(a)` over the
multiset of `(phase class, cell)` the ring met. -/
def binsMoment {d : ℕ} (P : (Module.End R S)ˣ) (I : X →ₗ[R] S) (E : A → X)
    (m : Multiset (ZMod d × A)) : S :=
  (m.map fun p => back P p.1.val (I (E p.2))).sum

/-- [proved-derived; formal-checked] **The source moment is read off the counts.** On a closing
source ring (`P^(d_g) = 1`), the phase-binned counts of the stream state carry the ring's source
moment `Σ_k P^(−τ_g(k)) I E(u_k)`, with `τ_g(k)` the position selective stepping gave cell `k`:
the moment is a receiver of the fixed-size state. -/
theorem binsMoment_stream {g : ℕ} (hg : g ∈ D.sources) (P : (Module.End R S)ˣ)
    (hP : P ^ D.period g = 1) (I : X →ₗ[R] S) (E : A → X) (τ₀ : ℕ → ℕ) (l : List A) :
    binsMoment P I E ((D.stream τ₀ l).bins g) =
      sourceMoment P I (fun k => (l.map E).getD k 0) (fun k => D.run (l.take (k + 1)) τ₀ g)
        l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [binsMoment, stream, initial, sourceMoment]
  | append_singleton l a ih =>
      rw [stream_append_one]
      change binsMoment P I E (if g ∈ D.sources then
        ((D.advance a (D.stream τ₀ l).lift g : ZMod (D.period g)), a) ::ₘ (D.stream τ₀ l).bins g
        else (D.stream τ₀ l).bins g) = _
      rw [if_pos hg, binsMoment, Multiset.map_cons, Multiset.sum_cons, ← binsMoment, ih,
        List.length_append, List.length_singleton, sourceMoment, sourceMoment,
        Finset.sum_range_succ, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k < l.length := Finset.mem_range.mp hk
        rw [List.take_append_of_le_length (by omega), List.map_append,
          List.getD_append _ _ _ _ (by simpa using hk')]
      · rw [ZMod.val_natCast, ← back_mod hP, stream_lift, ← SelectiveDecl.run_append_one]
        rw [List.take_of_length_le (by simp)]
        simp [List.getD_eq_getElem?_getD]

end Reading

/-! ## 4. Capacity: where the moment becomes lossy by counting -/

section Capacity

/-- [proved-derived; formal-checked] Each cell adds one count to every source ring. -/
theorem card_bins (τ₀ : ℕ → ℕ) {g : ℕ} (hg : g ∈ D.sources) (l : List A) :
    Multiset.card ((D.stream τ₀ l).bins g) = l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [stream, initial]
  | append_singleton l a ih =>
      rw [stream_append_one]
      change Multiset.card (if g ∈ D.sources then
        ((D.advance a (D.stream τ₀ l).lift g : ZMod (D.period g)), a) ::ₘ (D.stream τ₀ l).bins g
        else (D.stream τ₀ l).bins g) = _
      rw [if_pos hg, Multiset.card_cons, ih, List.length_append, List.length_singleton]

/-- [proved-derived; formal-checked] The offset `δ` bins one pair per cell at least `δ` into the
passage: `n − δ` pairs after `n` cells. -/
theorem card_pairBins (τ₀ : ℕ → ℕ) {g δ : ℕ} (hg : g ∈ D.sources) (hδ : δ ∈ D.offsets)
    (hδpos : 1 ≤ δ) (l : List A) :
    Multiset.card ((D.stream τ₀ l).pairBins g δ) = l.length - δ := by
  have hδW : δ ≤ D.windowLength := Finset.le_sup (f := id) hδ
  induction l using List.reverseRecOn with
  | nil => simp [stream, initial]
  | append_singleton l a ih =>
      rw [stream_append_one]
      change Multiset.card (if g ∈ D.sources ∧ δ ∈ D.offsets then
        ((D.stream τ₀ l).window[δ - 1]?).elim ((D.stream τ₀ l).pairBins g δ)
          (fun b => ((D.advance a (D.stream τ₀ l).lift g : ZMod (D.period g)), a, b) ::ₘ
            (D.stream τ₀ l).pairBins g δ)
        else (D.stream τ₀ l).pairBins g δ) = _
      rw [if_pos ⟨hg, hδ⟩, stream_window, List.length_append, List.length_singleton]
      by_cases hl : δ ≤ l.length
      · have hlt : δ - 1 < (l.reverse.take D.windowLength).length := by
          simp only [List.length_take, List.length_reverse]; omega
        rw [List.getElem?_eq_getElem hlt, Option.elim_some, Multiset.card_cons, ih]
        omega
      · have hnone : (l.reverse.take D.windowLength)[δ - 1]? = none := by
          rw [List.getElem?_eq_none_iff]
          simp only [List.length_take, List.length_reverse]; omega
        rw [hnone, Option.elim_none, ih]
        omega

theorem window_length (τ₀ : ℕ → ℕ) (l : List A) :
    (D.stream τ₀ l).window.length = min l.length D.windowLength := by
  rw [stream_window, List.length_take, List.length_reverse, min_comm]

variable [Fintype A] [DecidableEq A]

variable (D)

/-- [definition] The persisting source state read on the first `G` rings: lift point, the counts
of the source rings, their offset counts and the window. -/
abbrev Persist (G : ℕ) :=
  (Fin G → ℕ) × ((g : D.sources) → Multiset (ZMod (D.period g.1) × A)) ×
    ((p : D.sources × D.offsets) → Multiset (ZMod (D.period p.1.1) × A × A)) × List A

/-- [definition] The persisting part of a stream state. -/
def persist (G : ℕ) (s : D.StreamState) : D.Persist G :=
  (fun g => s.lift g, fun g => s.bins g.1, fun p => s.pairBins p.1.1 p.2.1, s.window)

variable [hne : ∀ g, NeZero (D.period g)]

/-- [definition] **The box of persisting states after `n` cells**: lift points within `2n` ticks of
the opening, counts of total `n` on each source ring (`Sym` of its slots), offset counts of total
`n − δ`, and windows of `min n (max Δ)` cells. -/
def box (τ₀ : ℕ → ℕ) (G n : ℕ) : Finset (D.Persist G) :=
  Fintype.piFinset (fun g : Fin G => Finset.Icc (τ₀ g) (τ₀ g + 2 * n)) ×ˢ
    Fintype.piFinset (fun g : D.sources => (Finset.univ : Finset (Sym (ZMod (D.period g.1) × A) n)).map
      ⟨Sym.toMultiset, Sym.coe_injective⟩) ×ˢ
    Fintype.piFinset (fun p : D.sources × D.offsets =>
      (Finset.univ : Finset (Sym (ZMod (D.period p.1.1) × A × A) (n - p.2.1))).map
        ⟨Sym.toMultiset, Sym.coe_injective⟩) ×ˢ
    (Finset.univ : Finset (List.Vector A (min n D.windowLength))).map
      ⟨List.Vector.toList, List.Vector.toList_injective⟩

/-- [definition] **The design's count** `N(n) = |A|^(max Δ) · ∏_(g<G) (2n + d_g) ·
∏_(g∈𝒮) [C(n + d_g|A| − 1, d_g|A| − 1) · ∏_(δ∈Δ) C(n − δ + d_g|A|² − 1, d_g|A|² − 1)]`, with
`alphabet = |A|`. -/
def capacityBound (G alphabet n : ℕ) : ℕ :=
  alphabet ^ D.windowLength * (∏ g ∈ Finset.range G, (2 * n + D.period g)) *
    ∏ g ∈ D.sources, (Nat.choose (n + D.period g * alphabet - 1) (D.period g * alphabet - 1) *
      ∏ δ ∈ D.offsets,
        Nat.choose (n - δ + D.period g * alphabet ^ 2 - 1) (D.period g * alphabet ^ 2 - 1))

variable {D}

/-- [proved-derived; formal-checked] Every persisting state after `n` cells lies in the box. -/
theorem persist_mem_box (hd : ∀ g, 2 ≤ D.period g) (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ)
    (τ₀ : ℕ → ℕ) (G : ℕ) (l : List A) :
    D.persist G (D.stream τ₀ l) ∈ D.box τ₀ G l.length := by
  refine Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun g => ?_,
    Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun g => ?_,
      Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr fun p => ?_, ?_⟩⟩⟩
  · show (D.stream τ₀ l).lift g ∈ _
    rw [stream_lift, Finset.mem_Icc]
    exact ⟨D.le_run l τ₀ g, D.run_le hd l τ₀ g⟩
  · exact Finset.mem_map.mpr ⟨⟨(D.stream τ₀ l).bins g.1, card_bins τ₀ g.2 l⟩,
      Finset.mem_univ _, rfl⟩
  · exact Finset.mem_map.mpr ⟨⟨(D.stream τ₀ l).pairBins p.1.1 p.2.1,
      card_pairBins τ₀ p.1.2 p.2.2 (hδpos _ p.2.2) l⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_map.mpr ⟨(⟨(D.stream τ₀ l).window, window_length τ₀ l⟩ :
      List.Vector A (min l.length D.windowLength)), Finset.mem_univ _, rfl⟩

omit [DecidableEq A] in
theorem card_slots (g : ℕ) :
    Fintype.card (ZMod (D.period g) × A) = D.period g * Fintype.card A := by
  rw [Fintype.card_prod, ZMod.card]

omit [DecidableEq A] in
theorem card_pairSlots (g : ℕ) :
    Fintype.card (ZMod (D.period g) × A × A) = D.period g * Fintype.card A ^ 2 := by
  rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, sq]

theorem multichoose_eq_choose {S n : ℕ} (hS : 1 ≤ S) :
    Nat.multichoose S n = Nat.choose (n + S - 1) (S - 1) := by
  rw [Nat.multichoose_eq, show S + n - 1 = n + S - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- [proved-derived; formal-checked] **The box has at most `N(n)` states.** -/
theorem card_box_le [Nonempty A] (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (D.box τ₀ G n).card ≤ D.capacityBound G (Fintype.card A) n := by
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos
  have hdpos : ∀ g, 1 ≤ D.period g := fun g => Nat.pos_of_ne_zero (hne g).out
  have hcard : (D.box τ₀ G n).card = (∏ _g : Fin G, (τ₀ _g + 2 * n + 1 - τ₀ _g)) *
      ((∏ g : D.sources, Nat.multichoose (D.period g.1 * Fintype.card A) n) *
        ((∏ p : D.sources × D.offsets,
          Nat.multichoose (D.period p.1.1 * Fintype.card A ^ 2) (n - p.2.1)) *
          Fintype.card A ^ min n D.windowLength)) := by
    rw [box, Finset.card_product, Finset.card_product, Finset.card_product,
      Fintype.card_piFinset, Fintype.card_piFinset, Fintype.card_piFinset, Finset.card_map,
      Finset.card_univ, card_vector]
    simp only [Finset.card_map, Finset.card_univ, Nat.card_Icc, Sym.card_sym_eq_multichoose,
      card_slots, card_pairSlots]
  have hlift : (∏ _g : Fin G, (τ₀ _g + 2 * n + 1 - τ₀ _g)) ≤
      ∏ g ∈ Finset.range G, (2 * n + D.period g) := by
    rw [← Fin.prod_univ_eq_prod_range]
    exact Finset.prod_le_prod' fun g _ => by have := hdpos g; omega
  have hwin : Fintype.card A ^ min n D.windowLength ≤ Fintype.card A ^ D.windowLength :=
    Nat.pow_le_pow_right hA (min_le_right _ _)
  have hsrc : (∏ g : D.sources, Nat.multichoose (D.period g.1 * Fintype.card A) n) *
      (∏ p : D.sources × D.offsets,
        Nat.multichoose (D.period p.1.1 * Fintype.card A ^ 2) (n - p.2.1)) =
      ∏ g ∈ D.sources, (Nat.choose (n + D.period g * Fintype.card A - 1)
        (D.period g * Fintype.card A - 1) *
        ∏ δ ∈ D.offsets, Nat.choose (n - δ + D.period g * Fintype.card A ^ 2 - 1)
          (D.period g * Fintype.card A ^ 2 - 1)) := by
    rw [Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    rw [← Finset.prod_coe_sort D.sources]
    refine Finset.prod_congr rfl fun g _ => ?_
    have h1 : 1 ≤ D.period g.1 * Fintype.card A := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (hne g.1).out (by omega))
    have h2 : 1 ≤ D.period g.1 * Fintype.card A ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (hne g.1).out (by positivity))
    rw [multichoose_eq_choose h1, ← Finset.prod_coe_sort D.offsets]
    congr 1
    exact Finset.prod_congr rfl fun δ _ => multichoose_eq_choose h2
  rw [hcard]
  unfold capacityBound
  calc (∏ _g : Fin G, (τ₀ _g + 2 * n + 1 - τ₀ _g)) *
        ((∏ g : D.sources, Nat.multichoose (D.period g.1 * Fintype.card A) n) *
          ((∏ p : D.sources × D.offsets,
            Nat.multichoose (D.period p.1.1 * Fintype.card A ^ 2) (n - p.2.1)) *
            Fintype.card A ^ min n D.windowLength))
      = (∏ _g : Fin G, (τ₀ _g + 2 * n + 1 - τ₀ _g)) *
          ((∏ g : D.sources, Nat.multichoose (D.period g.1 * Fintype.card A) n) *
            (∏ p : D.sources × D.offsets,
              Nat.multichoose (D.period p.1.1 * Fintype.card A ^ 2) (n - p.2.1))) *
            Fintype.card A ^ min n D.windowLength := by ac_rfl
    _ ≤ (∏ g ∈ Finset.range G, (2 * n + D.period g)) *
          (∏ g ∈ D.sources, (Nat.choose (n + D.period g * Fintype.card A - 1)
            (D.period g * Fintype.card A - 1) *
            ∏ δ ∈ D.offsets, Nat.choose (n - δ + D.period g * Fintype.card A ^ 2 - 1)
              (D.period g * Fintype.card A ^ 2 - 1))) * Fintype.card A ^ D.windowLength := by
        rw [hsrc]
        exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hlift) hwin
    _ = _ := by ac_rfl

/-- [proved-derived; formal-checked] **Capacity (R2 H1, R3 H1).** After `n` cells the persisting
source state takes at most `N(n)` values: it lies in a box of at most `N(n)` states. Where
`N(n) < |A|^n`, the source → state map on `A^n` is not injective (pigeonhole): the moment is lossy
by construction, a quotient and not a code of its cells. -/
theorem moment_capacity [Nonempty A] (hd : ∀ g, 2 ≤ D.period g)
    (hδpos : ∀ δ ∈ D.offsets, 1 ≤ δ) (τ₀ : ℕ → ℕ) (G n : ℕ) :
    (∀ l : List A, l.length = n → D.persist G (D.stream τ₀ l) ∈ D.box τ₀ G n) ∧
      (D.box τ₀ G n).card ≤ D.capacityBound G (Fintype.card A) n ∧
      (D.capacityBound G (Fintype.card A) n < Fintype.card A ^ n →
        ¬ Function.Injective fun v : Fin n → A => D.persist G (D.stream τ₀ (List.ofFn v))) := by
  refine ⟨fun l hl => hl ▸ persist_mem_box hd hδpos τ₀ G l, card_box_le τ₀ G n, fun hlt hinj => ?_⟩
  let f' : (Fin n → A) → D.box τ₀ G n := fun v =>
    ⟨D.persist G (D.stream τ₀ (List.ofFn v)), by
      simpa using persist_mem_box hd hδpos τ₀ G (List.ofFn v)⟩
  have hinj' : Function.Injective f' := fun v w h => hinj (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f' hinj'
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe] at hcard
  have := card_box_le (D := D) τ₀ G n
  omega

omit [Fintype A] [DecidableEq A] hne in
/-- [proved-derived; formal-checked] **`N(n)` is log-concave past the window.** Every factor is:
the window constant, each lift range `2n + d_g`, each stars-and-bars count `C(n + S − 1, S − 1)`,
and each offset count `C(n − δ + S' − 1, S' − 1)` from `n ≥ δ`. -/
theorem capacityBound_logConcave (hd1 : ∀ g, 1 ≤ D.period g) {alphabet : ℕ}
    (halphabet : 1 ≤ alphabet) (G : ℕ) :
    LogConcaveFrom D.windowLength (D.capacityBound G alphabet) := by
  have hchoose : ∀ S, 1 ≤ S → ∀ δ, δ ≤ D.windowLength →
      LogConcaveFrom D.windowLength fun n => Nat.choose (n - δ + S - 1) (S - 1) := by
    intro S hS δ hδ n hn
    have h' := logConcave_shift (logConcave_choose (S - 1)) δ n (hδ.trans hn)
    simpa only [show ∀ k, k - δ + S - 1 = k - δ + (S - 1) from fun k => by omega] using h'
  have hS : ∀ g, 1 ≤ D.period g * alphabet := fun g =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hd1 g; omega) (by omega))
  have hS2 : ∀ g, 1 ≤ D.period g * alphabet ^ 2 := fun g =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by have := hd1 g; omega) (by positivity))
  unfold capacityBound
  refine ((logConcave_const _ _).mul (LogConcaveFrom.prod _ _ fun g _ => ?_)).mul
    (LogConcaveFrom.prod _ _ fun g _ => LogConcaveFrom.mul ?_
      (LogConcaveFrom.prod _ _ fun δ hδ => hchoose _ (hS2 g) δ (Finset.le_sup (f := id) hδ)))
  · exact logConcave_linear _ 2 (D.period g)
  · simpa using hchoose _ (hS g) 0 (Nat.zero_le _)

omit [Fintype A] [DecidableEq A] hne in
theorem capacityBound_pos (hd1 : ∀ g, 1 ≤ D.period g) {alphabet : ℕ} (halphabet : 1 ≤ alphabet)
    (G n : ℕ) : 0 < D.capacityBound G alphabet n := by
  unfold capacityBound
  refine Nat.mul_pos (Nat.mul_pos (by positivity) (Finset.prod_pos fun g _ => ?_))
    (Finset.prod_pos fun g _ => Nat.mul_pos (Nat.choose_pos (by omega))
      (Finset.prod_pos fun δ _ => Nat.choose_pos (by omega)))
  have := hd1 g; omega

omit [DecidableEq A] hne in
/-- [proved-derived; formal-checked] **The admitted regime is lossy for good (R3 H1).** If the
count falls below `|A|ⁿ` at a first crossing `n*` past the window (`N(n*) < |A|^(n*)` and
`N(n* − 1) ≥ |A|^(n* − 1)`), it stays below at every later `n`, so the moment is lossy by
construction at every declared population of at least `n*` cells. -/
theorem capacity_persists [Nonempty A] (hd1 : ∀ g, 1 ≤ D.period g) (G : ℕ) {nstar : ℕ}
    (hstar : D.windowLength + 1 ≤ nstar)
    (hbelow : D.capacityBound G (Fintype.card A) nstar < Fintype.card A ^ nstar)
    (habove : Fintype.card A ^ (nstar - 1) ≤ D.capacityBound G (Fintype.card A) (nstar - 1)) :
    ∀ n, nstar ≤ n → D.capacityBound G (Fintype.card A) n < Fintype.card A ^ n :=
  stays_below_of_logConcave (capacityBound_logConcave hd1 Fintype.card_pos G)
    (capacityBound_pos hd1 Fintype.card_pos G) hstar hbelow habove

end Capacity

end SourceDecl

/-! ## 6. The directed-contrast law (moved from the retired `GeneratorSourceEpisode`) -/

section DirectedContrast

variable {R : Type*} [CommRing R]

/-- [definition] A directed contact between two source cells, of a declared kind. -/
structure DirectedContact (Cell Kind : Type*) where
  from_ : Cell
  to_ : Cell
  kind : Kind

/-- [definition] **The pooled directed contrast** at a target cell and kind: every contact of that
kind into the target contributes `source target − source from`; repeated contacts keep their
multiplicity. -/
def pooledContrast {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → R)
    (target : Cell) (kind : Kind) (site : Site) (axis : Axis) : R :=
  ∑ edge, if (contacts edge).kind = kind ∧ (contacts edge).to_ = target then
    source target site axis - source (contacts edge).from_ site axis else 0

/-- [definition] **The incidence pullback**: a covector on the pooled contrasts returns `+` at each
contact's target and `−` at its source, read at the contact's kind. -/
def pooledContrastPullback {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (covector : Cell → Kind → Site → Axis → R)
    (cell : Cell) (site : Site) (axis : Axis) : R :=
  (∑ edge, if (contacts edge).to_ = cell then
      covector (contacts edge).to_ (contacts edge).kind site axis else 0) -
    (∑ edge, if (contacts edge).from_ = cell then
      covector (contacts edge).to_ (contacts edge).kind site axis else 0)

/-- [proved-derived; formal-checked] An absent kind pools to zero. -/
theorem pooledContrast_zero_of_absent_kind {Cell Kind Site Axis Edge : Type*}
    [Fintype Edge] [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → R) (kind : Kind)
    (absent : ∀ edge, (contacts edge).kind ≠ kind)
    (target : Cell) (site : Site) (axis : Axis) :
    pooledContrast contacts source target kind site axis = 0 := by
  simp [pooledContrast, absent]

/-- [proved-derived; formal-checked] **The pullback is the incidence adjoint of the pooled
contrast**: pairing a covector with the pooled contrasts equals pairing its pullback with the
source chart, `⟨g, C s⟩ = ⟨Cᵀ g, s⟩`, with every repeated contact counted. -/
theorem pooledContrast_pairing_adjoint {Cell Kind Site Axis Edge : Type*}
    [Fintype Cell] [Fintype Kind] [Fintype Site] [Fintype Axis] [Fintype Edge]
    [DecidableEq Cell] [DecidableEq Kind]
    (contacts : Edge → DirectedContact Cell Kind)
    (source : Cell → Site → Axis → R)
    (covector : Cell → Kind → Site → Axis → R) :
    (∑ target, ∑ kind, ∑ site, ∑ axis,
        covector target kind site axis * pooledContrast contacts source target kind site axis) =
      ∑ cell, ∑ site, ∑ axis,
        pooledContrastPullback contacts covector cell site axis * source cell site axis := by
  -- Both sides are the edgewise sum `Σ_e Σ_site Σ_axis g(to_e, kind_e) (s(to_e) − s(from_e))`.
  have edgewise : ∀ edge : Edge,
      (∑ target, ∑ kind, ∑ site, ∑ axis, covector target kind site axis *
        (if (contacts edge).kind = kind ∧ (contacts edge).to_ = target then
          source target site axis - source (contacts edge).from_ site axis else 0)) =
      ∑ cell, ∑ site, ∑ axis,
        ((if (contacts edge).to_ = cell then
          covector (contacts edge).to_ (contacts edge).kind site axis else 0) -
         (if (contacts edge).from_ = cell then
          covector (contacts edge).to_ (contacts edge).kind site axis else 0)) *
          source cell site axis := by
    intro edge
    rw [Fintype.sum_eq_single (contacts edge).to_ (fun t ht => by simp [Ne.symm ht]),
      Fintype.sum_eq_single (contacts edge).kind (fun k hk => by simp [Ne.symm hk])]
    simp only [sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib]
    rw [Fintype.sum_eq_single (contacts edge).to_ (fun t ht => by simp [Ne.symm ht]),
      Fintype.sum_eq_single (contacts edge).from_ (fun t ht => by simp [Ne.symm ht])]
    simp [mul_sub, Finset.sum_sub_distrib]
  calc (∑ target, ∑ kind, ∑ site, ∑ axis,
        covector target kind site axis * pooledContrast contacts source target kind site axis)
      = ∑ edge : Edge, ∑ target, ∑ kind, ∑ site, ∑ axis, covector target kind site axis *
        (if (contacts edge).kind = kind ∧ (contacts edge).to_ = target then
          source target site axis - source (contacts edge).from_ site axis else 0) := by
        simp only [pooledContrast, Finset.mul_sum]
        symm
        rw [Finset.sum_comm (γ := Edge)]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_comm (γ := Edge)]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_comm (γ := Edge)]
        refine Finset.sum_congr rfl fun _ _ => ?_
        rw [Finset.sum_comm (γ := Edge)]
    _ = ∑ edge : Edge, ∑ cell, ∑ site, ∑ axis,
        ((if (contacts edge).to_ = cell then
          covector (contacts edge).to_ (contacts edge).kind site axis else 0) -
         (if (contacts edge).from_ = cell then
          covector (contacts edge).to_ (contacts edge).kind site axis else 0)) *
          source cell site axis := Finset.sum_congr rfl fun edge _ => edgewise edge
    _ = _ := by
        simp only [pooledContrastPullback, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
        congr 1 <;>
        · rw [Finset.sum_comm (γ := Edge)]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_comm (γ := Edge)]
          refine Finset.sum_congr rfl fun _ _ => ?_
          rw [Finset.sum_comm (γ := Edge)]

/-- [counterexample; formal-checked] **Multiplicity is kept.** Two copies of the contact `0 → 1`
pool twice the contrast of one. -/
theorem repeated_contact_doubles_its_contrast :
    pooledContrast (R := ℚ) (fun _ : Fin 2 => (⟨0, 1, ()⟩ : DirectedContact (Fin 2) Unit))
        (fun cell (_ : Unit) (_ : Unit) => if cell = 1 then 1 else 0) 1 () () () = 2 ∧
      pooledContrast (R := ℚ) (fun _ : Fin 1 => (⟨0, 1, ()⟩ : DirectedContact (Fin 2) Unit))
        (fun cell (_ : Unit) (_ : Unit) => if cell = 1 then 1 else 0) 1 () () () = 1 := by
  constructor <;> simp [pooledContrast]

end DirectedContrast

/-- [definition] One source ring of period `2`, no locks, no offsets, over `Bool` cells. -/
def oneSourceRing : SourceDecl Bool where
  period _ := 2
  lock _ := ∅
  code _ := 0
  sources := {0}
  offsets := ∅

/-- [counterexample; formal-checked] **Below capacity the moment can be a code of its cells.** For
one-cell passages the counts separate `[true]` from `[false]`: the source → state map is injective
there, so the hypothesis `N(n) < |A|^n` of `moment_capacity` is what makes the moment lossy. -/
theorem below_capacity_separates :
    (oneSourceRing.stream (fun _ => 0) [true]).bins 0 ≠
      (oneSourceRing.stream (fun _ => 0) [false]).bins 0 := by
  have ht := SourceDecl.stream_bins_append_one (D := oneSourceRing) (fun _ => 0)
    (Finset.mem_singleton_self 0) [] true
  have hf := SourceDecl.stream_bins_append_one (D := oneSourceRing) (fun _ => 0)
    (Finset.mem_singleton_self 0) [] false
  rw [List.nil_append] at ht hf
  rw [ht, hf]
  intro h
  have hmem := Multiset.mem_cons_self
    ((oneSourceRing.advance true (oneSourceRing.run [] fun _ => 0) 0 :
      ZMod (oneSourceRing.period 0)), true) ((oneSourceRing.stream (fun _ => 0) []).bins 0)
  rw [h, Multiset.mem_cons] at hmem
  rcases hmem with hmem | hmem
  · exact Bool.noConfusion (congrArg Prod.snd hmem)
  · exact absurd hmem (Multiset.notMem_zero _)

section Audit
#print axioms SelectiveDecl.selective_position
#print axioms SelectiveDecl.carryIn_le_one
#print axioms SelectiveDecl.position_eq_key_add_steps
#print axioms notch_steps_depend_on_own_key
#print axioms earlier_phase_class_is_load_bearing
#print axioms closingRing_moment_is_phaseBinned
#print axioms nonclosing_binning_fails
#print axioms encoderMoment_contract
#print axioms encoder_covector_tape_free
#print axioms exteriorOffset_independent_of_E
#print axioms open_eq_clockedRing_moment
#print axioms SourceDecl.selectiveClock_stream_descent
#print axioms SourceDecl.binsMoment_stream
#print axioms SourceDecl.moment_capacity
#print axioms SourceDecl.capacity_persists
#print axioms logConcavity_is_load_bearing
#print axioms below_capacity_separates
#print axioms pooledContrast_pairing_adjoint
#print axioms repeated_contact_doubles_its_contrast
end Audit

end Holonics.HNN.Moment

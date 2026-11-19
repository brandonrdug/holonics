import Holonics.Physics.Thermal.ChainAxes

/-!
# The chain axes joined to the path reversal: the lift's entropy reading and the mean carry

[definition] Source: the formal-obligations issue (#410), box "The chain axes (from #5)":
`Physics/Thermal/ChainAxes.entropy_reading` identified with `Aeon/Production/PathReversal`'s path
log ratio (`pathLogRatio_split`) along an oriented chain through a neck, and the mean signed
crossing rate as the current. Both targets were stated in the `[open]` paragraph of `ChainAxes`; the time/entropy
crossing (#5) is the aeon record's
(`research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md`). Atlas
`heat.time-entropy-helix`, `heat.ring-current-affinity`, `aeon.production-state-heat`,
`aeon.signed-flux`, `aeon.forward-aeon`.

A ring of `N = M + 3` cells (`Fin (M + 3)`, as in `ChainAxes`) carries a chain `P` and a law `π`.
A **ring path** `γ : Fin (n + 1) → Fin N` stays or moves one cell at every step (`RingPath`). Its
**lift** to `ℤ` starts at `(γ 0 : ℕ)` and adds `+1`, `−1` or `0` per step (`lift`), and its
**lift word** on the one-navigator lift `clockLift (Fin 1)` takes the edge from `z` along its
orientation for a forward step, the edge from `z − 1` against it for a backward step, and nothing
for a held step (`stepWord`, `liftWord`, `liftAeon`). The irreversibility on the lift reads the
medium's affinity of junction `z mod N` (`liftAffinity`), and the cell under a lift point is
`z mod N` (`cell`). The **carry steps** of a path are its steps `N − 1 → 0` (forward) and
`0 → N − 1` (backward), and its **signed carry count** is their difference (`carryCount`).

[proved-derived; formal-checked] What is proved.

1. **The lift projects back** (`cell_lift`, `lift_emod`): `lift γ i mod N = γ i` for every ring
   path.
2. **The lift's entropy reading is the path's affinity sum**:
   `wordReading (entropyForm a) (lift word of γ) = Σ_i affinity P (γ i) (γ (i+1))`
   (`wordReading_liftWord`), for every ring path, with no positivity: a held step reads
   `affinity P x x = 0` and a backward step reads `−affinity P y x = affinity P x y`
   (`affinity_self`, `affinity_swap`). Composed with `pathLogRatio_split` and `entropy_reading`,
   a positive path of an admissible nearest-neighbour ring chain (`π > 0`, symmetric support)
   reads
   **`log(P_γ / P_(Rγ)) = (log π(γ₀) − log π(γₙ)) + (s(γₙ) − s(γ₀)) + A · (signed crossings)`**
   (`pathLogRatio_eq_entropy_reading`, `pathLogRatio_eq_carry_reading`): the state term, the change
   of the entropy coordinate and the turn `A` of the helix times the signed crossings of the lift
   at the carry section `sectionForm 0 N`.
3. **The crossings are the carry steps** (`forwardCrossings_liftWord`,
   `backwardCrossings_liftWord`): the lift's forward and backward crossings of the carry section
   count the path's steps `N − 1 → 0` and `0 → N − 1`, and their difference is the whole windings
   of the lift, `⌊lift γ n / N⌋` (`carryCount_eq_winding`).
4. **The mean signed crossing is the current.** Under a stationary law of a stochastic chain, the
   pair of every step has the flow law `π x P(x, y)` (`pair_marginal`), so an additive path
   functional has mean `n` times its one-step mean (`mean_step_sum`). For the signed carry count
   this is `n · ringNet π P (N − 1)` (`mean_carryCount`), and on a nearest-neighbour ring,
   `n · J` with `J` the one net current (`mean_carryCount_eq_current`, by
   `ChainAxes.ring_nets_eq`). The same mean read on the lift's crossings and on the lift's
   windings is `n · J` (`mean_liftCrossings_eq_current`, `mean_liftWinding_eq_current`).
5. **The carry term carries `n · σ`.** On a positive ring the helix's turn is the cycle affinity
   (`turn_eq_cycleAffinity`), so the mean of the carry term `A · (signed carry count)` is
   `n · J · A = n · σ`, Schnakenberg's ring production (`mean_carryTerm_eq_production`).
6. **What reverses.** Relabelling the cells by `Fin.rev` negates the signed carry count
   (`carryCount_rev`) and the mean signed carry count, for every law
   (`mean_carryCount_reflect`), so the reflected stationary ring reads `−n · J`
   (`mean_carryCount_reflect_eq_current`): the path-law form of `ChainAxes.ring_reversal`.
7. **A witness.** The biased rotation of three cells (`PathReversal.Rotation`: forward `2/3`, back
   `1/3`, uniform law) carries `J = 1/9` (`rotation_current`); its mean signed crossing over two
   steps is `2/9` (`rotation_mean_carryCount`), and its mean carry term over two steps is
   `(2/3) log 2`, its production over two epochs (`rotation_mean_carryTerm`).

What is not claimed. The sums over paths are the path law's weighted sums: a mean in the sense of
probability when `π` sums to one, which the statements do not assume. No statement depends on the
neck beyond `ChainAxes.production_le_neck`: the carry section is a choice of chart, and the
identification and the mean hold at `N − 1 → 0` without reference to the least forward flow.
That the mean carry term equals `PathReversal`'s production `σₙ = n σ` for every ring (the epoch
production of a ring read as its ring production) is read here on the witness only. Continuous-time
chains, infinite chains and rings of fewer than three cells are not treated.

Computational object: the helical pair interaction, read on a ring chain. The ring of cells is the
circle and the lift to `ℤ` is the helix, whose carry is taken at the carry section (**helix**:
circle plus carry, `⌊lift / N⌋` the windings); each junction is a pair read in both directions,
its affinity the logarithm of the ratio of its two transition weights (**pair**); and the cell
`z mod N` against the windings `⌊z / N⌋` is the residue and carry of a placement (**faces and
placement**). Cell holonomy, the tube and the tower thread stay attached: the turn is the
holonomy of the affinity clock on the ring's declared circuit, read here, not on a two-cell.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Thermal.ChainPathJoin

open Finset Holonics.Aeon.Production Holonics.Aeon.Production.PathReversal
open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Winding
  Holonics.Aeon.Clock.Epoch
open Holonics.Physics.Thermal.ChainAxes

/-! ## 1. Words on the lift -/

section Words

variable {V E F : Type*}

/-- [proved-derived; formal-checked] Blocks chained end to end chain their concatenation. -/
theorem chained_flatten (K : ParametricComplex V E F) :
    ∀ {n : ℕ} (u : Fin (n + 1) → V) (b : Fin n → List (E × Bool)),
      (∀ i, K.Chained (u i.castSucc) (b i) (u i.succ)) →
        K.Chained (u 0) (List.ofFn b).flatten (u (Fin.last n))
  | 0, u, b, _ => by simp
  | n + 1, u, b, h => by
    rw [List.ofFn_succ, List.flatten_cons]
    have h0 := h 0
    rw [Fin.castSucc_zero] at h0
    refine K.chained_append h0 ?_
    have := chained_flatten K (fun i => u i.succ) (fun i => b i.succ) fun i => by
      simpa only [Fin.succ_castSucc] using h i.succ
    simpa only [Fin.succ_last] using this

/-- [proved-derived; formal-checked] A form reads a concatenation as the sum of its blocks. -/
theorem wordReading_flatten {A : Type*} [AddCommGroup A] (ω : E → A) :
    ∀ {n : ℕ} (b : Fin n → List (E × Bool)),
      wordReading ω (List.ofFn b).flatten = ∑ i, wordReading ω (b i)
  | 0, b => by simp
  | n + 1, b => by
    rw [List.ofFn_succ, List.flatten_cons, wordReading_append, wordReading_flatten ω,
      Fin.sum_univ_succ]

/-- [proved-derived; formal-checked] Forward crossings of a concatenation add over its blocks. -/
theorem forwardCrossings_flatten (ω : E → ℤ) :
    ∀ {n : ℕ} (b : Fin n → List (E × Bool)),
      forwardCrossings ω (List.ofFn b).flatten = ∑ i, forwardCrossings ω (b i)
  | 0, b => by simp [forwardCrossings]
  | n + 1, b => by
    rw [List.ofFn_succ, List.flatten_cons, forwardCrossings_append, forwardCrossings_flatten ω,
      Fin.sum_univ_succ]

/-- [proved-derived; formal-checked] Backward crossings of a concatenation add over its blocks. -/
theorem backwardCrossings_flatten (ω : E → ℤ) :
    ∀ {n : ℕ} (b : Fin n → List (E × Bool)),
      backwardCrossings ω (List.ofFn b).flatten = ∑ i, backwardCrossings ω (b i)
  | 0, b => by simp [backwardCrossings]
  | n + 1, b => by
    rw [List.ofFn_succ, List.flatten_cons, backwardCrossings_append, backwardCrossings_flatten ω,
      Fin.sum_univ_succ]

end Words

/-! ## 2. The cell of a lift point -/

section Cell

variable {M : ℕ}

/-- [definition] The cell of the ring under a lift point: `z mod N`, with `N = M + 3`. -/
def cell (z : ℤ) : Fin (M + 3) :=
  ⟨(z % ((M + 3 : ℕ) : ℤ)).toNat, by
    have h0 := Int.emod_nonneg z (show ((M + 3 : ℕ) : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos z (show (0 : ℤ) < ((M + 3 : ℕ) : ℤ) by omega)
    omega⟩

/-- [proved-standard; formal-checked] The cell's value is the residue `z mod N`. -/
theorem cell_val (z : ℤ) : (((cell (M := M) z : ℕ)) : ℤ) = z % ((M + 3 : ℕ) : ℤ) := by
  have h0 := Int.emod_nonneg z (show ((M + 3 : ℕ) : ℤ) ≠ 0 by omega)
  simp only [cell, Int.toNat_of_nonneg h0]

/-- [proved-standard; formal-checked] A cell's own value lies over that cell. -/
theorem cell_natCast (x : Fin (M + 3)) : cell (M := M) ((x : ℕ) : ℤ) = x := by
  apply Fin.ext
  have h := cell_val (M := M) ((x : ℕ) : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by omega)] at h
  exact_mod_cast h

/-- [proved-standard; formal-checked] One step up the lift is one cell forward on the ring. -/
theorem cell_add_one (z : ℤ) : cell (M := M) (z + 1) = cell z + 1 := by
  apply Fin.ext
  have h1 : (((cell (M := M) z + 1 : Fin (M + 3)) : ℕ) : ℤ) =
      (z % ((M + 3 : ℕ) : ℤ) + 1) % ((M + 3 : ℕ) : ℤ) := by
    rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < M + 3 by omega)]
    push_cast
    rw [cell_val]
    push_cast
    rfl
  have h2 := cell_val (M := M) (z + 1)
  rw [Int.emod_add_emod] at h1
  exact_mod_cast h2.trans h1.symm

/-- [proved-standard; formal-checked] A full period of the lift returns to the same cell. -/
theorem cell_add_period (z : ℤ) : cell (M := M) (z + ((M + 3 : ℕ) : ℤ)) = cell z := by
  apply Fin.ext
  have h := cell_val (M := M) (z + ((M + 3 : ℕ) : ℤ))
  rw [Int.add_emod_right, ← cell_val] at h
  exact_mod_cast h

/-- [proved-standard; formal-checked] A lift point lies over cell `0` if and only if `N` divides it. -/
theorem cell_eq_zero_iff (z : ℤ) : cell (M := M) z = 0 ↔ ((M + 3 : ℕ) : ℤ) ∣ z := by
  rw [Int.dvd_iff_emod_eq_zero, ← cell_val, Fin.ext_iff, Fin.val_zero]
  omega

end Cell

/-! ## 3. The lift of a ring path -/

section Lift

variable {M n : ℕ}

/-- [definition] **A ring path**: every step stays or moves one cell around the circle (the path
form of `ChainAxes.RingNeighbour`). -/
def RingPath (γ : Fin (n + 1) → Fin (M + 3)) : Prop :=
  ∀ i : Fin n, γ i.succ = γ i.castSucc ∨ γ i.succ = γ i.castSucc + 1 ∨ γ i.castSucc = γ i.succ + 1

/-- [proved-standard; formal-checked] On at least three cells a step forward moves. -/
theorem add_one_ne_self (x : Fin (M + 3)) : x + 1 ≠ x := fun h =>
  one_ne_zero_ring (M := M) (add_eq_left.mp h)

/-- [proved-standard; formal-checked] On at least three cells two steps forward move. -/
theorem add_two_ne_self (x : Fin (M + 3)) : x + 1 + 1 ≠ x := fun h => by
  rw [add_assoc] at h
  exact two_ne_zero_ring (M := M) (add_eq_left.mp h)

/-- [definition] The displacement of one step on the lift: `+1` forward, `−1` backward, `0` held. -/
def stepDelta (x y : Fin (M + 3)) : ℤ := if y = x + 1 then 1 else if x = y + 1 then -1 else 0

/-- [proved-derived; formal-checked] A held step does not move on the lift. -/
theorem stepDelta_stay (x : Fin (M + 3)) : stepDelta x x = 0 := by
  simp [stepDelta, (add_one_ne_self x).symm]

/-- [proved-derived; formal-checked] A forward step moves `+1` on the lift. -/
theorem stepDelta_forward (x : Fin (M + 3)) : stepDelta x (x + 1) = 1 := by simp [stepDelta]

/-- [proved-derived; formal-checked] A backward step moves `−1` on the lift. -/
theorem stepDelta_backward (y : Fin (M + 3)) : stepDelta (y + 1) y = -1 := by
  simp [stepDelta, (add_two_ne_self y).symm]

/-- [definition] **The lift of a ring path** to `ℤ`: it starts at `(γ 0 : ℕ)` and adds each step's
displacement. -/
def lift (γ : Fin (n + 1) → Fin (M + 3)) (i : Fin (n + 1)) : ℤ :=
  ((γ 0 : ℕ) : ℤ) + Fin.partialSum (fun j : Fin n => stepDelta (γ j.castSucc) (γ j.succ)) i

/-- [proved-derived; formal-checked] The lift starts at the first cell's value. -/
theorem lift_zero (γ : Fin (n + 1) → Fin (M + 3)) : lift γ 0 = ((γ 0 : ℕ) : ℤ) := by
  simp [lift]

/-- [proved-derived; formal-checked] The lift adds each step's displacement. -/
theorem lift_succ (γ : Fin (n + 1) → Fin (M + 3)) (i : Fin n) :
    lift γ i.succ = lift γ i.castSucc + stepDelta (γ i.castSucc) (γ i.succ) := by
  simp only [lift, Fin.partialSum_succ]
  ring

/-- [proved-derived; formal-checked] **The lift projects back to the path**: the cell under the
lift point of occurrence `i` is `γ i`. -/
theorem cell_lift {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) (i : Fin (n + 1)) :
    cell (lift γ i) = γ i := by
  induction i using Fin.induction with
  | zero => rw [lift_zero, cell_natCast]
  | succ i ih =>
    rw [lift_succ]
    rcases hγ i with h | h | h
    · rw [h, stepDelta_stay, add_zero, ih]
    · rw [h, stepDelta_forward, cell_add_one, ih]
    · rw [h, stepDelta_backward]
      have h1 := cell_add_one (M := M) (lift γ i.castSucc + -1)
      rw [neg_add_cancel_right, ih, h] at h1
      exact add_right_cancel h1.symm

/-- [proved-derived; formal-checked] **The lift read mod `N`** is the path: `lift i mod N = γ i`. -/
theorem lift_emod {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) (i : Fin (n + 1)) :
    lift γ i % ((M + 3 : ℕ) : ℤ) = ((γ i : ℕ) : ℤ) := by
  rw [← cell_val, cell_lift hγ]

/-- [proved-derived; formal-checked] The lift's residue, read in `ℕ`, is the path's cell. -/
theorem lift_emod_toNat {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) (i : Fin (n + 1)) :
    (lift γ i % ((M + 3 : ℕ) : ℤ)).toNat = γ i := by
  rw [lift_emod hγ, Int.toNat_natCast]

/-- [definition] The word of one step on the one-navigator lift `clockLift (Fin 1)` from `z`: the
edge from `z` along its orientation forward, the edge from `z − 1` against it backward, nothing
for a held step. -/
def stepWord (z : ℤ) (x y : Fin (M + 3)) : List (((Fin 1 → ℤ) × Fin 1) × Bool) :=
  if y = x + 1 then [((fun _ => z, 0), true)]
  else if x = y + 1 then [((fun _ => z + -1, 0), false)] else []

/-- [proved-derived; formal-checked] One step's word is chained from `z` to `z + stepDelta`. -/
theorem stepWord_chained (z : ℤ) (x y : Fin (M + 3)) :
    (clockLift (Fin 1)).Chained (fun _ => z) (stepWord z x y) (fun _ => z + stepDelta x y) := by
  unfold stepWord stepDelta
  split_ifs with h1 h2
  · simp only [ParametricComplex.chained_cons, ParametricComplex.chained_nil, clockLift,
      ParametricComplex.start, ParametricComplex.finish, if_true]
    refine ⟨trivial, ?_⟩
    funext j
    rw [Subsingleton.elim j 0]
    simp
  · simp only [ParametricComplex.chained_cons, ParametricComplex.chained_nil, clockLift,
      ParametricComplex.start, ParametricComplex.finish, Bool.false_eq_true, if_false]
    refine ⟨?_, trivial⟩
    funext j
    rw [Subsingleton.elim j 0]
    simp
  · simp

/-- [definition] **The lift word of a ring path**: its steps' words, chained along the lift. -/
def liftWord (γ : Fin (n + 1) → Fin (M + 3)) : List (((Fin 1 → ℤ) × Fin 1) × Bool) :=
  (List.ofFn fun i : Fin n => stepWord (lift γ i.castSucc) (γ i.castSucc) (γ i.succ)).flatten

/-- [definition] **The lift aeon of a ring path**, from its first to its last lift point. -/
def liftAeon (γ : Fin (n + 1) → Fin (M + 3)) :
    Aeon (clockLift (Fin 1)) (fun _ => lift γ 0) (fun _ => lift γ (Fin.last n)) :=
  ⟨liftWord γ, chained_flatten _ (fun i _ => lift γ i) _ fun i => by
    rw [lift_succ]
    exact stepWord_chained _ _ _⟩

end Lift

/-! ## 4. The entropy clock of the lift is the path's affinity sum -/

section Identification

variable {M n : ℕ}

/-- [definition] **The irreversibility on the lift**: junction `z` reads the medium's affinity
`log(P(z mod N, z+1 mod N) / P(z+1 mod N, z mod N))`. -/
noncomputable def liftAffinity (P : Fin (M + 3) → Fin (M + 3) → ℝ) (z : ℤ) : ℝ :=
  RealChart.affinity P (cell z) (cell (z + 1))

/-- [proved-derived; formal-checked] The irreversibility on the lift has period `N`. -/
theorem liftAffinity_periodic (P : Fin (M + 3) → Fin (M + 3) → ℝ) :
    Function.Periodic (liftAffinity P) ((M + 3 : ℕ) : ℤ) := fun z => by
  unfold liftAffinity
  rw [cell_add_period, add_right_comm, cell_add_period]

/-- [proved-standard; formal-checked] A held step has affinity `0`, positive or not. -/
theorem affinity_self (P : Fin (M + 3) → Fin (M + 3) → ℝ) (x : Fin (M + 3)) :
    RealChart.affinity P x x = 0 := by
  unfold RealChart.affinity
  by_cases h : P x x = 0
  · rw [h, div_zero, Real.log_zero]
  · rw [div_self h, Real.log_one]

/-- [proved-standard; formal-checked] The affinity changes sign with the step's direction. -/
theorem affinity_swap (P : Fin (M + 3) → Fin (M + 3) → ℝ) (x y : Fin (M + 3)) :
    RealChart.affinity P y x = -RealChart.affinity P x y := by
  unfold RealChart.affinity
  rw [← Real.log_inv, inv_div]

/-- [proved-derived; formal-checked] One step's word reads its affinity on the lift's entropy clock. -/
theorem wordReading_stepWord (P : Fin (M + 3) → Fin (M + 3) → ℝ) {z : ℤ} {x y : Fin (M + 3)}
    (hz : cell z = x) (hxy : y = x ∨ y = x + 1 ∨ x = y + 1) :
    wordReading (entropyForm (liftAffinity P)) (stepWord z x y) = RealChart.affinity P x y := by
  rcases hxy with h | h | h
  · subst h
    simp [stepWord, (add_one_ne_self y).symm, affinity_self]
  · subst h
    simp [stepWord, wordReading, stepReading, entropyForm, liftAffinity, hz, cell_add_one]
  · subst h
    have hy : cell (z + -1) = y := by
      have h1 := cell_add_one (M := M) (z + -1)
      rw [neg_add_cancel_right, hz] at h1
      exact add_right_cancel h1.symm
    simp [stepWord, (add_two_ne_self y).symm, wordReading, stepReading, entropyForm,
      liftAffinity, hy, hz, affinity_swap P y (y + 1)]

/-- [proved-derived; formal-checked] **The lift's entropy reading is the path's affinity sum**:
`wordReading (entropyForm a) (lift γ) = Σ_i affinity P (γ i) (γ (i+1))` for every ring path. -/
theorem wordReading_liftWord (P : Fin (M + 3) → Fin (M + 3) → ℝ) {γ : Fin (n + 1) → Fin (M + 3)}
    (hγ : RingPath γ) :
    wordReading (entropyForm (liftAffinity P)) (liftWord γ) =
      ∑ i : Fin n, RealChart.affinity P (γ i.castSucc) (γ i.succ) := by
  rw [liftWord, wordReading_flatten]
  exact sum_congr rfl fun i _ => wordReading_stepWord P (cell_lift hγ i.castSucc) (hγ i)

/-- [proved-derived; formal-checked] A path of nonzero law under a ring chain is a ring path. -/
theorem ringPath_of_pathLaw_ne_zero {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hnn : RingNeighbour P) {γ : Fin (n + 1) → Fin (M + 3)} (h : pathLaw π P n γ ≠ 0) :
    RingPath γ := fun i =>
  hnn _ _ (prod_ne_zero_iff.mp (right_ne_zero_of_mul h) i (mem_univ i))

/-- [proved-derived; formal-checked] **The path log ratio is the entropy reading of the lift.**
For a positive path of a ring chain, `log(P_γ / P_(Rγ))` is the state term
`log π(γ₀) − log π(γₙ)` plus the change of the entropy coordinate plus the cycle affinity (the
helix's turn) times the signed crossings of the lift at the carry section. -/
theorem pathLogRatio_eq_entropy_reading {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hA : Admissible π P) (hnn : RingNeighbour P) {γ : Fin (n + 1) → Fin (M + 3)}
    (hpos : 0 < pathLaw π P n γ) :
    Real.log (pathLaw π P n γ / revLaw π P n γ) =
      (Real.log (π (γ 0)) - Real.log (π (γ (Fin.last n)))) +
        ((coordinate (liftAffinity P) (γ (Fin.last n)) - coordinate (liftAffinity P) (γ 0)) +
          turn (M + 3) (liftAffinity P) *
            (((forwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) : ℤ) -
              backwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) : ℤ) : ℝ)) := by
  have hγ := ringPath_of_pathLaw_ne_zero hnn hpos.ne'
  rw [RealChart.pathLogRatio_split hA hpos, ← wordReading_liftWord P hγ]
  have h := entropy_reading (N := M + 3) (by omega) (liftAffinity_periodic P) (liftAeon γ)
  simp only [lift_emod_toNat hγ] at h
  exact congrArg _ h

end Identification

/-! ## 5. The lift's crossings of the carry section are the path's carry steps -/

section Crossings

variable {M n : ℕ}

/-- [definition] The forward carry steps of a path: `N − 1 → 0`. -/
def forwardCarries (γ : Fin (n + 1) → Fin (M + 3)) : ℕ :=
  #(univ.filter fun i : Fin n => γ i.castSucc = Fin.last (M + 2) ∧ γ i.succ = 0)

/-- [definition] The backward carry steps of a path: `0 → N − 1`. -/
def backwardCarries (γ : Fin (n + 1) → Fin (M + 3)) : ℕ :=
  #(univ.filter fun i : Fin n => γ i.castSucc = 0 ∧ γ i.succ = Fin.last (M + 2))

/-- [definition] **The signed carry count** of a path: forward minus backward carry steps. -/
def carryCount (γ : Fin (n + 1) → Fin (M + 3)) : ℤ := (forwardCarries γ : ℤ) - backwardCarries γ

/-- [proved-standard; formal-checked] The last cell is not the first. -/
theorem last_ne_zero_ring : Fin.last (M + 2) ≠ (0 : Fin (M + 3)) := by
  rw [Ne, Fin.ext_iff, Fin.val_last, Fin.val_zero]
  omega

/-- [proved-standard; formal-checked] On at least three cells the last cell is not cell `1`. -/
theorem last_ne_one_ring : Fin.last (M + 2) ≠ (0 + 1 : Fin (M + 3)) := by
  rw [Ne, Fin.ext_iff, Fin.val_last, zero_add, Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  omega

/-- [proved-standard; formal-checked] A step forward lands on `0` if and only if it leaves the last cell. -/
theorem add_one_eq_zero_iff (x : Fin (M + 3)) : x + 1 = 0 ↔ x = Fin.last (M + 2) := by
  constructor
  · intro h
    have h2 : x + 1 = Fin.last (M + 2) + 1 := by rw [h]; exact (Fin.last_add_one (M + 2)).symm
    exact add_right_cancel h2
  · rintro rfl
    exact Fin.last_add_one (M + 2)

/-- [proved-derived; formal-checked] The carry section cuts the edge from `z` when `z + 1` is over `0`. -/
theorem sectionForm_lift_eq_one (z : ℤ) :
    sectionForm (0 : Fin 1) (M + 3) ((fun _ => z, 0) : (Fin 1 → ℤ) × Fin 1) = 1 ↔
      cell (M := M) (z + 1) = 0 := by
  rw [cell_eq_zero_iff]
  unfold sectionForm
  split_ifs with h
  · exact ⟨fun _ => h.2, fun _ => rfl⟩
  · exact ⟨fun h' => absurd h' (by norm_num), fun h' => absurd ⟨rfl, h'⟩ h⟩

/-- [proved-derived; formal-checked] A forward one-step word crosses when its edge is cut. -/
theorem forwardCrossings_single {E : Type*} (ω : E → ℤ) (e : E) :
    forwardCrossings ω [(e, true)] = if ω e = 1 then 1 else 0 := by
  unfold forwardCrossings
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] A backward one-step word crosses when its edge is cut. -/
theorem backwardCrossings_single {E : Type*} (ω : E → ℤ) (e : E) :
    backwardCrossings ω [(e, false)] = if ω e = 1 then 1 else 0 := by
  unfold backwardCrossings
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] One step crosses the carry section forward on `N − 1 → 0`. -/
theorem forwardCrossings_stepWord {z : ℤ} {x y : Fin (M + 3)} (hz : cell z = x)
    (hxy : y = x ∨ y = x + 1 ∨ x = y + 1) :
    forwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (stepWord z x y) =
      if x = Fin.last (M + 2) ∧ y = 0 then 1 else 0 := by
  rcases hxy with h | h | h
  · subst h
    have : ¬ (y = Fin.last (M + 2) ∧ y = 0) := fun h => last_ne_zero_ring (h.1.symm.trans h.2)
    simp [stepWord, (add_one_ne_self y).symm, forwardCrossings, this]
  · subst h
    have hc : cell (z + 1) = x + 1 := by rw [cell_add_one, hz]
    have hiff : (x = Fin.last (M + 2) ∧ x + 1 = 0) ↔ x + 1 = 0 :=
      ⟨fun h => h.2, fun h => ⟨(add_one_eq_zero_iff x).mp h, h⟩⟩
    rw [stepWord, if_pos rfl, forwardCrossings_single]
    simp only [sectionForm_lift_eq_one, hc, hiff]
  · subst h
    have : ¬ (y + 1 = Fin.last (M + 2) ∧ y = 0) := fun h => by
      rw [h.2] at h
      exact last_ne_one_ring h.1.symm
    simp [stepWord, (add_two_ne_self y).symm, forwardCrossings, this]

/-- [proved-derived; formal-checked] One step crosses the carry section backward on `0 → N − 1`. -/
theorem backwardCrossings_stepWord {z : ℤ} {x y : Fin (M + 3)} (hz : cell z = x)
    (hxy : y = x ∨ y = x + 1 ∨ x = y + 1) :
    backwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (stepWord z x y) =
      if x = 0 ∧ y = Fin.last (M + 2) then 1 else 0 := by
  rcases hxy with h | h | h
  · subst h
    have : ¬ (y = 0 ∧ y = Fin.last (M + 2)) := fun h => last_ne_zero_ring (h.2.symm.trans h.1)
    simp [stepWord, (add_one_ne_self y).symm, backwardCrossings, this]
  · subst h
    have : ¬ (x = 0 ∧ x + 1 = Fin.last (M + 2)) := fun h => by
      rw [h.1] at h
      exact last_ne_one_ring h.2.symm
    simp [stepWord, backwardCrossings, this]
  · subst h
    have hc : cell (z + -1 + 1) = y + 1 := by rw [neg_add_cancel_right, hz]
    have hiff : (y + 1 = 0 ∧ y = Fin.last (M + 2)) ↔ y + 1 = 0 :=
      ⟨fun h => h.1, fun h => ⟨h, (add_one_eq_zero_iff y).mp h⟩⟩
    rw [stepWord, if_neg (add_two_ne_self y).symm, if_pos rfl, backwardCrossings_single]
    simp only [sectionForm_lift_eq_one, hc, hiff]

/-- [proved-derived; formal-checked] **The lift's forward crossings of the carry section are the
path's forward carry steps** `N − 1 → 0`. -/
theorem forwardCrossings_liftWord {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) :
    forwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) = forwardCarries γ := by
  rw [liftWord, forwardCrossings_flatten, forwardCarries, card_filter]
  exact sum_congr rfl fun i _ => forwardCrossings_stepWord (cell_lift hγ i.castSucc) (hγ i)

/-- [proved-derived; formal-checked] **The lift's backward crossings of the carry section are the
path's backward carry steps** `0 → N − 1`. -/
theorem backwardCrossings_liftWord {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) :
    backwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) = backwardCarries γ := by
  rw [liftWord, backwardCrossings_flatten, backwardCarries, card_filter]
  exact sum_congr rfl fun i _ => backwardCrossings_stepWord (cell_lift hγ i.castSucc) (hγ i)

/-- [proved-derived; formal-checked] **The signed carry count is the lift's winding**: forward
minus backward carry steps of a ring path is `⌊lift γ n / N⌋`, the whole windings of its lift. -/
theorem carryCount_eq_winding {γ : Fin (n + 1) → Fin (M + 3)} (hγ : RingPath γ) :
    carryCount γ = lift γ (Fin.last n) / ((M + 3 : ℕ) : ℤ) := by
  have h := signed_count_is_flux (0 : Fin 1) (d := M + 3) (by omega) (liftAeon γ)
  have h0 : lift γ 0 / ((M + 3 : ℕ) : ℤ) = 0 := by
    rw [lift_zero]
    exact Int.ediv_eq_zero_of_lt (by omega) (by have := (γ 0).isLt; omega)
  change ((forwardCrossings _ (liftWord γ) : ℕ) : ℤ) - (backwardCrossings _ (liftWord γ) : ℕ) =
    lift γ (Fin.last n) / _ - lift γ 0 / _ at h
  rw [forwardCrossings_liftWord hγ, backwardCrossings_liftWord hγ, h0, sub_zero] at h
  exact h

/-- [proved-derived; formal-checked] **The path log ratio read by the carry steps**: for a positive
path of a ring chain, `log(P_γ / P_(Rγ))` is the state term plus the change of the entropy
coordinate plus the turn times the signed carry count. -/
theorem pathLogRatio_eq_carry_reading {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hA : Admissible π P) (hnn : RingNeighbour P) {γ : Fin (n + 1) → Fin (M + 3)}
    (hpos : 0 < pathLaw π P n γ) :
    Real.log (pathLaw π P n γ / revLaw π P n γ) =
      (Real.log (π (γ 0)) - Real.log (π (γ (Fin.last n)))) +
        ((coordinate (liftAffinity P) (γ (Fin.last n)) - coordinate (liftAffinity P) (γ 0)) +
          turn (M + 3) (liftAffinity P) * (carryCount γ : ℝ)) := by
  have hγ := ringPath_of_pathLaw_ne_zero hnn hpos.ne'
  rw [pathLogRatio_eq_entropy_reading hA hnn hpos, forwardCrossings_liftWord hγ,
    backwardCrossings_liftWord hγ, carryCount]

end Crossings

/-! ## 6. The mean signed crossing is the current -/

section Mean

/-- [proved-standard; formal-checked] **The step is a marginal**: under a stationary law of a
stochastic chain, the pair `(γ i, γ (i+1))` of every step of a path has the flow law
`π x · P(x, y)`. -/
theorem pair_marginal {S : Type*} [Fintype S] {K : Type*} [Field K] {π : S → K} {P : S → S → K}
    (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (g : S → S → K) :
    ∀ (n : ℕ) (i : Fin n), ∑ γ : Fin (n + 1) → S, pathLaw π P n γ * g (γ i.castSucc) (γ i.succ) =
      ∑ x, ∑ y, flow π P x y * g x y
  | 0, i => i.elim0
  | n + 1, i => by
    rw [sum_snoc]
    cases i using Fin.lastCases with
    | last =>
      have hstep : ∀ γ : Fin (n + 1) → S,
          ∑ y, pathLaw π P (n + 1) (Fin.snoc γ y) *
            g ((Fin.snoc γ y : Fin (n + 2) → S) (Fin.last n).castSucc)
              ((Fin.snoc γ y : Fin (n + 2) → S) (Fin.last n).succ) =
          pathLaw π P n γ * (fun x => ∑ y, P x y * g x y) (γ (Fin.last n)) := by
        intro γ
        simp only [pathLaw_snoc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last, mul_sum]
        exact sum_congr rfl fun y _ => by ring
      rw [sum_congr rfl fun γ _ => hstep γ, last_marginal hπ n (fun x => ∑ y, P x y * g x y)]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum]
      exact sum_congr rfl fun y _ => by unfold flow; ring
    | cast j =>
      have hstep : ∀ γ : Fin (n + 1) → S,
          ∑ y, pathLaw π P (n + 1) (Fin.snoc γ y) *
            g ((Fin.snoc γ y : Fin (n + 2) → S) j.castSucc.castSucc)
              ((Fin.snoc γ y : Fin (n + 2) → S) j.castSucc.succ) =
          pathLaw π P n γ * g (γ j.castSucc) (γ j.succ) := by
        intro γ
        simp only [pathLaw_snoc, Fin.succ_castSucc, Fin.snoc_castSucc]
        rw [← sum_mul, ← mul_sum, hrow, mul_one]
      rw [sum_congr rfl fun γ _ => hstep γ]
      exact pair_marginal hπ hrow g n j

/-- [proved-standard; formal-checked] **A stationary path law sees every step with the flow law**:
the mean of an additive path functional `Σ_i f(γ i, γ (i+1))` over `n` steps is `n` times its mean
`Σ_(x,y) π x P(x,y) f(x,y)` over one step. -/
theorem mean_step_sum {S : Type*} [Fintype S] {K : Type*} [Field K] {π : S → K} {P : S → S → K}
    (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (f : S → S → K) (n : ℕ) :
    ∑ γ : Fin (n + 1) → S, pathLaw π P n γ * ∑ i : Fin n, f (γ i.castSucc) (γ i.succ) =
      n * ∑ x, ∑ y, flow π P x y * f x y := by
  rw [sum_congr rfl fun γ _ => mul_sum _ _ _, sum_comm,
    sum_congr rfl fun i _ => pair_marginal hπ hrow f n i, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]

variable {M n : ℕ}

/-- [proved-standard; formal-checked] A double sum of a two-point indicator reads its point. -/
theorem sum_sum_ite_ite {S : Type*} [Fintype S] [DecidableEq S] (g : S → S → ℝ) (a b : S) :
    ∑ x, ∑ y, (if x = a then if y = b then g x y else 0 else 0) = g a b := by
  rw [Fintype.sum_eq_single a fun x hx => by simp [hx], Fintype.sum_eq_single b fun y hy => by
    simp [hy]]
  simp

/-- [proved-derived; formal-checked] The signed carry count is a sum over the path's steps. -/
theorem carryCount_eq_sum (γ : Fin (n + 1) → Fin (M + 3)) :
    (carryCount γ : ℝ) = ∑ i : Fin n,
      ((if γ i.castSucc = Fin.last (M + 2) ∧ γ i.succ = 0 then 1 else 0) -
        (if γ i.castSucc = 0 ∧ γ i.succ = Fin.last (M + 2) then 1 else 0) : ℝ) := by
  rw [sum_sub_distrib, carryCount, forwardCarries, backwardCarries, card_filter, card_filter]
  push_cast
  rfl

/-- [proved-derived; formal-checked] **The mean signed carry count is the net current of the
carry junction**: under a stationary law, `E_π[forward − backward carry steps over n steps]` is
`n · ringNet π P (N − 1)`. -/
theorem mean_carryCount {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ * (carryCount γ : ℝ) =
      n * ringNet π P (Fin.last (M + 2)) := by
  simp_rw [carryCount_eq_sum]
  refine (mean_step_sum hπ hrow (fun x y => ((if x = Fin.last (M + 2) ∧ y = 0 then 1 else 0) -
    (if x = 0 ∧ y = Fin.last (M + 2) then 1 else 0) : ℝ)) n).trans ?_
  congr 1
  simp only [mul_sub, mul_ite, mul_one, mul_zero, sum_sub_distrib, ite_and]
  rw [sum_sum_ite_ite, sum_sum_ite_ite, ringNet, Fin.last_add_one]

/-- [proved-derived; formal-checked] **The mean signed crossing of the carry section is the
current**: on a stationary nearest-neighbour ring, `E_π[forward − backward carry steps over n
steps] = n · J`, with `J = ringNet π P 0` the one net current (`ChainAxes.ring_nets_eq`). -/
theorem mean_carryCount_eq_current {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hnn : RingNeighbour P) (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ * (carryCount γ : ℝ) = n * ringNet π P 0 := by
  rw [mean_carryCount hπ hrow, ring_nets_eq hnn hπ hrow]

/-- [proved-derived; formal-checked] **The same mean read on the lift**: the mean of forward minus
backward crossings of the carry section `sectionForm 0 N` by the lift words is `n · J`. -/
theorem mean_liftCrossings_eq_current {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hnn : RingNeighbour P) (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ *
      (((forwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) : ℤ) -
        backwardCrossings (sectionForm (0 : Fin 1) (M + 3)) (liftWord γ) : ℤ) : ℝ) =
      n * ringNet π P 0 := by
  rw [← mean_carryCount_eq_current hnn hπ hrow n]
  refine sum_congr rfl fun γ _ => ?_
  by_cases h : pathLaw π P n γ = 0
  · rw [h, zero_mul, zero_mul]
  · have hγ := ringPath_of_pathLaw_ne_zero hnn h
    rw [forwardCrossings_liftWord hγ, backwardCrossings_liftWord hγ, carryCount]

/-- [proved-derived; formal-checked] **The mean winding of the lift is the current**:
`E_π[⌊lift γ n / N⌋] = n · J`. -/
theorem mean_liftWinding_eq_current {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hnn : RingNeighbour P) (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ *
      ((lift γ (Fin.last n) / ((M + 3 : ℕ) : ℤ) : ℤ) : ℝ) = n * ringNet π P 0 := by
  rw [← mean_carryCount_eq_current hnn hπ hrow n]
  refine sum_congr rfl fun γ _ => ?_
  by_cases h : pathLaw π P n γ = 0
  · rw [h, zero_mul, zero_mul]
  · rw [carryCount_eq_winding (ringPath_of_pathLaw_ne_zero hnn h)]

end Mean

/-! ## 7. The carry term carries the production, and the orientation's sign -/

section Production

variable {M n : ℕ}

/-- [proved-derived; formal-checked] The lift's turn is the sum of the ring's junction affinities. -/
theorem turn_liftAffinity (P : Fin (M + 3) → Fin (M + 3) → ℝ) :
    turn (M + 3) (liftAffinity P) = ∑ i : Fin (M + 3), RealChart.affinity P i (i + 1) := by
  unfold turn coordinate liftAffinity
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun i _ => ?_
  rw [cell_add_one, cell_natCast]

/-- [proved-derived; formal-checked] **The helix's turn is the ring's cycle affinity**: on a ring
whose law and junction steps are positive, the carry `A` of the lift's helix is the cycle affinity
of `σ = J · A` (`ChainAxes.cycleAffinity_law_free`). -/
theorem turn_eq_cycleAffinity {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hπ : ∀ x, 0 < π x) (hf : ∀ x, 0 < P x (x + 1)) (hb : ∀ x, 0 < P (x + 1) x) :
    turn (M + 3) (liftAffinity P) =
      cycleAffinity (fun i => flow π P i (i + 1)) (fun i => flow π P (i + 1) i) := by
  rw [turn_liftAffinity]
  have h := cycleAffinity_law_free π (fun i => P i (i + 1)) (fun i => P (i + 1) i) hπ hf hb
  simp only [flow]
  rw [h]
  exact sum_congr rfl fun i _ => Real.log_div (hf i).ne' (hb i).ne'

/-- [proved-standard; formal-checked] A constant factor leaves a weighted sum. -/
theorem sum_mul_left_comm {α : Type*} [Fintype α] (w c : α → ℝ) (A : ℝ) :
    ∑ γ, w γ * (A * c γ) = A * ∑ γ, w γ * c γ := by
  rw [mul_sum]
  exact sum_congr rfl fun γ _ => by ring

/-- [proved-derived; formal-checked] **The carry term carries `n · σ`**: on a stationary positive
nearest-neighbour ring, the mean of the carry term `A · (signed carry count)` over `n` steps is `n`
times the ring's production `σ = J · A` (`ChainAxes.stationary_ringProduction_eq`). -/
theorem mean_carryTerm_eq_production {π : Fin (M + 3) → ℝ} {P : Fin (M + 3) → Fin (M + 3) → ℝ}
    (hnn : RingNeighbour P) (hπ : Kac.Stationary P π) (hrow : ∀ x, ∑ y, P x y = 1)
    (hpos : ∀ x, 0 < π x) (hf : ∀ x, 0 < P x (x + 1)) (hb : ∀ x, 0 < P (x + 1) x) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ *
        (turn (M + 3) (liftAffinity P) * (carryCount γ : ℝ)) =
      n * ringProduction (fun i => flow π P i (i + 1)) (fun i => flow π P (i + 1) i) := by
  rw [stationary_ringProduction_eq hnn hπ hrow, ← turn_eq_cycleAffinity hpos hf hb,
    sum_mul_left_comm, mean_carryCount_eq_current hnn hπ hrow]
  ring

/-- [proved-standard; formal-checked] `Fin.rev x` is the last cell if and only if `x = 0`. -/
theorem rev_eq_last_iff (x : Fin (M + 3)) : Fin.rev x = Fin.last (M + 2) ↔ x = 0 := by
  rw [← (Fin.rev_zero (M + 2) : Fin.rev (0 : Fin (M + 3)) = Fin.last (M + 2)), Fin.rev_inj]

/-- [proved-standard; formal-checked] `Fin.rev x = 0` if and only if `x` is the last cell. -/
theorem rev_eq_zero_iff (x : Fin (M + 3)) : Fin.rev x = 0 ↔ x = Fin.last (M + 2) := by
  rw [← (Fin.rev_last (M + 2) : Fin.rev (Fin.last (M + 2)) = (0 : Fin (M + 3))), Fin.rev_inj]

/-- [proved-derived; formal-checked] **Reversing the orientation negates the signed carry count**:
relabelling the cells by `Fin.rev` exchanges forward and backward carry steps. -/
theorem carryCount_rev (γ : Fin (n + 1) → Fin (M + 3)) :
    carryCount (fun i => Fin.rev (γ i)) = -carryCount γ := by
  have hf : forwardCarries (fun i => Fin.rev (γ i)) = backwardCarries γ := by
    unfold forwardCarries backwardCarries
    simp only [rev_eq_last_iff, rev_eq_zero_iff]
  have hb : backwardCarries (fun i => Fin.rev (γ i)) = forwardCarries γ := by
    unfold forwardCarries backwardCarries
    simp only [rev_eq_last_iff, rev_eq_zero_iff]
  rw [carryCount, carryCount, hf, hb]
  ring

/-- [proved-derived; formal-checked] **Reversing the orientation negates the mean signed carry
count** (the path-law form of `ChainAxes.ring_reversal`): the chain relabelled by `Fin.rev` reads
the opposite mean, for every law. -/
theorem mean_carryCount_reflect (π : Fin (M + 3) → ℝ) (P : Fin (M + 3) → Fin (M + 3) → ℝ)
    (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3),
        pathLaw (fun x => π (Fin.rev x)) (fun x y => P (Fin.rev x) (Fin.rev y)) n γ *
          (carryCount γ : ℝ) =
      -∑ γ : Fin (n + 1) → Fin (M + 3), pathLaw π P n γ * (carryCount γ : ℝ) := by
  rw [← sum_neg_distrib]
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ => Fin.revPerm) _ _ fun γ => ?_).symm
  show -(pathLaw π P n γ * (carryCount γ : ℝ)) =
    pathLaw (fun x => π (Fin.rev x)) (fun x y => P (Fin.rev x) (Fin.rev y)) n
      (fun i => Fin.rev (γ i)) * (carryCount (fun i => Fin.rev (γ i)) : ℝ)
  rw [carryCount_rev]
  simp only [pathLaw, Fin.rev_rev]
  push_cast
  ring

/-- [proved-derived; formal-checked] **On a stationary ring, the reflected chain's mean signed
carry count is `−n · J`.** -/
theorem mean_carryCount_reflect_eq_current {π : Fin (M + 3) → ℝ}
    {P : Fin (M + 3) → Fin (M + 3) → ℝ} (hnn : RingNeighbour P) (hπ : Kac.Stationary P π)
    (hrow : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∑ γ : Fin (n + 1) → Fin (M + 3),
        pathLaw (fun x => π (Fin.rev x)) (fun x y => P (Fin.rev x) (Fin.rev y)) n γ *
          (carryCount γ : ℝ) =
      -(n * ringNet π P 0) := by
  rw [mean_carryCount_reflect, mean_carryCount_eq_current hnn hπ hrow]

end Production

/-! ## 8. A witness: the biased rotation of three cells -/

section Witness

/-- [proved-derived; formal-checked] The biased rotation is a nearest-neighbour ring. -/
theorem rotation_ringNeighbour : RingNeighbour (M := 0) (chainR Rotation.P) := by
  have h : ∀ x y : Fin 3, y = x ∨ y = x + 1 ∨ x = y + 1 := by decide
  exact fun x y _ => h x y

/-- [proved-derived; formal-checked] **The biased rotation carries the current `J = 1/9`**. -/
theorem rotation_current : ringNet (M := 0) (lawR Rotation.π) (chainR Rotation.P) 0 = 1 / 9 := by
  simp only [ringNet, flow, lawR, chainR, Rotation.P, Rotation.π]
  norm_num

/-- [proved-derived; formal-checked] **The witness**: under the uniform law, the biased rotation's
mean signed crossing of the carry section over two steps is `2/9 = 2 · J`, nonzero. -/
theorem rotation_mean_carryCount :
    ∑ γ : Fin 3 → Fin 3,
        pathLaw (lawR Rotation.π) (chainR Rotation.P) 2 γ * (carryCount γ : ℝ) = 2 / 9 := by
  rw [mean_carryCount_eq_current rotation_ringNeighbour (stationary_cast Rotation.stationary)
    (rows_cast Rotation.rows), rotation_current]
  norm_num

/-- [proved-derived; formal-checked] **The witness's carry term carries its production**: the mean
carry term `A · (signed carry count)` over two steps is `(2/3) log 2`, the rotation's production
over two epochs (`PathReversal.Rotation.rotation_production_pos`), with `A = 3 log 2`. -/
theorem rotation_mean_carryTerm :
    ∑ γ : Fin 3 → Fin 3, pathLaw (lawR Rotation.π) (chainR Rotation.P) 2 γ *
        (turn 3 (liftAffinity (chainR Rotation.P)) * (carryCount γ : ℝ)) =
      production Rotation.π Rotation.P 2 := by
  have hturn : turn 3 (liftAffinity (chainR Rotation.P)) = 3 * Real.log 2 := by
    rw [turn_liftAffinity, Fin.sum_univ_three]
    exact Rotation.rotation_cycle_affinity
  rw [sum_mul_left_comm, rotation_mean_carryCount, hturn, Rotation.rotation_production_pos.2.2.2 2]
  push_cast
  ring

end Witness

end Holonics.Physics.Thermal.ChainPathJoin

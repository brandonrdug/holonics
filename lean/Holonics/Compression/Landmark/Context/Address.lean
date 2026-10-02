import Holonics.Compression.Landmark.Context.Tree
import Holonics.HNN.Contact
import Holonics.Aeon.Clock.Lock
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Compression.Landmark.Context.Address: the receiving letters, typed bundles of the earlier ticks

[definition; agent-inferred] Campaign 2 of rebuild step 4 (`docs/plans/THE_REBUILD.md`, Lean item
13 of table (b); #73), from Sol's review of the campaign (§2). The computational object is the
helical pair interaction; this owner is the address of the receiving parametron's storage, the
tree of landmarks (`Compression/Landmark/Context/Tree`). Each earlier cell's tick contributes one **typed bundle**:
its cell and the declared features read at that tick (a ring's phase class, a contact's lock
address and site kind). Of the winding guide's six general objects it touches the **tower thread**
(the address restricts by dropping its oldest whole bundle; a coarser grain is a restriction of the
features), **faces and placement** (the finite partitions a letter is read on), the **pair** (a
contact's lock address, `Aeon/Clock/Lock`) and the **helix** (a ring's phase class is the phase of
a circle-plus-carry at its grain). No holonomy is claimed.

```text
state       σ_(c::h) = step σ_h c                     the retained clock state after a past h (newest first)
bundle      b(c :: h) = (c, read σ_(c::h))            a tick's cell and its features, read after the tick
address     a_D(h) = [b(h), b(tail h), …]_D            newest bundle first, boundary before the passage
window      a_D(w ++ h) = (bundles of w from σ_h ++ a_D(h)).take D     phase j reads w = its known targets
restriction a_d(h) = a_D(h).take d ;  flat(a_d) = flat(a_D).take (d (1 + r))
phase class ⌊g · fract x⌋ ∈ [0, g) ;  at x = k/d, g = d: k mod d ;  g' ∣ g: ⌊g' y⌋ = ⌊g y⌋ / (g/g')
lock        Unlocked, or reduced (p, q), 0 < p ≤ P, 0 < q ≤ Q ;  Q = the horizon H: a first return by H iff q ≤ H
code        0 (boundary) ,  1 + x + |A| · f  (injective) ;  f = Σ v_i Π_(k<i) s_k  (mixed radix, injective)
dominance   W_enlarged = ½ W_cells + ½ W_bundles  (the join's sequential mixture)
            −log₂ ∏ q_join ≤ −log₂ prior_w(S) + 1 − log₂ ∏_(leaves of S) E  per dyadic cell (Γ(S) at w = ½)
            L ≤ L_c + |H| + ρ + ρ_c  over the passage's opened dyadic cells H
```

[proved-derived; formal-checked] What is proved.

1. **`bundle_causal`.** The address shifts by one bundle a tick, the tick's bundle read after its
   step and never again (`address_succ_cons`); a window's phase address, at the history `w ++ h`
   of its known targets `w` after the cut `h`, is the window's bundles read from the retained state
   at the cut followed by the cut's address, truncated (`address_append`): it is a function of the
   pair the pending ratio copies at its cut (the retained clock state and the address), and of the
   known targets only, never of the cell it predicts.
2. **`bundle_restrict`.** Restricting the address at `D` to `d ≤ D` is the address at `d`; the next
   depth appends one whole bundle; and the flattened bundle word (each bundle `k` letters)
   restricted to `d k` letters is the flattened restricted address.
3. **`feature_scale_square`.** When a state restriction `π` commutes with the transport
   (`π (step σ c) = step' (π σ) c`) and the feature extraction commutes with it
   (`read' (π σ) = ρ (read σ)`), the coarse address is the fine one's features mapped by `ρ`, and
   the mapping commutes with the depth restriction: a scale square. The phase-class instance: a
   grain `g'` dividing `g` reads `⌊g' y⌋ = ⌊g y⌋ / (g/g')` (`phaseClass_coarsen`), and at an exact
   phase `k/d` any grain reads `⌊g' k/d⌋` (`phaseClass_of_exact`).
4. **`address_descends_retention`.** If a retention map identifies states the transport and the
   feature reading cannot separate (`ret σ = ret σ' → ret (step σ c) = ret (step σ' c)` and
   `ret σ = ret σ' → read σ = read σ'`), every future window's bundles are a function of the
   retained quotient: the letters keep no past.
5. **`phase_partition_finite`.** At a grain `g > 0` the phase class lies in `[0, g)`, its fibre is
   the interval `[k/g, (k+1)/g)` of the open phase, every class is read, and the ring's exact
   phase `j/d` at its own grain `d` reads `j mod d` (an empty fibre).
6. **`lock_partition_finite`.** The lock letters at bounds `(P, Q)` (`Unlocked` and the reduced
   `(p, q)`, `0 < p ≤ P`, `0 < q ≤ Q`: the addresses a contact reads in its declared orientation,
   a box and not the Farey family of `[0, 1]`) are finite, at most `(P + 1)(Q + 1) + 1`; a positive
   rate of reduced numerator at most `P` and denominator at most `Q` has exactly one address; and
   for a reduced rate the first return of the two clocks falls within a horizon `H` exactly when
   `q ≤ H`, so `Q = H` is the greatest denominator whose first return is observable before it. The
   contact's own law (`HNN/Contact.contact_lock_address`: the least-denominator rate of the
   measured fibre, closing at its `q`, in the box `p ≤ m_g`, `q ≤ m_h`) lands in this family
   whenever the windings are read up to the horizon: the contact's lock address and this
   partition are one object, the reading and the finite family it lands in.
7. **`bundle_code_injective`.** The bundle code (`0` the boundary, `1 + x + n f` a cell `x < n` with
   feature code `f`) is injective when the feature code is; the features' mixed-radix code is
   injective on values within their slots and lies below the slots' product.
8. **`cell_only_dominance_with_feature_charge`.** At a dyadic cell the enlarged tree joins the cell
   branch's faces `a_t` and the bundle branch's `b_t` by the sequential mixture
   (`Tree.sequential_mixture`); when the cell branch's product is its tree weight under the
   declared stop-weight law `w` (Decision 32; `Tree.stop_weight_step`), the join codes within
   one bit of the cell tree, and for every cell-only pruned tree `S` within `−log₂ prior_w(S) + 1` of
   its leaves' code (`Tree.stop_kraft_and_dominance`; `Γ(S) + 1` at `w = ½`). Over the passage (`passage_join_bound`) the enlarged tree
   pays at most one bit a dyadic cell opened: `−log₂ ∏_h ∏_t q_(h,t) ≤ Σ_h −log₂ W_h + |H|`
   (`|H| ≤ 2^B − 1`, the splitting dyadic cells, `255` at `|A| = 256`); an executed enlarged code
   within its certified drift `ρ` of the ideal join, against an executed cell-only code within `ρ_c`
   of the cell tree, satisfies `L ≤ L_c + |H| + ρ + ρ_c`, the bound the development harness checks.

[conditional] The ideal join's weight is `½ W_cells + ½ W_bundles`; a tighter charge needs a prior
reserving more weight for the cell branch.

[open] The lock letter's reading (the contact's measured winding pair and the address selected
from it) is the contact owner's (`HNN/Contact.contact_lock_address`), consumed here as the finite
partition it lands in. The executed rank of a reduced pair in Rust
(`hnn::contact::ContactLock::code`, ordered by `(q, p)`) is checked by the tests, not stated here.

The Rust consumers are `crates/holonics/src/compression/landmark/context.rs` (`Letter`, `Bundle`, `LetterFamily`,
`Feature`, `letter_address`, the join of the enlarged tree), `crates/holonics/src/hnn/contact.rs`
(`LockDeclaration::letters`, `ContactLock::code`, `ContactReading::letter`: the contact letter's
partition and rank) and `crates/holonics/src/hnn/receiving.rs` (`LetterReader`, `ActiveAddress`,
`clock_letters`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Address

open Holonics.Compression.Landmark.Context.Tree (restrict PrunedTree StopLaw stopWeight treeLik TreeStanding
  stop_kraft_and_dominance seqLik seqMix sequential_mixture_bounds)

/-! ## 1. Bundles and the address -/

section Address

variable {A F S : Type*}

/-- [definition] **A typed bundle**: the boundary before the passage, or a tick's cell with its
features read after the tick. -/
inductive Bundle (A F : Type*)
  | boundary : Bundle A F
  | tick (cell : A) (features : F) : Bundle A F
deriving DecidableEq

/-- [definition] **The retained state after a past** (newest cell first). -/
def stateAfter (step : S → A → S) (σ₀ : S) : List A → S
  | [] => σ₀
  | c :: h => step (stateAfter step σ₀ h) c

/-- [definition] **The state reached from `σ` over a window** (newest cell first). -/
def runFrom (step : S → A → S) (σ : S) : List A → S
  | [] => σ
  | c :: w => step (runFrom step σ w) c

/-- [definition] **A window's bundles** (newest first), each read after its tick from the state at
the window's opening. -/
def windowBundles (step : S → A → S) (read : S → F) (σ : S) : List A → List (Bundle A F)
  | [] => []
  | c :: w => Bundle.tick c (read (runFrom step σ (c :: w))) :: windowBundles step read σ w

/-- [definition] **The address of depth `D` at a past `h`**: its `D` newest bundles, newest first,
the boundary past the passage's first cell. -/
def address (step : S → A → S) (read : S → F) (σ₀ : S) : ℕ → List A → List (Bundle A F)
  | 0, _ => []
  | D + 1, [] => Bundle.boundary :: address step read σ₀ D []
  | D + 1, c :: h => Bundle.tick c (read (stateAfter step σ₀ (c :: h))) :: address step read σ₀ D h

theorem stateAfter_append (step : S → A → S) (σ₀ : S) (w h : List A) :
    stateAfter step σ₀ (w ++ h) = runFrom step (stateAfter step σ₀ h) w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [stateAfter, runFrom, ih]

theorem address_length (step : S → A → S) (read : S → F) (σ₀ : S) :
    ∀ D h, (address step read σ₀ D h).length = D
  | 0, _ => rfl
  | D + 1, [] => by simp [address, address_length step read σ₀ D []]
  | D + 1, _ :: h => by simp [address, address_length step read σ₀ D h]

/-- The address of the passage's opening is the boundary alone. -/
theorem address_nil (step : S → A → S) (read : S → F) (σ₀ : S) :
    ∀ D, address step read σ₀ D [] = List.replicate D Bundle.boundary
  | 0 => rfl
  | D + 1 => by simp [address, address_nil step read σ₀ D, List.replicate_succ]

/-- One tick shifts the address by its bundle. -/
theorem address_succ_cons (step : S → A → S) (read : S → F) (σ₀ : S) (D : ℕ) (c : A)
    (h : List A) :
    address step read σ₀ (D + 1) (c :: h) =
      Bundle.tick c (read (step (stateAfter step σ₀ h) c)) :: address step read σ₀ D h := rfl

/-- Restricting the address to a shallower depth is the shallower address. -/
theorem address_take (step : S → A → S) (read : S → F) (σ₀ : S) :
    ∀ d D h, d ≤ D → (address step read σ₀ D h).take d = address step read σ₀ d h
  | 0, _, _, _ => by simp [address]
  | d + 1, D + 1, [], hd => by
    simp only [address, List.take_succ_cons]
    exact congrArg _ (address_take step read σ₀ d D [] (by omega))
  | d + 1, D + 1, c :: h, hd => by
    simp only [address, List.take_succ_cons]
    exact congrArg _ (address_take step read σ₀ d D h (by omega))
  | _ + 1, 0, _, hd => by omega

/-- The next depth appends one older bundle. -/
theorem address_succ_snoc (step : S → A → S) (read : S → F) (σ₀ : S) :
    ∀ D h, ∃ b, address step read σ₀ (D + 1) h = address step read σ₀ D h ++ [b]
  | 0, [] => ⟨Bundle.boundary, rfl⟩
  | 0, c :: h => ⟨_, rfl⟩
  | D + 1, [] => by
    obtain ⟨b, hb⟩ := address_succ_snoc step read σ₀ D []
    refine ⟨b, ?_⟩
    show Bundle.boundary :: address step read σ₀ (D + 1) [] =
      (Bundle.boundary :: address step read σ₀ D []) ++ [b]
    rw [hb]
    rfl
  | D + 1, c :: h => by
    obtain ⟨b, hb⟩ := address_succ_snoc step read σ₀ D h
    refine ⟨b, ?_⟩
    show Bundle.tick c (read (stateAfter step σ₀ (c :: h))) :: address step read σ₀ (D + 1) h =
      (Bundle.tick c (read (stateAfter step σ₀ (c :: h))) :: address step read σ₀ D h) ++ [b]
    rw [hb]
    rfl

/-- A word of `k`-letter pieces restricted to `d k` letters is its first `d` pieces. -/
theorem take_flatMap_uniform {B L : Type*} (flat : B → List L) (k : ℕ)
    (hk : ∀ b, (flat b).length = k) :
    ∀ (l : List B) (d : ℕ), (l.flatMap flat).take (d * k) = (l.take d).flatMap flat
  | [], d => by simp
  | b :: l, 0 => by simp
  | b :: l, d + 1 => by
    rw [List.flatMap_cons, List.take_succ_cons, List.flatMap_cons,
      show (d + 1) * k = (flat b).length + d * k by rw [hk]; ring,
      List.take_length_add_append, take_flatMap_uniform flat k hk l d]

/-- The address at a longer history is the window's bundles, then the cut's address, truncated. -/
theorem address_append (step : S → A → S) (read : S → F) (σ₀ : S) :
    ∀ (w h : List A) (D : ℕ),
      address step read σ₀ D (w ++ h) =
        (windowBundles step read (stateAfter step σ₀ h) w ++ address step read σ₀ D h).take D
  | [], h, D => by
    simp [windowBundles, List.take_of_length_le (le_of_eq (address_length step read σ₀ D h))]
  | c :: w, h, 0 => rfl
  | c :: w, h, D + 1 => by
    have ih := address_append step read σ₀ w h D
    have hstate : stateAfter step σ₀ (c :: (w ++ h)) =
        runFrom step (stateAfter step σ₀ h) (c :: w) := stateAfter_append step σ₀ (c :: w) h
    have htail : (windowBundles step read (stateAfter step σ₀ h) w ++
          address step read σ₀ D h).take D =
        (windowBundles step read (stateAfter step σ₀ h) w ++
          address step read σ₀ (D + 1) h).take D := by
      rw [List.take_append, List.take_append,
        address_take step read σ₀ _ D h (by omega),
        address_take step read σ₀ _ (D + 1) h (by omega)]
    rw [List.cons_append, address, hstate, ih, htail]
    rfl

/-- [proved-derived; formal-checked] **`bundle_causal`: a letter is read from the retained state
before the cell it predicts.**
* One tick shifts the address by exactly its bundle, read after its step; the earlier bundles are
  unchanged: a bundle is never read again.
* A window's phase address at the history `w ++ h` (its known targets `w`, newest first, after
  the cut `h`) is the window's bundles read from the retained state at the cut followed by the
  cut's address, truncated to `D`. It is a function of that pair, which the pending ratio copies at
  its cut, and of the known targets; the predicted cell is not among its arguments.
* Two pasts that agree on the retained state and on the address at the cut agree on every phase
  address of every window after it. -/
theorem bundle_causal (step : S → A → S) (read : S → F) (σ₀ : S) (D : ℕ) :
    (∀ c h, address step read σ₀ (D + 1) (c :: h) =
      Bundle.tick c (read (step (stateAfter step σ₀ h) c)) :: address step read σ₀ D h) ∧
      (∀ w h, address step read σ₀ D (w ++ h) =
        (windowBundles step read (stateAfter step σ₀ h) w ++ address step read σ₀ D h).take D) ∧
      ∀ h h', stateAfter step σ₀ h = stateAfter step σ₀ h' →
        address step read σ₀ D h = address step read σ₀ D h' →
        ∀ w, address step read σ₀ D (w ++ h) = address step read σ₀ D (w ++ h') := by
  refine ⟨fun c h => rfl, fun w h => address_append step read σ₀ w h D,
    fun h h' hs ha w => ?_⟩
  rw [address_append, address_append, hs, ha]

/-- [proved-derived; formal-checked] **`bundle_restrict`: the address restricts by whole bundles.**
* Restricting the address at `D` to `d ≤ D` (`Tree.restrict`, a `take`) is the address at
  `d`: restriction drops the oldest whole bundles.
* The address at `D + 1` is the address at `D` with one older bundle appended.
* When every bundle flattens to `k` letters (its cell, then its `k − 1` feature letters), the
  flattened address restricted to `d k` letters is the flattened address at `d`: the bundle tree's
  node at `d k` letters is the address restricted to `d` bundles. -/
theorem bundle_restrict (step : S → A → S) (read : S → F) (σ₀ : S) :
    (∀ d D h, d ≤ D → restrict d (address step read σ₀ D h) = address step read σ₀ d h) ∧
      (∀ D h, ∃ b, address step read σ₀ (D + 1) h = address step read σ₀ D h ++ [b]) ∧
      ∀ {L : Type*} (flat : Bundle A F → List L) (k : ℕ), (∀ b, (flat b).length = k) →
        ∀ d D h, d ≤ D →
          ((address step read σ₀ D h).flatMap flat).take (d * k) =
            (address step read σ₀ d h).flatMap flat :=
  ⟨address_take step read σ₀, address_succ_snoc step read σ₀,
    fun flat k hk d D h hd => by
      rw [take_flatMap_uniform flat k hk, address_take step read σ₀ d D h hd]⟩

/-- [definition] **A bundle's features mapped** by a coarsening `ρ`. -/
def Bundle.map {F' : Type*} (ρ : F → F') : Bundle A F → Bundle A F'
  | .boundary => .boundary
  | .tick c f => .tick c (ρ f)

/-- [proved-derived; formal-checked] **`feature_scale_square`, with its commutation hypothesis.**
When a restriction `π` of the retained state commutes with the transport
(`π (step σ c) = step' (π σ) c`, `π σ₀ = σ₀'`) and the feature extraction commutes with it
(`read' (π σ) = ρ (read σ)`), then:
* the coarse address is the fine address with its features mapped by `ρ`;
* mapping commutes with the depth restriction, so the depth restriction and the feature
  coarsening form a square: either order meets at the coarse address of depth `d`.
Without the commutation hypothesis a coarse letter can depend on what the coarse state forgot, and
no square is claimed. -/
theorem feature_scale_square {S' F' : Type*} (step : S → A → S) (read : S → F) (σ₀ : S)
    (step' : S' → A → S') (read' : S' → F') (σ₀' : S') (π : S → S') (ρ : F → F')
    (hσ : π σ₀ = σ₀') (hstep : ∀ σ c, π (step σ c) = step' (π σ) c)
    (hread : ∀ σ, read' (π σ) = ρ (read σ)) :
    (∀ D h, address step' read' σ₀' D h = (address step read σ₀ D h).map (Bundle.map ρ)) ∧
      ∀ d D h, d ≤ D →
        restrict d ((address step read σ₀ D h).map (Bundle.map ρ)) =
          (restrict d (address step read σ₀ D h)).map (Bundle.map ρ) ∧
        restrict d (address step' read' σ₀' D h) = address step' read' σ₀' d h := by
  have hstate : ∀ h, π (stateAfter step σ₀ h) = stateAfter step' σ₀' h := by
    intro h
    induction h with
    | nil => exact hσ
    | cons c h ih => simp [stateAfter, hstep, ih]
  have hmap : ∀ D h, address step' read' σ₀' D h =
      (address step read σ₀ D h).map (Bundle.map ρ) := by
    intro D
    induction D with
    | zero => intro h; rfl
    | succ D ih =>
      intro h
      cases h with
      | nil => simp [address, ih, Bundle.map]
      | cons c h =>
        simp only [address, List.map_cons, Bundle.map, ih]
        rw [← hread, hstate]
  exact ⟨hmap, fun d D h hd => ⟨by simp [restrict, List.map_take],
    address_take step' read' σ₀' d D h hd⟩⟩

/-- [proved-derived; formal-checked] **`address_descends_retention`.** If a retention map
identifies only states that the transport and the feature reading cannot separate, every future
window's bundles are a function of the retained quotient: two states with one retention read the
same bundles over every window. The letters are read from the retained sufficient state and keep
no past. -/
theorem address_descends_retention {R : Type*} (step : S → A → S) (read : S → F) (ret : S → R)
    (hstep : ∀ σ σ' c, ret σ = ret σ' → ret (step σ c) = ret (step σ' c))
    (hread : ∀ σ σ', ret σ = ret σ' → read σ = read σ') :
    ∀ σ σ', ret σ = ret σ' → ∀ w, windowBundles step read σ w = windowBundles step read σ' w ∧
      ret (runFrom step σ w) = ret (runFrom step σ' w) := by
  intro σ σ' h w
  induction w with
  | nil => exact ⟨rfl, h⟩
  | cons c w ih =>
    have hr : ret (runFrom step σ (c :: w)) = ret (runFrom step σ' (c :: w)) :=
      hstep _ _ c ih.2
    refine ⟨?_, hr⟩
    simp only [windowBundles, ih.1, hread _ _ hr]

end Address

/-! ## 2. The finite partitions -/

section Partitions

/-- [definition] **The phase class at a grain `g`**: `⌊g · fract x⌋`, the open phase `fract x` of a
turn read at `g` classes. -/
def phaseClass (g : ℕ) (x : ℚ) : ℕ := ⌊(g : ℚ) * Int.fract x⌋₊

/-- [proved-derived; formal-checked] **`phase_partition_finite`.** At a grain `g > 0`:
* every phase class lies in `[0, g)`;
* the class `k` is read exactly on its fibre, `k/g ≤ fract x < (k + 1)/g`;
* every class `k < g` is read (at `x = k/g`);
* the ring's exact phase `j/d` at its own grain `d` reads `j mod d`: its fibre is empty. -/
theorem phase_partition_finite (g : ℕ) (hg : 0 < g) :
    (∀ x, phaseClass g x < g) ∧
      (∀ x k, phaseClass g x = k ↔ (k : ℚ) / g ≤ Int.fract x ∧ Int.fract x < (k + 1) / g) ∧
      (∀ k < g, phaseClass g ((k : ℚ) / g) = k) ∧
      ∀ j : ℕ, phaseClass g ((j : ℚ) / g) = j % g := by
  have hg' : (0 : ℚ) < g := by exact_mod_cast hg
  have hlt : ∀ x : ℚ, (g : ℚ) * Int.fract x < g := fun x => by
    have := Int.fract_lt_one x
    nlinarith
  have hnn : ∀ x : ℚ, 0 ≤ (g : ℚ) * Int.fract x := fun x =>
    mul_nonneg hg'.le (Int.fract_nonneg x)
  have hclass : ∀ j : ℕ, phaseClass g ((j : ℚ) / g) = j % g := by
    intro j
    have hj : (j : ℚ) = (g : ℚ) * ((j / g : ℕ) : ℚ) + ((j % g : ℕ) : ℚ) := by
      exact_mod_cast (Nat.div_add_mod j g).symm
    have hsplit : (j : ℚ) / g = ((j / g : ℕ) : ℚ) + ((j % g : ℕ) : ℚ) / g := by
      rw [hj]
      field_simp
    have hfract : Int.fract ((j : ℚ) / g) = ((j % g : ℕ) : ℚ) / g := by
      rw [Int.fract_eq_iff]
      refine ⟨by positivity, ?_, ⟨((j / g : ℕ) : ℤ), ?_⟩⟩
      · rw [div_lt_one hg']
        exact_mod_cast Nat.mod_lt j hg
      · rw [hsplit, Int.cast_natCast]
        ring
    unfold phaseClass
    rw [hfract, mul_div_cancel₀ _ hg'.ne', Nat.floor_natCast]
  refine ⟨fun x => ?_, fun x k => ?_, fun k hk => by rw [hclass, Nat.mod_eq_of_lt hk], hclass⟩
  · unfold phaseClass
    exact (Nat.floor_lt (hnn x)).mpr (by exact_mod_cast hlt x)
  · unfold phaseClass
    rw [Nat.floor_eq_iff (hnn x), div_le_iff₀ hg', lt_div_iff₀ hg', mul_comm (Int.fract x)]

/-- [proved-derived; formal-checked] **`phaseClass_coarsen`: a dividing grain is a restriction of
the finer class.** For `g = g' m` with `m > 0`, `⌊g' y⌋ = ⌊g y⌋ / m`: the coarse class is read from
the fine class alone (the commutation hypothesis of `feature_scale_square` for grains). -/
theorem phaseClass_coarsen (g' m : ℕ) (hm : 0 < m) (x : ℚ) :
    phaseClass g' x = phaseClass (g' * m) x / m := by
  unfold phaseClass
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Nat.floor_div_natCast]
  congr 1
  push_cast
  field_simp

/-- [proved-derived; formal-checked] **`phaseClass_of_exact`: at an exact phase every grain reads the
fine class.** For `k < d`, the phase `k/d` read at any grain `g'` is `⌊g' k / d⌋`, a function of the
class `k` read at the ring's own grain `d` (the half-turn sheet is `g' = 2`). -/
theorem phaseClass_of_exact (g' d k : ℕ) (hk : k < d) :
    phaseClass g' ((k : ℚ) / d) = g' * k / d := by
  have hd : (0 : ℚ) < d := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) hk)
  have hfract : Int.fract ((k : ℚ) / d) = (k : ℚ) / d := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, by rw [div_lt_one hd]; exact_mod_cast hk⟩
  unfold phaseClass
  rw [hfract, ← mul_div_assoc, ← Nat.cast_mul, Nat.floor_div_eq_div]

/-- [definition] **A reduced lock address within the bounds `(P, Q)`**: `(p, q)` with `0 < p ≤ P`,
`0 < q ≤ Q` and `gcd(p, q) = 1`, the addresses a contact `g → h` can read in its declared
orientation (`HNN/Contact.contact_lock_address`: `p` turns of ring `g` per `q` of ring `h`); a box,
not the Farey family of `[0, 1]`, since ring `g` may wind faster than ring `h`. -/
def LockPair (P Q : ℕ) : Type :=
  {pq : Fin (P + 1) × Fin (Q + 1) // 0 < pq.1.val ∧ 0 < pq.2.val ∧
    Nat.Coprime pq.1.val pq.2.val}

instance (P Q : ℕ) : Fintype (LockPair P Q) := by
  unfold LockPair; infer_instance

/-- [definition] **A lock letter**: `Unlocked` (`none`) at the declared tolerance, or a reduced
address within the bounds. -/
abbrev LockLetter (P Q : ℕ) := Option (LockPair P Q)

open Holonics.Aeon.Clock.Lock (IsCycle jointReading) in
/-- [proved-derived; formal-checked] **`lock_partition_finite`: the contact's lock letters are a
finite partition, and the bound is the horizon.**
* The lock letters at `(P, Q)` are finite: at most `(P + 1)(Q + 1) + 1` of them.
* A positive rate of reduced numerator at most `P` and reduced denominator at most `Q` has exactly
  one reduced address: the rates within the bounds are partitioned by their addresses.
* For a reduced rate `p/q` the two clocks' first return falls within a horizon of `H` turns of the
  second clock exactly when `q ≤ H`: the bound `Q = H` is the greatest denominator whose first
  return is observable before the admitted horizon. The cycles are the lock's own
  (`Aeon/Clock/Lock.cycle_iff_period_dvd`: exactly the multiples of `q`), the period at which the
  contact's address closes (`HNN/Contact.{contact_lock_address, lockAddress_closes}`); and since the
  address of windings `(m_g, m_h)` lies in the box `p ≤ m_g`, `q ≤ m_h`, windings counted up to the
  horizon's closing tick (`m_h ≤ H`) always land in the family. -/
theorem lock_partition_finite (P Q : ℕ) :
    Fintype.card (LockLetter P Q) ≤ (P + 1) * (Q + 1) + 1 ∧
      (∀ r : ℚ, 0 < r → r.num ≤ P → r.den ≤ Q →
        ∃! ℓ : LockPair P Q, ((ℓ.1.1.val : ℚ) / ℓ.1.2.val) = r) ∧
      ∀ (p : ℤ) (q H : ℕ), 0 < q → IsCoprime (q : ℤ) p →
        ((∃ k : ℤ, 0 < k ∧ k ≤ H ∧ IsCycle (jointReading ((p : ℚ) / q) k)) ↔ q ≤ H) := by
  refine ⟨?_, fun r hr0 hnumP hden => ?_, fun p q H hq hcop => ?_⟩
  · rw [Fintype.card_option]
    have : Fintype.card (LockPair P Q) ≤ (P + 1) * (Q + 1) := by
      unfold LockPair
      refine (Fintype.card_subtype_le _).trans ?_
      simp
    omega
  · have hnum : 0 < r.num := Rat.num_pos.mpr hr0
    have hcopr : Nat.Coprime r.num.toNat r.den := by
      have := r.reduced
      rwa [show r.num.natAbs = r.num.toNat by omega] at this
    refine ⟨⟨(⟨r.num.toNat, by omega⟩, ⟨r.den, by omega⟩), by simp only; omega, r.den_pos,
      hcopr⟩, ?_, ?_⟩
    · show ((r.num.toNat : ℕ) : ℚ) / (r.den : ℚ) = r
      rw [show ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg hnum.le]
      exact Rat.num_div_den r
    · rintro ⟨⟨p, q⟩, hp, hq, hc⟩ he
      have hq' : (0 : ℤ) < (q.val : ℤ) := by exact_mod_cast hq
      have hc' : Nat.Coprime (p.val : ℤ).natAbs (q.val : ℤ).natAbs := by simpa using hc
      have e : ((p.val : ℤ) : ℚ) / ((q.val : ℤ) : ℚ) = r := by simpa using he
      have hn := Rat.num_div_eq_of_coprime hq' hc'
      have hd := Rat.den_div_eq_of_coprime hq' hc'
      rw [e] at hn hd
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        simp only
        omega
      · apply Fin.ext
        simp only
        omega
  · have hcycles := Holonics.Aeon.Clock.Lock.cycle_iff_period_dvd p q hq hcop
    constructor
    · rintro ⟨k, hk0, hkH, hcyc⟩
      have := Int.le_of_dvd hk0 ((hcycles k).mp hcyc)
      omega
    · intro hqH
      exact ⟨q, by exact_mod_cast hq, by exact_mod_cast hqH, (hcycles q).mpr (dvd_refl _)⟩

/-- [definition] **The features' mixed-radix code**, least significant slot first:
`v₀ + s₀ (v₁ + s₁ (…))`. -/
def mixedCode : List ℕ → List ℕ → ℕ
  | v :: vs, s :: ss => v + s * mixedCode vs ss
  | _, _ => 0

/-- [definition] **Values within their slots**: equal lengths, each value below its slot's size. -/
def WithinSlots : List ℕ → List ℕ → Prop
  | [], [] => True
  | v :: vs, s :: ss => v < s ∧ WithinSlots vs ss
  | _, _ => False

theorem mixedCode_lt : ∀ vs ss, WithinSlots vs ss → mixedCode vs ss < ss.prod
  | [], [], _ => by simp [mixedCode]
  | v :: vs, s :: ss, ⟨hv, hw⟩ => by
    have ih := mixedCode_lt vs ss hw
    simp only [mixedCode, List.prod_cons]
    calc v + s * mixedCode vs ss < s + s * mixedCode vs ss := by omega
      _ = s * (mixedCode vs ss + 1) := by ring
      _ ≤ s * ss.prod := Nat.mul_le_mul_left s ih
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem mixedCode_injective : ∀ vs ws ss, WithinSlots vs ss → WithinSlots ws ss →
    mixedCode vs ss = mixedCode ws ss → vs = ws
  | [], [], [], _, _, _ => rfl
  | v :: vs, w :: ws, s :: ss, ⟨hv, hvs⟩, ⟨hw, hws⟩, h => by
    simp only [mixedCode] at h
    have hmod : v = w := by
      have := congrArg (· % s) h
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] using this
    have hs : 0 < s := lt_of_le_of_lt (Nat.zero_le v) hv
    have hdiv : mixedCode vs ss = mixedCode ws ss := by
      have := congrArg (· / s) h
      simpa [Nat.add_mul_div_left _ _ hs, Nat.div_eq_of_lt hv, Nat.div_eq_of_lt hw] using this
    rw [hmod, mixedCode_injective vs ws ss hvs hws hdiv]
  | [], [], _ :: _, h, _, _ => h.elim
  | [], _ :: _, [], _, h, _ => h.elim
  | [], _ :: _, _ :: _, h, _, _ => h.elim
  | _ :: _, [], [], h, _, _ => h.elim
  | _ :: _, [], _ :: _, _, h, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _ => h.elim

/-- [definition] **The bundle code**: `0` for the boundary, `1 + x + n f` for a cell `x < n` with
the features' code `f`. -/
def bundleCode {F : Type*} (n : ℕ) (enc : F → ℕ) : Bundle (Fin n) F → ℕ
  | .boundary => 0
  | .tick c f => 1 + c.val + n * enc f

/-- [proved-derived; formal-checked] **`bundle_code_injective`.**
* The bundle code is injective when the features' code is: the boundary is `0`, a cell `x < n` is
  read back as the code's residue `mod n` after the boundary's one, and the features as its
  quotient.
* The features' mixed-radix code is injective on values within their slots and lies below the
  slots' product, so a bundle code lies below `1 + n Π s_i`. -/
theorem bundle_code_injective {F : Type*} (n : ℕ) (enc : F → ℕ) (henc : Function.Injective enc) :
    Function.Injective (bundleCode n enc) ∧
      (∀ vs ws ss, WithinSlots vs ss → WithinSlots ws ss →
        mixedCode vs ss = mixedCode ws ss → vs = ws) ∧
      ∀ vs ss, WithinSlots vs ss → mixedCode vs ss < ss.prod := by
  refine ⟨?_, mixedCode_injective, mixedCode_lt⟩
  rintro (_ | ⟨c, f⟩) (_ | ⟨c', f'⟩) h
  · rfl
  · simp only [bundleCode] at h; omega
  · simp only [bundleCode] at h; omega
  · simp only [bundleCode] at h
    have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) c.isLt
    have h2 : c.val + n * enc f = c'.val + n * enc f' := by omega
    have hc : c.val = c'.val := by
      have := congrArg (· % n) h2
      simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.isLt, Nat.mod_eq_of_lt c'.isLt]
        using this
    have hf : enc f = enc f' := by
      have h3 : n * enc f = n * enc f' := by omega
      exact Nat.eq_of_mul_eq_mul_left hn h3
    rw [Fin.ext hc, henc hf]

end Partitions

/-! ## 3. The enlarged tree keeps the cell-only branch -/

section Dominance

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type*} [Fintype A] [DecidableEq A]

/-- [proved-derived; formal-checked] **`passage_join_bound`: one bit a dyadic cell over the
passage.** Over the dyadic cells `H` a passage opens, each joining its cell branch's faces `a_h`
(whose product over its routed digits is the cell-only tree's weight `W_h` there) with its bundle
branch's faces `b_h` by the sequential mixture, the enlarged tree codes within `|H|` bits of the
cell-only tree: `−log₂ ∏_h ∏_t q_(h,t) ≤ Σ_h −log₂ W_h + |H|`. -/
theorem passage_join_bound {ι : Type*} (H : Finset ι) {a b : ι → ℕ → ℚ} (n : ι → ℕ)
    (W : ι → ℚ) (ha : ∀ h t, 0 < a h t) (hb : ∀ h t, 0 < b h t)
    (hW : ∀ h ∈ H, seqLik (a h) (n h) = W h) :
    -Real.logb 2 ((∏ h ∈ H, ∏ t ∈ Finset.range (n h), seqMix (a h) (b h) t : ℚ) : ℝ) ≤
      ∑ h ∈ H, -Real.logb 2 (W h : ℝ) + H.card := by
  have hpos : ∀ h, (0 : ℝ) < ((∏ t ∈ Finset.range (n h), seqMix (a h) (b h) t : ℚ) : ℝ) := by
    intro h
    have lo := (sequential_mixture_bounds (ha h) (hb h) (n h)).1
    have hA := Holonics.Compression.Landmark.Context.Tree.seqLik_pos (ha h) (n h)
    have hmax : (0 : ℚ) < max (seqLik (a h) (n h)) (seqLik (b h) (n h)) / 2 :=
      half_pos (lt_of_lt_of_le hA (le_max_left _ _))
    exact_mod_cast lt_of_lt_of_le hmax lo
  rw [Rat.cast_prod, Real.logb_prod _ _ (fun h _ => (hpos h).ne'), ← Finset.sum_neg_distrib,
    show (H.card : ℝ) = ∑ _h ∈ H, (1 : ℝ) by simp, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun h hh => ?_
  have hbnd := (sequential_mixture_bounds (ha h) (hb h) (n h)).2.2.2
  have hm := min_le_left (-Real.logb 2 (seqLik (a h) (n h) : ℝ))
    (-Real.logb 2 (seqLik (b h) (n h) : ℝ))
  rw [hW h hh] at hm hbnd
  linarith

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cell_only_dominance_with_feature_charge`.** At one dyadic
cell, let `a_t` be the cell branch's faces of its routed digits and `b_t` the bundle branch's, joined
by the sequential mixture `q_t` (`Tree.seqMix`, the ratio stepped after every digit). When
the cell branch's faces multiply to its tree weight under the declared stop-weight law `w`,
`∏_(t<n) a_t = W_cells` (`Tree.stop_weight_step`'s telescope):
* the join codes within one bit of the cell tree: `−log₂ ∏ q ≤ −log₂ W_cells + 1`;
* for every cell-only pruned tree `S`, `−log₂ ∏ q ≤ (−log₂ prior_w(S) + 1) − log₂ ∏_(leaves of S) E`
  (`Tree.stop_kraft_and_dominance`): the embedded cell tree costs its own prior's code and
  the join's one bit; at `w = ½` the prior's code is `Γ(S)` (`PrunedTree.prior_half_bits`);
* **over the passage, at most one bit a dyadic cell opened** (`passage_join_bound`): for the
  dyadic cells `H` a passage opens, an executed enlarged code `L` within its certified drift `ρ`
  of the ideal join and an executed cell-only code `L_c` within `ρ_c` of the cell tree's ideal
  code satisfy `L ≤ L_c + |H| + ρ + ρ_c`. The features' description is charged beside it. -/
theorem cell_only_dominance_with_feature_charge [Nonempty A] {a b : ℕ → ℚ}
    (ha : ∀ t, 0 < a t) (hb : ∀ t, 0 < b t) {w : ℕ → ℚ} (hw : StopLaw w)
    (N : TreeStanding Ltr A) (m : ℕ) (s : List Ltr)
    (n : ℕ) (hcell : seqLik a n = stopWeight w N m s) :
    -Real.logb 2 ((∏ t ∈ Finset.range n, seqMix a b t : ℚ) : ℝ) ≤
        -Real.logb 2 (stopWeight w N m s : ℝ) + 1 ∧
      (∀ S : PrunedTree Ltr m,
        -Real.logb 2 ((∏ t ∈ Finset.range n, seqMix a b t : ℚ) : ℝ) ≤
          (-Real.logb 2 (PrunedTree.prior w m s.length S : ℝ) + 1) -
            Real.logb 2 (treeLik N m s S : ℝ)) ∧
      ∀ {ι : Type} (H : Finset ι) (a' b' : ι → ℕ → ℚ) (n' : ι → ℕ) (W : ι → ℚ),
        (∀ h t, 0 < a' h t) → (∀ h t, 0 < b' h t) → (∀ h ∈ H, seqLik (a' h) (n' h) = W h) →
        ∀ L Lc ρ ρc : ℝ,
          L ≤ -Real.logb 2
              ((∏ h ∈ H, ∏ t ∈ Finset.range (n' h), seqMix (a' h) (b' h) t : ℚ) : ℝ) + ρ →
          ∑ h ∈ H, -Real.logb 2 (W h : ℝ) ≤ Lc + ρc →
          L ≤ Lc + H.card + ρ + ρc := by
  have hjoin := (sequential_mixture_bounds ha hb n).2.2.2
  have hm := min_le_left (-Real.logb 2 (seqLik a n : ℝ)) (-Real.logb 2 (seqLik b n : ℝ))
  have hmin : -Real.logb 2 ((∏ t ∈ Finset.range n, seqMix a b t : ℚ) : ℝ) ≤
      -Real.logb 2 (seqLik a n : ℝ) + 1 := by linarith
  rw [hcell] at hmin
  refine ⟨hmin, fun S => ?_, fun H a' b' n' W ha' hb' hW L Lc ρ ρc hL hc => ?_⟩
  · have hdom := ((stop_kraft_and_dominance hw N m s).2 S).2
    linarith
  · have hp := passage_join_bound H n' W ha' hb' hW
    linarith

end Dominance

section Audit

#print axioms bundle_causal
#print axioms bundle_restrict
#print axioms feature_scale_square
#print axioms address_descends_retention
#print axioms phase_partition_finite
#print axioms phaseClass_coarsen
#print axioms phaseClass_of_exact
#print axioms lock_partition_finite
#print axioms bundle_code_injective
#print axioms passage_join_bound
#print axioms cell_only_dominance_with_feature_charge

end Audit

end Holonics.Compression.Landmark.Context.Address

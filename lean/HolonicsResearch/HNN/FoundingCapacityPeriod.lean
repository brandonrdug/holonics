import Holonics.HNN.RangedMoment

/-!
# A founded ring's capacity crossover is nondecreasing in its period, and a late source stays inside it

Source: comment c6249536068 of #62, item 3 (`capacity_crossover_monotone_in_period`), on the
founding of #398 (`hnn::moment::{capacity, capacity_located, capacity_admits}` and
`hnn::field::Field::{founding_candidates, founding_admits}` at `d5ed4adc1`; atlas
`hnn.capacity-crossover-monotone-in-period`). A founding of period `ℓ` declares the field's rings
and sources with one `Own` source ring appended (`Field::founding_partition`), whose lift advances
one tick a cell, and admits the period where the expanded partition's count `N_ℓ(n)` falls below
`|A|ⁿ` at the declared population (`founding_admits`). The field then doubles and bisects the
admitted periods and confirms the boundary by one whole declaration (`founding_candidates`), which
reads a monotone boundary only if `N_ℓ(n)` is nondecreasing in `ℓ`.

The box wrote the count as `n·(F + ℓ)`; the atlas row as `n*(F+ell)`. Read against
`capacity_with_clock` and `Field::founding_partition`, the count is the product
`N_ℓ(n) = F(n) · (n + ℓ) · C(n + ℓ|A| − 1, ℓ|A| − 1) · ∏_δ C(n − δ + ℓ|A|² − 1, ℓ|A|² − 1)` of the
field's own count `F(n)` (the existing rings' lift factors and the existing sources' histograms),
the Own ring's lift factor `1·n + ℓ`, and the founded source's histograms (`foundCount_eq`); the
statement is that this product is nondecreasing in `ℓ`.

## What is proved

* **Stars and bars grow with their slots and their population.** `C(m + S − 1, S − 1)` is
  nondecreasing in the slots `S` (`choose_slots_mono`) and in the population `m`, so in both at
  once (`choose_slots_le`); an Own population `t ≤ n` gives `C(t + k − 1, k − 1) ≤ C(n + k − 1, k − 1)`
  (`own_population_le`).
* **The source-state count is nondecreasing in every period.** For two declarations with the same
  sources and offsets, periods pointwise `D.period ≤ D'.period` give
  `D.capacityBoundWith ≤ D'.capacityBoundWith` at every rate, ring count, alphabet and population
  (`capacityBoundWith_mono_period`): each lift factor `rate·n + d_g` and each histogram's slot count
  `d_g|A|`, `d_g|A|²` grows with `d_g`.
* **The founded partition.** `found D G ℓ` appends ring `G` of period `ℓ` to the sources, at the
  Own rate one (`foundRate`). Where `G` is not already a source, its count factors as the field's
  own count times the founded ring's factors (`foundCount_eq`), and it is nondecreasing in `ℓ`
  (`foundCount_mono`).
* **`capacity_crossover_monotone_in_period`.** A period lossy at a population leaves every shorter
  period lossy there (`lossy_of_lossy_longer`), so the admitted periods at the field's population
  are an initial segment, the monotone boundary `founding_candidates` doubles and bisects
  (`founding_admits_initial_segment`); and the crossover `n*_ℓ`, the least population at which the
  founded partition is lossy, is nondecreasing in the period (`capacity_crossover_monotone_in_period`).
  Through `RangedMoment.capacityWith_persists` (lossiness persists from a first crossing past the
  held window), the one-count predicate `N_ℓ(P) < |A|^P` is `n*_ℓ ≤ P` (`founding_admits_iff`),
  which is what `capacity_admits` reads in place of the search.
* **The late-source histogram bridge.** A source founded after the field opened has its own
  population `t ≤ n`: its phase counts total `t` and its offset-`δ` counts total `min(t, n − δ)`
  (the module header of `hnn::moment` at `d5ed4adc1`), and its Own lift has taken at most `n` ticks.
  The box of such states has at most `(n + ℓ)·C(n + ℓ|A| − 1, ℓ|A| − 1)·∏_δ C(n − δ + ℓ|A|² − 1, ℓ|A|² − 1)`
  states (`late_source_card_le`, `late_source_bridge`), the founded source's factor at the declared
  population, so the founded partition's count `N_ℓ(n)` still bounds it and its crossover still
  certifies lossiness.

## Limits

* The bridge is a count: that a late source's persisting state lies in that box (its phase counts
  of total `t`, its offset counts of total `min(t, n − δ)`, its lift within `n` ticks) is the
  ingest's bookkeeping at a late opening, which `HNN/Moment.persist_mem_box` proves at a common
  opening and which is not re-proved here for a late one.
* One opening, no re-key: the scope of `HNN/RangedMoment`'s count. The reframed count of
  `HNN/ReframedMoment` and the leaky factor of `HNN/LeakyCapacity` stand beside it.
* The pigeonhole reading of `N_ℓ(n) < |A|ⁿ` holds for a total source map on the full `A^n`, as in
  `moment_capacityWith`; nothing here bounds a learned constitution.

The computational object is the helical pair interaction: the founded source's histograms count
pairs of a cell and the cell `δ` back at each phase of the founded ring. Of the winding guide's six
objects this touches the helix (the Own ring's lift and its period), the pair (the offset counts),
and the tower thread (the founded ring is a restriction of the field's partition to one more
source); faces and placement, cell holonomy and the tube stay attached through `HNN/Moment`.

Consumers: `HNN/RangedMoment.SourceDecl.{capacityBoundWith, capacityWith_persists}`,
`HNN/Moment.SourceDecl.capacityBound`, the founding's search (`hnn::field::Field::{
founding_candidates, founding_admits}` and `hnn::moment::{capacity, capacity_admits}` at
`d5ed4adc1`), and the atlas row `hnn.capacity-crossover-monotone-in-period`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FoundingCapacityPeriod

open Holonics.HNN.Moment

/-! ## 1. Stars and bars grow with their slots and their population -/

/-- [proved-derived; formal-checked] **A stars-and-bars count grows with its slots**:
`S ↦ C(m + S − 1, S − 1)` is nondecreasing, by Pascal's rule
`C(m + S, S) = C(m + S − 1, S − 1) + C(m + S − 1, S)`. -/
theorem choose_slots_mono (m : ℕ) : Monotone fun S => Nat.choose (m + S - 1) (S - 1) := by
  refine monotone_nat_of_le_succ fun S => ?_
  rcases S with _ | S
  · simp
  · show Nat.choose (m + (S + 1) - 1) (S + 1 - 1) ≤ Nat.choose (m + (S + 1 + 1) - 1) (S + 1 + 1 - 1)
    rw [show m + (S + 1) - 1 = m + S by omega, show S + 1 - 1 = S by omega,
      show m + (S + 1 + 1) - 1 = m + S + 1 by omega, show S + 1 + 1 - 1 = S + 1 by omega,
      Nat.choose_succ_succ]
    exact Nat.le_add_right _ _

/-- [proved-derived; formal-checked] **A stars-and-bars count grows with its population and its
slots.** -/
theorem choose_slots_le {m m' S S' : ℕ} (hm : m ≤ m') (hS : S ≤ S') :
    Nat.choose (m + S - 1) (S - 1) ≤ Nat.choose (m' + S' - 1) (S' - 1) :=
  (Nat.choose_le_choose _ (by omega)).trans (choose_slots_mono m' hS)

/-- [proved-derived; formal-checked] **An Own population below the declared one counts fewer
histograms**: `t ≤ n` gives `C(t + k − 1, k − 1) ≤ C(n + k − 1, k − 1)`. -/
theorem own_population_le {t n : ℕ} (k : ℕ) (h : t ≤ n) :
    Nat.choose (t + k - 1) (k - 1) ≤ Nat.choose (n + k - 1) (k - 1) :=
  choose_slots_le h le_rfl

/-! ## 2. The source-state count grows with every period -/

section Count

variable {A : Type*}

/-- [proved-derived; formal-checked] **The source-state count is nondecreasing in every period.**
Two declarations with the same sources and offsets, periods pointwise ordered, have their counts
`N(n) = |A|^(max Δ)·∏_(g<G)(rate_g n + d_g)·∏_(g∈𝒮)[C(n + d_g|A| − 1, d_g|A| − 1)·∏_δ C(n − δ + d_g|A|² − 1, d_g|A|² − 1)]`
in the same order. -/
theorem capacityBoundWith_mono_period {D D' : SourceDecl A} (hs : D'.sources = D.sources)
    (ho : D'.offsets = D.offsets) (hp : ∀ g, D.period g ≤ D'.period g) (rate : ℕ → ℕ)
    (G alphabet n : ℕ) :
    D.capacityBoundWith rate G alphabet n ≤ D'.capacityBoundWith rate G alphabet n := by
  unfold SourceDecl.capacityBoundWith SourceDecl.windowLength
  rw [hs, ho]
  refine Nat.mul_le_mul (Nat.mul_le_mul le_rfl
    (Finset.prod_le_prod' fun g _ => Nat.add_le_add_left (hp g) _))
    (Finset.prod_le_prod' fun g _ => Nat.mul_le_mul ?_ (Finset.prod_le_prod' fun δ _ => ?_))
  · exact choose_slots_le le_rfl (Nat.mul_le_mul_right _ (hp g))
  · exact choose_slots_le le_rfl (Nat.mul_le_mul_right _ (hp g))

/-! ## 3. The founded partition -/

/-- [definition] **The partition a founding of period `ℓ` declares** (`Field::founding_partition`):
ring `G` takes period `ℓ` and joins the sources; the offsets and the other rings stay. -/
def found (D : SourceDecl A) (G ℓ : ℕ) : SourceDecl A :=
  { D.toSelectiveDecl with
    period := Function.update D.period G ℓ
    sources := insert G D.sources
    offsets := D.offsets }

/-- [definition] **The founded ring's rate**: an Own ring advances one tick a cell
(`capacity_rates`: `RingAdvance::Own` has rate one on every clock). -/
def foundRate (rate : ℕ → ℕ) (G : ℕ) : ℕ → ℕ := Function.update rate G 1

/-- [definition] **The founded partition's count** `N_ℓ(n)` on `G + 1` rings. -/
def foundCount (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet ℓ n : ℕ) : ℕ :=
  (found D G ℓ).capacityBoundWith (foundRate rate G) (G + 1) alphabet n

/-- [proved-derived; formal-checked] **The founded count factors** as the field's own count `F(n)`
times the Own ring's lift factor `n + ℓ` and the founded source's histograms, where ring `G` was not
already a source. -/
theorem foundCount_eq (D : SourceDecl A) (rate : ℕ → ℕ) {G : ℕ} (hG : G ∉ D.sources)
    (alphabet ℓ n : ℕ) :
    foundCount D rate G alphabet ℓ n =
      D.capacityBoundWith rate G alphabet n *
        ((n + ℓ) * (Nat.choose (n + ℓ * alphabet - 1) (ℓ * alphabet - 1) *
          ∏ δ ∈ D.offsets, Nat.choose (n - δ + ℓ * alphabet ^ 2 - 1) (ℓ * alphabet ^ 2 - 1))) := by
  unfold foundCount SourceDecl.capacityBoundWith SourceDecl.windowLength
  have hlift : ∏ g ∈ Finset.range G, (foundRate rate G g * n + (found D G ℓ).period g) =
      ∏ g ∈ Finset.range G, (rate g * n + D.period g) := by
    refine Finset.prod_congr rfl fun g hg => ?_
    have hne : g ≠ G := (Finset.mem_range.mp hg).ne
    simp [foundRate, found, Function.update_of_ne hne]
  have hsrc : ∏ g ∈ D.sources,
      (Nat.choose (n + (found D G ℓ).period g * alphabet - 1) ((found D G ℓ).period g * alphabet - 1) *
        ∏ δ ∈ D.offsets, Nat.choose (n - δ + (found D G ℓ).period g * alphabet ^ 2 - 1)
          ((found D G ℓ).period g * alphabet ^ 2 - 1)) =
      ∏ g ∈ D.sources,
        (Nat.choose (n + D.period g * alphabet - 1) (D.period g * alphabet - 1) *
          ∏ δ ∈ D.offsets, Nat.choose (n - δ + D.period g * alphabet ^ 2 - 1)
            (D.period g * alphabet ^ 2 - 1)) := by
    refine Finset.prod_congr rfl fun g hg => ?_
    have hne : g ≠ G := fun h => hG (h ▸ hg)
    simp [found, Function.update_of_ne hne]
  have hGp : (found D G ℓ).period G = ℓ := by simp [found]
  have hGr : foundRate rate G G = 1 := by simp [foundRate]
  rw [show (found D G ℓ).sources = insert G D.sources from rfl,
    show (found D G ℓ).offsets = D.offsets from rfl, Finset.prod_range_succ, hlift,
    Finset.prod_insert hG, hsrc, hGp, hGr, one_mul]
  ring

/-- [proved-derived; formal-checked] **The founded count is nondecreasing in the period.** -/
theorem foundCount_mono (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet : ℕ) {ℓ ℓ' : ℕ}
    (hℓ : ℓ ≤ ℓ') (n : ℕ) :
    foundCount D rate G alphabet ℓ n ≤ foundCount D rate G alphabet ℓ' n := by
  unfold foundCount
  refine capacityBoundWith_mono_period (D := found D G ℓ) (D' := found D G ℓ') rfl rfl
    (fun g => ?_) _ _ _ _
  by_cases h : g = G
  · subst h; simpa [found] using hℓ
  · simp [found, Function.update_of_ne h]

/-! ## 4. The crossover is nondecreasing in the period -/

/-- [proved-derived; formal-checked] **A period lossy at a population leaves every shorter period
lossy there**: `N_ℓ'(n) < |A|ⁿ` and `ℓ ≤ ℓ'` give `N_ℓ(n) < |A|ⁿ`. -/
theorem lossy_of_lossy_longer (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet : ℕ) {ℓ ℓ' n : ℕ}
    (hℓ : ℓ ≤ ℓ') (h : foundCount D rate G alphabet ℓ' n < alphabet ^ n) :
    foundCount D rate G alphabet ℓ n < alphabet ^ n :=
  (foundCount_mono D rate G alphabet hℓ n).trans_lt h

/-- [proved-derived; formal-checked] **The admitted periods are an initial segment**: a period the
population `P` admits (`founding_admits`: the expanded partition lossy at `P`) admits every shorter
one, so the doubling and bisection of `founding_candidates` read a monotone boundary. -/
theorem founding_admits_initial_segment (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet P : ℕ)
    {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') (h : foundCount D rate G alphabet ℓ' P < alphabet ^ P) :
    foundCount D rate G alphabet ℓ P < alphabet ^ P :=
  lossy_of_lossy_longer D rate G alphabet hℓ h

/-- [proved-derived; formal-checked] A longer period that is lossy somewhere leaves the shorter one
lossy somewhere. -/
theorem exists_lossy_of_longer (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet : ℕ) {ℓ ℓ' : ℕ}
    (hℓ : ℓ ≤ ℓ') (h : ∃ n, foundCount D rate G alphabet ℓ' n < alphabet ^ n) :
    ∃ n, foundCount D rate G alphabet ℓ n < alphabet ^ n :=
  h.imp fun _ hn => lossy_of_lossy_longer D rate G alphabet hℓ hn

/-- [proved-derived; formal-checked] **`capacity_crossover_monotone_in_period`.** The crossover
`n*_ℓ`, the least population at which the founded partition of period `ℓ` is lossy, is
nondecreasing in the period: `ℓ ≤ ℓ'` gives `n*_ℓ ≤ n*_ℓ'`. -/
theorem capacity_crossover_monotone_in_period (D : SourceDecl A) (rate : ℕ → ℕ) (G alphabet : ℕ)
    {ℓ ℓ' : ℕ} (hℓ : ℓ ≤ ℓ') (h : ∃ n, foundCount D rate G alphabet ℓ' n < alphabet ^ n) :
    Nat.find (exists_lossy_of_longer D rate G alphabet hℓ h) ≤ Nat.find h :=
  Nat.find_mono fun _ hn => lossy_of_lossy_longer D rate G alphabet hℓ hn

end Count

section Persist

variable {A : Type*} [Fintype A] [Nonempty A]

/-- [proved-derived; formal-checked] **The one count reads the crossover.** Where the founded
partition's first crossing `n*_ℓ` lies past the held window (`max Δ < n*_ℓ`) and every period is at
least one, a population `P` is lossy exactly when `n*_ℓ ≤ P`: the predicate `founding_admits`
evaluates by one count is the crossover's (`RangedMoment.capacityWith_persists`). -/
theorem founding_admits_iff (D : SourceDecl A) (rate : ℕ → ℕ) (G : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hd1 : ∀ g, 1 ≤ D.period g)
    (h : ∃ n, foundCount D rate G (Fintype.card A) ℓ n < Fintype.card A ^ n)
    (hwin : D.windowLength + 1 ≤ Nat.find h) (P : ℕ) :
    foundCount D rate G (Fintype.card A) ℓ P < Fintype.card A ^ P ↔ Nat.find h ≤ P := by
  refine ⟨fun hP => Nat.find_min' h hP, fun hP => ?_⟩
  have hd1' : ∀ g, 1 ≤ (found D G ℓ).period g := fun g => by
    by_cases hg : g = G
    · subst hg; simpa [found] using hℓ
    · simpa [found, Function.update_of_ne hg] using hd1 g
  have habove : Fintype.card A ^ (Nat.find h - 1) ≤
      foundCount D rate G (Fintype.card A) ℓ (Nat.find h - 1) :=
    not_lt.mp (Nat.find_min h (by omega))
  exact SourceDecl.capacityWith_persists (D := found D G ℓ) (foundRate rate G) hd1' (G + 1)
    (nstar := Nat.find h) hwin (Nat.find_spec h) habove P hP

end Persist

/-! ## 5. The late-source histogram bridge -/

section Late

/-- [proved-derived; formal-checked] **The histograms of a population** of `t` arrivals on `k ≥ 1`
slots number `C(t + k − 1, k − 1)`. -/
theorem card_sym_eq_choose (β : Type*) [Fintype β] [DecidableEq β] (t : ℕ)
    (hβ : 1 ≤ Fintype.card β) :
    Fintype.card (Sym β t) = Nat.choose (t + Fintype.card β - 1) (Fintype.card β - 1) := by
  rw [Sym.card_sym_eq_multichoose, Nat.multichoose_eq,
    show Fintype.card β + t - 1 = t + Fintype.card β - 1 by omega]
  exact Nat.choose_symm_of_eq_add (by omega)

/-- [proved-derived; formal-checked] **A late source's histograms fit the declared population's**:
phase counts of total `t ≤ n` and offset-`δ` counts of total `min(t, n − δ)` take at most
`C(n + k − 1, k − 1)·∏_δ C(n − δ + k′ − 1, k′ − 1)` values, `k` and `k′` the phase and pair slots. -/
theorem late_source_card_le (β γ : Type*) [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    (offsets : Finset ℕ) {t n : ℕ} (ht : t ≤ n) (hβ : 1 ≤ Fintype.card β)
    (hγ : 1 ≤ Fintype.card γ) :
    Fintype.card (Sym β t × ((δ : offsets) → Sym γ (min t (n - δ.1)))) ≤
      Nat.choose (n + Fintype.card β - 1) (Fintype.card β - 1) *
        ∏ δ ∈ offsets, Nat.choose (n - δ + Fintype.card γ - 1) (Fintype.card γ - 1) := by
  rw [Fintype.card_prod, Fintype.card_pi, card_sym_eq_choose β t hβ]
  refine Nat.mul_le_mul (own_population_le _ ht) ?_
  rw [← Finset.prod_coe_sort offsets]
  refine Finset.prod_le_prod' fun δ _ => ?_
  rw [card_sym_eq_choose γ _ hγ]
  exact own_population_le _ (min_le_right _ _)

/-- [proved-derived; formal-checked] **The late-source histogram bridge.** A source of period `ℓ`
founded after the field opened, with its own population `t ≤ n`, its Own lift within `n` ticks of
its opening, its phase counts of total `t` and its offset counts of total `min(t, n − δ)`, has at
most the founded source's factor of `N_ℓ(n)` at the declared population `n`:
`(n + ℓ)·C(n + ℓ|A| − 1, ℓ|A| − 1)·∏_δ C(n − δ + ℓ|A|² − 1, ℓ|A|² − 1)`. With `foundCount_eq`, the
founded partition's count still bounds the late source's states. -/
theorem late_source_bridge (A : Type*) [Fintype A] [DecidableEq A] [Nonempty A]
    (offsets : Finset ℕ) (ℓ : ℕ) [NeZero ℓ] (τ₀ : ℕ) {t n : ℕ} (ht : t ≤ n) :
    (Finset.Icc τ₀ (τ₀ + n)).card *
        Fintype.card (Sym (ZMod ℓ × A) t × ((δ : offsets) → Sym (ZMod ℓ × A × A) (min t (n - δ.1)))) ≤
      (n + ℓ) * (Nat.choose (n + ℓ * Fintype.card A - 1) (ℓ * Fintype.card A - 1) *
        ∏ δ ∈ offsets,
          Nat.choose (n - δ + ℓ * Fintype.card A ^ 2 - 1) (ℓ * Fintype.card A ^ 2 - 1)) := by
  have hA : 1 ≤ Fintype.card A := Fintype.card_pos
  have hℓ : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr (NeZero.ne ℓ)
  have hβ : Fintype.card (ZMod ℓ × A) = ℓ * Fintype.card A := by
    rw [Fintype.card_prod, ZMod.card]
  have hγ : Fintype.card (ZMod ℓ × A × A) = ℓ * Fintype.card A ^ 2 := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, sq]
  have hlift : (Finset.Icc τ₀ (τ₀ + n)).card ≤ n + ℓ := by
    rw [Nat.card_Icc]; omega
  have hcard := late_source_card_le (ZMod ℓ × A) (ZMod ℓ × A × A) offsets ht
    (by rw [hβ]; exact Nat.one_le_iff_ne_zero.mpr (by positivity))
    (by rw [hγ]; exact Nat.one_le_iff_ne_zero.mpr (by positivity))
  rw [hβ, hγ] at hcard
  exact Nat.mul_le_mul hlift hcard

end Late

end Holonics.HNN.FoundingCapacityPeriod

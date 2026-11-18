import Mathlib

/-!
# A level's sites are the landmarks of its news: the first round of the claim, its isolation, and what it keeps

[proved-derived] The source is #410's box "The level's law of sites", left by the record of November 13
(`research/records/2026-11-13_A_LEVELS_SITES_ARE_THE_LANDMARKS_OF_ITS_NEWS_A_PLACE_NO_LARGER_NEWS_STANDS_WITHIN_A_SECTION_OF_THE_CLAIM_THE_CARRIED_CUT_AND_THE_ODOMETER_ARE_ONE_LAW_ANCHORED_NEARER_AND_FARTHER_AND_ONE_PROGRAM_READS_EVERY_SYMBOL_STREAM.md`,
§2 and §5; atlas `code.site-isolation-landmark`; built in the engine's `scale`, G145).

The model. A passage is `N` places `0, …, N − 1` with news `c : ℕ → K` read on `K`, any linearly ordered commutative
ring: `ℤ` is the news at a declared grain (the machine's, a code on `2^(−20)` bits), `ℝ` the record's nats. A place
arrives at `S_t = Σ_(v ≤ t) c_v` (`arrival`; a place's own news lies in the gap before it), `u ≻ t` when `c_u > c_t`,
or `c_u = c_t` and `u < t` (`Greater`), and `u` reaches `t` at the section `σ` when `|S_u − S_t| < σ` (`Reaches`).
A place is a site of the first round `P(σ)` when no greater place of the passage reaches it (`Site`). The claim
`G(σ)` is the set with `t ∈ G ⇔` no `u ∈ G` with `u ≻ t` reaches `t` (`IsClaim`, `claim`).

What is proved. News is nonnegative wherever a hypothesis `hc` says so, and nothing asks it to be positive.

1. **The order** (`greater_irrefl`, `greater_trans`, `greater_asymm`, `greater_total`, `greater_of_lt`,
   `greater_of_gt`): `≻` is a strict total order of the places; an earlier place is greater when its news is no
   less, a later one when its news is more. A passage that holds a place holds a greatest one (`exists_greatest`).
2. **The isolation** (`isolation`, `site_iff_isolation`, `isolation_eq_top`, `left_nearest`, `right_nearest`,
   `isolation_eq_min`, `isolation_eq_left`, `isolation_eq_right`): with `ρ_t` the least news to a greater place
   (`⊤` where none is greater), `t ∈ P(σ) ⇔ σ ≤ ρ_t`; and `ρ_t` is the record's
   `min(S_t − S_u at the last u < t with c_u ≥ c_t, S_u − S_t at the first u > t with c_u > c_t)`, one side alone
   where the other holds no such place.
3. **A landmark opens** (statement 1; `landmark_opens`): `c_t ≥ σ ⇒ t ∈ P(σ)`.
4. **The grain** (statement 2; `sites_apart`, `sites_apart_ordered`, `claim_sites_apart`): two sites of `P(σ)`, and
   two sites of `G(σ)`, stand `σ` or more apart.
5. **One number a place** (statement 3; `site_antitone`, `claim_not_nested`, `record_example_is_nested`):
   `σ ≤ σ′ ⇒ P(σ′) ⊆ P(σ)`. The claim is not nested: news `30, 15, 9` (the record's unit in tenths) has
   `G(10) = {0, 1}` and `G(20) = {0, 2}`.
6. **A site at every section** (R7; `greatest_is_site`, `exists_site`): the passage's greatest place is a site at
   every section, so `P(σ)` holds a place whenever the passage does.
7. **The claim** (`rank_lt`, `claim_isClaim`, `claim_unique`, `site_subset_claim`, `claim_covers`): on a finite
   passage the claim exists and is the one set that satisfies its equation (well-founded on `≻`); `P(σ) ⊆ G(σ)`;
   and every place is a site of `G` or is reached by a greater one (statement 6's first half).
8. **Reach** (statement 4; `site_congr`, `site_congr_iff`): whether `t ∈ P(σ)` is decided by the places within a
   section of `t`: two passages in which the places that reach `t` are the same places, with the same news and at
   the same distance from `t`, agree on it.
9. **The stable core, one direction** (statement 5; `stable_core`): a site of `P(σ)` is a site of the claim of
   every passage that agrees with this one within a section of it.
10. **A stretch that repeats is dark** (statement 7; `repeat_is_dark`, `period_news`, `sites_of_repeating_stretch`,
    `site_near_start_of_repeat`): where a place's news equals the news one period earlier and the period carries
    less than a section, the place is no site; all periods of a repeating stretch carry the same news; so a site
    of `P(σ)` inside a repeating stretch stands in its first period, less than a section from its start.
11. **Silence** (statement 8; `faint_place_is_dark`, `zero_news_not_greater`): a place that carries less than a
    section and no more than the place before it is no site, and a place of no news is greater than no place of
    positive news.
12. **Rulers** (`ruler_sites_two`, `ruler_sites_five`, `ruler_isolations`): the passage `2, 1, 3, 1, 1, 2, 1, 4`
    arrives at `2, 3, 6, 7, 8, 10, 11, 15`; its isolations are `4, 1, 9, 1, 1, 4, 1, ⊤`, its sites at the section
    `2` are the places `0, 2, 5, 7` and at the section `5` the places `2, 7`.

Limits. One passage of one region: the built cut begins again at each region's opening, which is this law on each
region. The stable core's other direction (a place some greater place reaches is no site of the claim in a passage
built to agree within the section) is not here: its passage is constructed in the record and is stated there for
news in `ℝ`; at an integer grain the record's "less news than `u`" has no positive value when `c_u` is one unit.
Statement 6's bound of three sections on a stride of `G` and statement 8's scaling are not here. Agreement of two
passages is stated at the same indices; a passage with places inserted before `t` is the same statement after a
shift of indices, which is not modelled. The level's clock `τ_j` and its strides are in `HNN/PhaseChart`.

The computational object is the helical pair interaction: the clock of news is a helix whose turn is the section,
a site is a face where the passage's own order of news has no greater neighbour within a turn, and the claim is
the pairing's precedence read along that helix. Of the winding guide's six general objects this touches the helix
(the clock of news and its section), the faces and placement (which places are sites) and the tower thread (the
nesting of `P` across sections); the pair, the cell holonomy and the tube stay attached.

Consumers: the atlas rows `code.site-isolation-landmark` and `tower.level-holds-no-unit`; `HNN/PhaseChart`'s clock.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.SiteIsolation

open Finset

section Law

variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## The clock of news -/

/-- [definition] A place's arrival on the clock of news, `S_t = Σ_(v ≤ t) c_v`: its own news lies before it. -/
def arrival (c : ℕ → K) (t : ℕ) : K := ∑ v ∈ range (t + 1), c v

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] The first place arrives at its own news, `S_0 = c_0`. -/
@[simp] theorem arrival_zero (c : ℕ → K) : arrival c 0 = c 0 := by simp [arrival]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard] `S_(t+1) = S_t + c_(t+1)`. -/
theorem arrival_succ (c : ℕ → K) (t : ℕ) : arrival c (t + 1) = arrival c t + c (t + 1) := by
  unfold arrival
  rw [Finset.sum_range_succ]

/-- [proved-standard] With nonnegative news a later place arrives no earlier. -/
theorem arrival_mono {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {u t : ℕ} (h : u ≤ t) : arrival c u ≤ arrival c t := by
  induction t, h using Nat.le_induction with
  | base => exact le_rfl
  | succ t _ ih =>
    rw [arrival_succ]
    linarith [hc (t + 1)]

/-- [proved-standard] A later place stands at least its own news after an earlier one: `S_u + c_t ≤ S_t`. -/
theorem arrival_add_le {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {u t : ℕ} (h : u < t) :
    arrival c u + c t ≤ arrival c t := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [arrival_succ]
  linarith [arrival_mono hc (Nat.lt_succ_iff.mp h)]

/-- [proved-standard] The distance of two places on the clock of news is the later arrival less the earlier. -/
theorem dist_of_le {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {u t : ℕ} (h : u ≤ t) :
    |arrival c u - arrival c t| = arrival c t - arrival c u := by
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (arrival_mono hc h))]

/-! ## The order of news, reach, and the first round -/

/-- [definition] `u ≻ t`: `u` carries more news, or as much and stands earlier. -/
def Greater (c : ℕ → K) (u t : ℕ) : Prop := c t < c u ∨ (c u = c t ∧ u < t)

instance (c : ℕ → K) (u t : ℕ) : Decidable (Greater c u t) :=
  inferInstanceAs (Decidable (c t < c u ∨ (c u = c t ∧ u < t)))

/-- [definition] `u` reaches `t` at the section `σ`: they stand less than a section apart. -/
def Reaches (c : ℕ → K) (σ : K) (u t : ℕ) : Prop := |arrival c u - arrival c t| < σ

instance (c : ℕ → K) (σ : K) (u t : ℕ) : Decidable (Reaches c σ u t) :=
  inferInstanceAs (Decidable (|arrival c u - arrival c t| < σ))

/-- [definition] The first round `P(σ)` on a passage of `N` places: no greater place reaches `t`. -/
def Site (c : ℕ → K) (N : ℕ) (σ : K) (t : ℕ) : Prop :=
  t < N ∧ ∀ u < N, Greater c u t → ¬ Reaches c σ u t

instance (c : ℕ → K) (N : ℕ) (σ : K) (t : ℕ) : Decidable (Site c N σ t) :=
  inferInstanceAs (Decidable (t < N ∧ ∀ u < N, Greater c u t → ¬ Reaches c σ u t))

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] No place is greater than itself. -/
theorem greater_irrefl (c : ℕ → K) (t : ℕ) : ¬ Greater c t t := by
  rintro (h | ⟨_, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] The order of news is transitive. -/
theorem greater_trans {c : ℕ → K} {u v t : ℕ} (h1 : Greater c u v) (h2 : Greater c v t) : Greater c u t := by
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inl (by rw [← h2]; exact h1)
  · exact Or.inl (by rw [h1]; exact h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] Of two places at most one is the greater. -/
theorem greater_asymm {c : ℕ → K} {u t : ℕ} (h : Greater c u t) : ¬ Greater c t u :=
  fun h' => greater_irrefl c u (greater_trans h h')

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] **Of two places one is the greater.** -/
theorem greater_total (c : ℕ → K) {u t : ℕ} (h : u ≠ t) : Greater c u t ∨ Greater c t u := by
  rcases lt_trichotomy (c u) (c t) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · rcases Nat.lt_or_gt_of_ne h with h' | h'
    · exact Or.inl (Or.inr ⟨heq, h'⟩)
    · exact Or.inr (Or.inr ⟨heq.symm, h'⟩)
  · exact Or.inl (Or.inl hgt)

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] An earlier place is greater exactly when its news is no less. -/
theorem greater_of_lt {c : ℕ → K} {u t : ℕ} (h : u < t) : Greater c u t ↔ c t ≤ c u := by
  constructor
  · rintro (h1 | ⟨h1, _⟩)
    · exact h1.le
    · exact h1.ge
  · intro h1
    rcases h1.lt_or_eq with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h2.symm, h⟩

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] A later place is greater exactly when its news is more. -/
theorem greater_of_gt {c : ℕ → K} {u t : ℕ} (h : t < u) : Greater c u t ↔ c t < c u := by
  constructor
  · rintro (h1 | ⟨_, h1⟩)
    · exact h1
    · exact absurd h1 (Nat.lt_asymm h)
  · exact Or.inl

omit [IsStrictOrderedRing K] in
/-- [proved-derived] Reach is symmetric. -/
theorem reaches_comm (c : ℕ → K) (σ : K) (u t : ℕ) : Reaches c σ u t ↔ Reaches c σ t u := by
  unfold Reaches
  rw [abs_sub_comm]

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] **A passage that holds a place holds a greatest one.** -/
theorem exists_greatest (c : ℕ → K) {N : ℕ} (hN : 0 < N) : ∃ t < N, ∀ u < N, ¬ Greater c u t := by
  classical
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (range N) c ⟨0, mem_range.mpr hN⟩
  have hs : ((range N).filter (fun u => c u = c m)).Nonempty := ⟨m, mem_filter.mpr ⟨hm, rfl⟩⟩
  have hmem := Finset.min'_mem _ hs
  rw [mem_filter, mem_range] at hmem
  refine ⟨_, hmem.1, fun u hu hg => ?_⟩
  rcases hg with h | ⟨h1, h2⟩
  · rw [hmem.2] at h
    exact absurd (hmax u (mem_range.mpr hu)) (not_le.mpr h)
  · have hus : u ∈ (range N).filter (fun u => c u = c m) :=
      mem_filter.mpr ⟨mem_range.mpr hu, h1.trans hmem.2⟩
    exact absurd (Finset.min'_le _ u hus) (not_le.mpr h2)

/-! ## The isolation -/

/-- [definition] A place's isolation `ρ_t`: the least news to a greater place of the passage, `⊤` where no place
is greater. -/
def isolation (c : ℕ → K) (N t : ℕ) : WithTop K :=
  ((range N).filter (fun u => Greater c u t)).inf fun u => ((|arrival c u - arrival c t| : K) : WithTop K)

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The landmark clause:** `t ∈ P(σ) ⇔ σ ≤ ρ_t`. -/
theorem site_iff_isolation (c : ℕ → K) {N t : ℕ} (σ : K) (ht : t < N) :
    Site c N σ t ↔ (σ : WithTop K) ≤ isolation c N t := by
  unfold Site isolation Reaches
  rw [Finset.le_inf_iff]
  constructor
  · rintro ⟨_, h⟩ u hu
    rw [mem_filter, mem_range] at hu
    exact WithTop.coe_le_coe.mpr (not_lt.mp (h u hu.1 hu.2))
  · intro h
    exact ⟨ht, fun u hu hg =>
      not_lt.mpr (WithTop.coe_le_coe.mp (h u (mem_filter.mpr ⟨mem_range.mpr hu, hg⟩)))⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] The greatest place's isolation is `⊤`. -/
theorem isolation_eq_top (c : ℕ → K) {N t : ℕ} (h : ∀ u < N, ¬ Greater c u t) : isolation c N t = ⊤ := by
  unfold isolation
  rw [Finset.filter_false_of_mem (fun u hu => h u (mem_range.mp hu)), Finset.inf_empty]

/-- [proved-derived] On the left the nearest greater place is the last one whose news is no less: every greater
place before `t` arrives no later than it. -/
theorem left_nearest {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {u t w : ℕ}
    (hlast : ∀ x, u < x → x < t → c x < c t) (hw : w < t) (hg : Greater c w t) :
    arrival c w ≤ arrival c u := by
  have hcw : c t ≤ c w := (greater_of_lt hw).mp hg
  have hwu : w ≤ u := by
    by_contra hcon
    exact absurd (hlast w (not_le.mp hcon) hw) (not_lt.mpr hcw)
  exact arrival_mono hc hwu

/-- [proved-derived] On the right the nearest greater place is the first one whose news is more: every greater
place after `t` arrives no earlier than it. -/
theorem right_nearest {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {v t w : ℕ}
    (hfirst : ∀ x, t < x → x < v → c x ≤ c t) (hw : t < w) (hg : Greater c w t) :
    arrival c v ≤ arrival c w := by
  have hcw : c t < c w := (greater_of_gt hw).mp hg
  have hvw : v ≤ w := by
    by_contra hcon
    exact absurd (hfirst w hw (not_le.mp hcon)) (not_le.mpr hcw)
  exact arrival_mono hc hvw

/-- [proved-derived] **The isolation is the record's minimum:** with `u` the last place before `t` whose news is
no less and `v` the first place after `t` whose news is more, `ρ_t = min(S_t − S_u, S_v − S_t)`. -/
theorem isolation_eq_min {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N u t v : ℕ}
    (hu : u < t) (hcu : c t ≤ c u) (hlast : ∀ x, u < x → x < t → c x < c t)
    (hv : t < v) (hvN : v < N) (hcv : c t < c v) (hfirst : ∀ x, t < x → x < v → c x ≤ c t) :
    isolation c N t =
      min ((arrival c t - arrival c u : K) : WithTop K) ((arrival c v - arrival c t : K) : WithTop K) := by
  apply le_antisymm
  · apply le_min
    · have hm : u ∈ (range N).filter (fun w => Greater c w t) :=
        mem_filter.mpr ⟨mem_range.mpr (by omega), (greater_of_lt hu).mpr hcu⟩
      have h1 : isolation c N t ≤ ((|arrival c u - arrival c t| : K) : WithTop K) :=
        Finset.inf_le (f := fun w => ((|arrival c w - arrival c t| : K) : WithTop K)) hm
      rwa [dist_of_le hc hu.le] at h1
    · have hm : v ∈ (range N).filter (fun w => Greater c w t) :=
        mem_filter.mpr ⟨mem_range.mpr hvN, (greater_of_gt hv).mpr hcv⟩
      have h1 : isolation c N t ≤ ((|arrival c v - arrival c t| : K) : WithTop K) :=
        Finset.inf_le (f := fun w => ((|arrival c w - arrival c t| : K) : WithTop K)) hm
      rwa [abs_sub_comm, dist_of_le hc hv.le] at h1
  · unfold isolation
    rw [Finset.le_inf_iff]
    intro w hw
    rw [mem_filter, mem_range] at hw
    rcases lt_trichotomy w t with hwt | rfl | hwt
    · refine le_trans (min_le_left _ _) (WithTop.coe_le_coe.mpr ?_)
      rw [dist_of_le hc hwt.le]
      linarith [left_nearest hc hlast hwt hw.2]
    · exact absurd hw.2 (greater_irrefl c w)
    · refine le_trans (min_le_right _ _) (WithTop.coe_le_coe.mpr ?_)
      rw [abs_sub_comm, dist_of_le hc hwt.le]
      linarith [right_nearest hc hfirst hwt hw.2]

/-- [proved-derived] Where no later place carries more, the isolation is the left side alone. -/
theorem isolation_eq_left {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N u t : ℕ} (htN : t < N)
    (hu : u < t) (hcu : c t ≤ c u) (hlast : ∀ x, u < x → x < t → c x < c t)
    (hnone : ∀ x, t < x → x < N → c x ≤ c t) :
    isolation c N t = ((arrival c t - arrival c u : K) : WithTop K) := by
  apply le_antisymm
  · have hm : u ∈ (range N).filter (fun w => Greater c w t) :=
      mem_filter.mpr ⟨mem_range.mpr (by omega), (greater_of_lt hu).mpr hcu⟩
    have h1 : isolation c N t ≤ ((|arrival c u - arrival c t| : K) : WithTop K) :=
      Finset.inf_le (f := fun w => ((|arrival c w - arrival c t| : K) : WithTop K)) hm
    rwa [dist_of_le hc hu.le] at h1
  · unfold isolation
    rw [Finset.le_inf_iff]
    intro w hw
    rw [mem_filter, mem_range] at hw
    rcases lt_trichotomy w t with hwt | rfl | hwt
    · refine WithTop.coe_le_coe.mpr ?_
      rw [dist_of_le hc hwt.le]
      linarith [left_nearest hc hlast hwt hw.2]
    · exact absurd hw.2 (greater_irrefl c w)
    · exact absurd ((greater_of_gt hwt).mp hw.2) (not_lt.mpr (hnone w hwt hw.1))

/-- [proved-derived] Where no earlier place carries as much, the isolation is the right side alone. -/
theorem isolation_eq_right {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N t v : ℕ}
    (hnone : ∀ x, x < t → c x < c t)
    (hv : t < v) (hvN : v < N) (hcv : c t < c v) (hfirst : ∀ x, t < x → x < v → c x ≤ c t) :
    isolation c N t = ((arrival c v - arrival c t : K) : WithTop K) := by
  apply le_antisymm
  · have hm : v ∈ (range N).filter (fun w => Greater c w t) :=
      mem_filter.mpr ⟨mem_range.mpr hvN, (greater_of_gt hv).mpr hcv⟩
    have h1 : isolation c N t ≤ ((|arrival c v - arrival c t| : K) : WithTop K) :=
      Finset.inf_le (f := fun w => ((|arrival c w - arrival c t| : K) : WithTop K)) hm
    rwa [abs_sub_comm, dist_of_le hc hv.le] at h1
  · unfold isolation
    rw [Finset.le_inf_iff]
    intro w hw
    rw [mem_filter, mem_range] at hw
    rcases lt_trichotomy w t with hwt | rfl | hwt
    · exact absurd ((greater_of_lt hwt).mp hw.2) (not_le.mpr (hnone w hwt))
    · exact absurd hw.2 (greater_irrefl c w)
    · refine WithTop.coe_le_coe.mpr ?_
      rw [abs_sub_comm, dist_of_le hc hwt.le]
      linarith [right_nearest hc hfirst hwt hw.2]

/-! ## The record's statements on the first round -/

/-- [proved-derived] **A landmark opens** (statement 1): a place that carries a section of news or more is a
site. -/
theorem landmark_opens {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N t : ℕ} {σ : K} (ht : t < N) (h : σ ≤ c t) :
    Site c N σ t := by
  refine ⟨ht, fun u _ hg hr => ?_⟩
  unfold Reaches at hr
  rcases lt_trichotomy u t with hut | rfl | hut
  · rw [dist_of_le hc hut.le] at hr
    linarith [arrival_add_le hc hut]
  · exact greater_irrefl c u hg
  · rw [abs_sub_comm, dist_of_le hc hut.le] at hr
    have := (greater_of_gt hut).mp hg
    linarith [arrival_add_le hc hut]

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The grain** (statement 2): two sites stand a section or more apart. -/
theorem sites_apart {c : ℕ → K} {N s t : ℕ} {σ : K} (hs : Site c N σ s) (ht : Site c N σ t) (hne : s ≠ t) :
    σ ≤ |arrival c s - arrival c t| := by
  rcases greater_total c hne with hg | hg
  · exact not_lt.mp (ht.2 s hs.1 hg)
  · rw [abs_sub_comm]
    exact not_lt.mp (hs.2 t ht.1 hg)

/-- [proved-derived] The grain in the passage's order: the later of two sites arrives a section or more after the
earlier. -/
theorem sites_apart_ordered {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N s t : ℕ} {σ : K}
    (hs : Site c N σ s) (ht : Site c N σ t) (hst : s < t) : σ ≤ arrival c t - arrival c s := by
  have h := sites_apart hs ht hst.ne
  rwa [dist_of_le hc hst.le] at h

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **One number a place** (statement 3): a site at a section is a site at every smaller one. -/
theorem site_antitone {c : ℕ → K} {N t : ℕ} {σ σ' : K} (h : σ ≤ σ') (hs : Site c N σ' t) : Site c N σ t :=
  ⟨hs.1, fun u hu hg hr => hs.2 u hu hg (lt_of_lt_of_le hr h)⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The greatest place is a site at every section** (R7). -/
theorem greatest_is_site {c : ℕ → K} {N t : ℕ} (ht : t < N) (h : ∀ u < N, ¬ Greater c u t) (σ : K) :
    Site c N σ t :=
  ⟨ht, fun u hu hg _ => h u hu hg⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **A site at every section:** a passage that holds a place holds a site of `P(σ)`, whatever
the section. -/
theorem exists_site (c : ℕ → K) {N : ℕ} (hN : 0 < N) (σ : K) : ∃ t, Site c N σ t := by
  obtain ⟨t, ht, h⟩ := exists_greatest c hN
  exact ⟨t, greatest_is_site ht h σ⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **Reach** (statement 4): if every place that reaches `t` in a second passage is a place of the
first with the same news and at the same distance from `t`, a site of the first is a site of the second. -/
theorem site_congr {c c' : ℕ → K} {N N' t : ℕ} {σ : K} (ht' : t < N') (hct : c' t = c t)
    (h : ∀ u < N', Reaches c' σ u t →
      u < N ∧ c u = c' u ∧ arrival c u - arrival c t = arrival c' u - arrival c' t) :
    Site c N σ t → Site c' N' σ t := by
  rintro ⟨_, hs⟩
  refine ⟨ht', fun u hu hg hr => ?_⟩
  obtain ⟨huN, hcu, hd⟩ := h u hu hr
  refine hs u huN ?_ ?_
  · unfold Greater at hg ⊢
    rw [hcu, ← hct]
    exact hg
  · unfold Reaches at hr ⊢
    rw [hd]
    exact hr

omit [IsStrictOrderedRing K] in
/-- [proved-derived] Reach, both ways: two passages that agree within a section of `t` agree on whether `t` is a
site. -/
theorem site_congr_iff {c c' : ℕ → K} {N N' t : ℕ} {σ : K} (ht : t < N) (ht' : t < N') (hct : c' t = c t)
    (h : ∀ u < N', Reaches c' σ u t →
      u < N ∧ c u = c' u ∧ arrival c u - arrival c t = arrival c' u - arrival c' t)
    (h' : ∀ u < N, Reaches c σ u t →
      u < N' ∧ c' u = c u ∧ arrival c' u - arrival c' t = arrival c u - arrival c t) :
    Site c N σ t ↔ Site c' N' σ t :=
  ⟨site_congr ht' hct h, site_congr ht hct.symm h'⟩

/-! ## The claim -/

/-- [definition] A set of places is the claim `G(σ)` of the passage: `t ∈ G` exactly when no greater place of `G`
reaches it. -/
def IsClaim (c : ℕ → K) (N : ℕ) (σ : K) (G : ℕ → Prop) : Prop :=
  ∀ t, G t ↔ t < N ∧ ∀ u < N, G u → Greater c u t → ¬ Reaches c σ u t

/-- [definition] A place's count of greater places in the passage. -/
def rank (c : ℕ → K) (N t : ℕ) : ℕ := ((range N).filter (fun u => Greater c u t)).card

omit [CommRing K] [IsStrictOrderedRing K] in
/-- [proved-derived] A greater place has fewer places greater than it: the claim's recursion is well-founded. -/
theorem rank_lt (c : ℕ → K) {N u t : ℕ} (hu : u < N) (hg : Greater c u t) : rank c N u < rank c N t := by
  unfold rank
  apply Finset.card_lt_card
  refine ⟨fun w hw => ?_, fun hsub => ?_⟩
  · rw [mem_filter] at hw ⊢
    exact ⟨hw.1, greater_trans hw.2 hg⟩
  · have hmem : u ∈ (range N).filter (fun w => Greater c w u) :=
      hsub (mem_filter.mpr ⟨mem_range.mpr hu, hg⟩)
    exact greater_irrefl c u (mem_filter.mp hmem).2

/-- [definition] The claim, by recursion on the order of news: the most first. -/
def claim (c : ℕ → K) (N : ℕ) (σ : K) : ℕ → Prop :=
  (InvImage.wf (rank c N) Nat.lt_wfRel.wf).fix (C := fun _ => Prop) fun t G =>
    t < N ∧ ∀ u (hu : u < N) (hg : Greater c u t), G u (rank_lt c hu hg) → ¬ Reaches c σ u t

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The claim exists:** the recursion satisfies the claim's equation. -/
theorem claim_isClaim (c : ℕ → K) (N : ℕ) (σ : K) : IsClaim c N σ (claim c N σ) := by
  intro t
  unfold claim
  conv_lhs => rw [WellFounded.fix_eq]
  constructor
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun u hu hG hg => h u hu hg hG⟩
  · rintro ⟨ht, h⟩
    exact ⟨ht, fun u hu hg hG => h u hu hG hg⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The claim is one set:** two sets that satisfy the claim's equation hold the same places. -/
theorem claim_unique {c : ℕ → K} {N : ℕ} {σ : K} {G G' : ℕ → Prop} (hG : IsClaim c N σ G)
    (hG' : IsClaim c N σ G') (t : ℕ) : G t ↔ G' t := by
  induction t using (InvImage.wf (rank c N) Nat.lt_wfRel.wf).induction with
  | _ t ih =>
    rw [hG t, hG' t]
    constructor
    · rintro ⟨ht, h⟩
      exact ⟨ht, fun u hu hGu hg => h u hu ((ih u (rank_lt c hu hg)).mpr hGu) hg⟩
    · rintro ⟨ht, h⟩
      exact ⟨ht, fun u hu hGu hg => h u hu ((ih u (rank_lt c hu hg)).mp hGu) hg⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The first round is inside the claim:** `P(σ) ⊆ G(σ)`. -/
theorem site_subset_claim {c : ℕ → K} {N t : ℕ} {σ : K} {G : ℕ → Prop} (hG : IsClaim c N σ G)
    (hs : Site c N σ t) : G t :=
  (hG t).mpr ⟨hs.1, fun u hu _ hg => hs.2 u hu hg⟩

omit [IsStrictOrderedRing K] in
/-- [proved-derived] The grain for the claim (statement 2): two sites of `G(σ)` stand a section or more apart. -/
theorem claim_sites_apart {c : ℕ → K} {N s t : ℕ} {σ : K} {G : ℕ → Prop} (hG : IsClaim c N σ G)
    (hs : G s) (ht : G t) (hne : s ≠ t) : σ ≤ |arrival c s - arrival c t| := by
  have hs' := (hG s).mp hs
  have ht' := (hG t).mp ht
  rcases greater_total c hne with hg | hg
  · exact not_lt.mp (ht'.2 s hs'.1 hs hg)
  · rw [abs_sub_comm]
    exact not_lt.mp (hs'.2 t ht'.1 ht hg)

omit [IsStrictOrderedRing K] in
/-- [proved-derived] Every place of the passage is a site of the claim or is reached by a greater one (statement
6's first half). -/
theorem claim_covers {c : ℕ → K} {N t : ℕ} {σ : K} {G : ℕ → Prop} (hG : IsClaim c N σ G) (ht : t < N) :
    G t ∨ ∃ u < N, G u ∧ Greater c u t ∧ Reaches c σ u t := by
  by_cases h : G t
  · exact Or.inl h
  · right
    by_contra hcon
    refine h ((hG t).mpr ⟨ht, fun u hu hGu hg hr => hcon ⟨u, hu, hGu, hg, hr⟩⟩)

omit [IsStrictOrderedRing K] in
/-- [proved-derived] **The stable core, one direction** (statement 5): a site of the first round is a site of the
claim of every passage that agrees with this one within a section of it. -/
theorem stable_core {c c' : ℕ → K} {N N' t : ℕ} {σ : K} {G' : ℕ → Prop} (hs : Site c N σ t)
    (ht' : t < N') (hct : c' t = c t)
    (h : ∀ u < N', Reaches c' σ u t →
      u < N ∧ c u = c' u ∧ arrival c u - arrival c t = arrival c' u - arrival c' t)
    (hG' : IsClaim c' N' σ G') : G' t :=
  site_subset_claim hG' (site_congr ht' hct h hs)

/-! ## Repeats and silence -/

/-- [proved-derived] **A repeat is dark** (statement 7): a place whose news equals the news one period earlier,
the period carrying less than a section, is no site: the earlier place is equal and earlier, and reaches. -/
theorem repeat_is_dark {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N p t : ℕ} {σ : K} (hp : 0 < p) (hpt : p ≤ t)
    (ht : t < N) (hrep : c (t - p) = c t) (hnews : arrival c t - arrival c (t - p) < σ) :
    ¬ Site c N σ t := by
  rintro ⟨_, hs⟩
  have hlt : t - p < t := by omega
  refine hs (t - p) (by omega) (Or.inr ⟨hrep, hlt⟩) ?_
  unfold Reaches
  rw [dist_of_le hc hlt.le]
  exact hnews

/-- [proved-derived] In a stretch `[a, b]` that repeats with period `p`, every period carries the first period's
news: `S_(v+p) − S_v = S_(a+p) − S_a`. -/
theorem period_news {c : ℕ → K} {a b p : ℕ} (hrep : ∀ v, a ≤ v → v + p ≤ b → c (v + p) = c v)
    {v : ℕ} (hav : a ≤ v) (hvb : v + p ≤ b) :
    arrival c (v + p) - arrival c v = arrival c (a + p) - arrival c a := by
  induction v, hav using Nat.le_induction with
  | base => rfl
  | succ v hav ih =>
    have h1 := ih (by omega)
    have h2 := hrep (v + 1) (by omega) hvb
    rw [show v + 1 + p = v + p + 1 by omega] at h2 ⊢
    rw [arrival_succ, arrival_succ, h2]
    linarith

/-- [proved-derived] **A stretch that repeats is dark past its first period** (statement 7): a site of the first
round inside a stretch that repeats with a period carrying less than a section stands in the stretch's first
period. -/
theorem sites_of_repeating_stretch {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N a b p t : ℕ} {σ : K} (hp : 0 < p)
    (hrep : ∀ v, a ≤ v → v + p ≤ b → c (v + p) = c v)
    (hnews : arrival c (a + p) - arrival c a < σ)
    (htb : t ≤ b) (hs : Site c N σ t) : t < a + p := by
  by_contra hcon
  have hpt : p ≤ t := by omega
  have hv : t - p + p = t := Nat.sub_add_cancel hpt
  have h1 := hrep (t - p) (by omega) (by omega)
  have h2 := period_news hrep (v := t - p) (by omega) (by omega)
  rw [hv] at h1 h2
  exact repeat_is_dark hc hp hpt hs.1 h1.symm (by rw [h2]; exact hnews) hs

/-- [proved-derived] So such a site stands less than a section after the stretch's start. -/
theorem site_near_start_of_repeat {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N a b p t : ℕ} {σ : K} (hp : 0 < p)
    (hrep : ∀ v, a ≤ v → v + p ≤ b → c (v + p) = c v)
    (hnews : arrival c (a + p) - arrival c a < σ)
    (htb : t ≤ b) (hs : Site c N σ t) : arrival c t - arrival c a < σ := by
  have hlt := sites_of_repeating_stretch hc hp hrep hnews htb hs
  linarith [arrival_mono hc hlt.le]

/-- [proved-derived] **Silence** (statement 8): a place that carries less than a section and no more than the
place before it is no site. -/
theorem faint_place_is_dark {c : ℕ → K} (hc : ∀ v, 0 ≤ c v) {N t : ℕ} {σ : K} (ht : t + 1 < N)
    (hle : c (t + 1) ≤ c t) (hσ : c (t + 1) < σ) : ¬ Site c N σ (t + 1) := by
  rintro ⟨_, hs⟩
  refine hs t (by omega) ((greater_of_lt (Nat.lt_succ_self t)).mpr hle) ?_
  unfold Reaches
  rw [dist_of_le hc (Nat.le_succ t), arrival_succ]
  linarith

omit [IsStrictOrderedRing K] in
/-- [proved-derived] A place of no news is greater than no place of positive news, so it bars no such site. -/
theorem zero_news_not_greater {c : ℕ → K} {z t : ℕ} (hz : c z = 0) (ht : 0 < c t) : ¬ Greater c z t := by
  rintro (h | ⟨h, _⟩)
  · rw [hz] at h
    exact lt_asymm h ht
  · rw [hz] at h
    exact ht.ne h

end Law

/-! ## Rulers, at an integer grain -/

/-- [definition] A passage of eight places, news `2, 1, 3, 1, 1, 2, 1, 4`, arriving at
`2, 3, 6, 7, 8, 10, 11, 15`. -/
def rulerNews : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | 2 => 3
  | 3 => 1
  | 4 => 1
  | 5 => 2
  | 6 => 1
  | 7 => 4
  | _ => 0

/-- [proved-derived] The ruler's sites at the section `2` are the places `0, 2, 5, 7`. -/
theorem ruler_sites_two : (range 8).filter (fun t => Site rulerNews 8 2 t) = {0, 2, 5, 7} := by
  decide

/-- [proved-derived] The ruler's sites at the section `5` are the places `2, 7`, among those at the section `2`. -/
theorem ruler_sites_five : (range 8).filter (fun t => Site rulerNews 8 5 t) = {2, 7} := by
  decide

/-- [proved-derived] The ruler's isolations: `4, 1, 9, 1, 1, 4, 1, ⊤`. -/
theorem ruler_isolations :
    (List.range 8).map (isolation rulerNews 8) =
      [((4 : ℤ) : WithTop ℤ), ((1 : ℤ) : WithTop ℤ), ((9 : ℤ) : WithTop ℤ), ((1 : ℤ) : WithTop ℤ),
        ((1 : ℤ) : WithTop ℤ), ((4 : ℤ) : WithTop ℤ), ((1 : ℤ) : WithTop ℤ), ⊤] := by
  decide

/-- [definition] News `30, 15, 9`: the record's unit in tenths, arriving at `30, 45, 54`. -/
def nestRuler : ℕ → ℤ
  | 0 => 30
  | 1 => 15
  | _ => 9

/-- [proved-derived] At the section `10` the claim of `30, 15, 9` is the first two places. -/
theorem nestRuler_claim_ten : IsClaim nestRuler 3 10 (fun t => t = 0 ∨ t = 1) := by
  intro t
  by_cases ht : t < 3
  · interval_cases t <;> decide
  · constructor
    · rintro (rfl | rfl) <;> omega
    · exact fun h => absurd h.1 ht

/-- [proved-derived] At the section `20` the claim of `30, 15, 9` is the first place and the third. -/
theorem nestRuler_claim_twenty : IsClaim nestRuler 3 20 (fun t => t = 0 ∨ t = 2) := by
  intro t
  by_cases ht : t < 3
  · interval_cases t <;> decide
  · constructor
    · rintro (rfl | rfl) <;> omega
    · exact fun h => absurd h.1 ht

/-- [counterexample] **The claim is not nested** (statement 3's second half): a passage and two sections
`σ ≤ σ′` with a site of `G(σ′)` that is no site of `G(σ)`. -/
theorem claim_not_nested :
    ∃ (c : ℕ → ℤ) (N : ℕ) (σ σ' : ℤ) (G G' : ℕ → Prop),
      σ ≤ σ' ∧ IsClaim c N σ G ∧ IsClaim c N σ' G' ∧ ∃ t, G' t ∧ ¬ G t :=
  ⟨nestRuler, 3, 10, 20, _, _, by norm_num, nestRuler_claim_ten, nestRuler_claim_twenty, 2, Or.inr rfl,
    by rintro (h | h) <;> omega⟩

/-- [definition] The record's own figures for that counterexample, news `3, 2, 1` in tenths. -/
def recordRuler : ℕ → ℤ
  | 0 => 30
  | 1 => 20
  | _ => 10

/-- [counterexample] On the clock of news the record's figures `3, 2, 1` arrive at `3, 5, 6`, and their claims
are nested: all three places at the section `1`, the first two at the section `2`. -/
theorem record_example_is_nested :
    IsClaim recordRuler 3 10 (fun t => t = 0 ∨ t = 1 ∨ t = 2) ∧
      IsClaim recordRuler 3 20 (fun t => t = 0 ∨ t = 1) := by
  constructor
  · intro t
    by_cases ht : t < 3
    · interval_cases t <;> decide
    · constructor
      · rintro (rfl | rfl | rfl) <;> omega
      · exact fun h => absurd h.1 ht
  · intro t
    by_cases ht : t < 3
    · interval_cases t <;> decide
    · constructor
      · rintro (rfl | rfl) <;> omega
      · exact fun h => absurd h.1 ht

end Holonics.Compression.Landmark.SiteIsolation

import Holonics.HNN.RingLoci

/-!
# HNN.WordDiamond: the word's opened diamond lies in every admitted collapse's retained set

[definition] #62 (owed by `HNN/JointStep`, receipt 5976863787: "a Lean statement that
`Reach::loci` lies within the collapse's retained set"). A deposit's reads past its own locus read
the loci of the word's opened diamond (`hnn::constitution::Reach::loci`). The Rust builds that set
as `Diamond::retained` of one diamond:

* at a comparison's deposit, `Diamond::opened(field, phases, opening.support(field))`
  (`hnn::reference`, the deposit beside `compose_return`): reach seeded at the source rings and at
  every ring the carried interior occupies, observe from the ratio's receiving ring, both run
  `phases.last_epoch()` rounds;
* at a contact's deposit, `Diamond::of(field, phases)` (`hnn::word::continuation`), the same with an
  empty support.

The collapse keeps `retention::retained(field, admitted, opens)`: every receiving map and the union
of `Diamond::admitted(field, phases, opens).retained(field)` over the admitted family, the declared
receivers from mount on (`Resident::mount_with`). Under the carry (`Opens::OnMotion`) each
admitted receiver's diamond is `Diamond::continuing`, both recursions closed (`|rings|` rounds) and
`e_last = 2|rings|`, which is `LocusMap.Retained S R (2|B|)` on the block graph (`JointStep`'s
`RUST S R`).

[proved-derived; formal-checked] What this file proves, for every epoch bound `e`:

1. **A seed the sources reach adds no reach** (`reach_lift`): a block within `j` hops of the seeds
   `S ∪ U`, every block of `U` reached from `S`, is within `|B| − 1` hops of `S`; and a block that
   observes a receiver of `Rw ⊆ R` observes `R` within `|B| − 1` hops (`observes_lift`).
2. **The word's opened diamond lies in the continuing collapse's retained set**
   (`opened_retained`): `Retained (S ∪ U) Rw e ℓ → Retained S R (2|B|) ℓ` for every base locus
   (element, junction, channel, conductance), every `e`, every carried support `U` the sources reach
   and every word receiver among the admitted ones; with the ring loci too (`opened_rust_retained`:
   a standing by its elements, a source port by its observe distance, a receiving map always).
3. **The carried support is reached from the sources** (`carried_support`, `pending_support`): a
   valid resident's carried change and every pending opening are zero off `reachAll S`
   (`TickStanding.Valid`), so the support `EndChange::support` reads satisfies 2's hypothesis.
4. **The word's diamonds are the retained set** (`word_diamond_retained`): the loci some opened
   diamond retains (`OpenedDiamond S R`, every `Retained (S ∪ U) Rw e` with `U ⊆ reachAll S`,
   `Rw ⊆ R`) are exactly `Retained S R (2|B|)`. `JointStep.certified_word_rust_unchanged` uses it
   to discharge `JointStep`'s `diam ⊆ keep`: with the joint reading's non-budget reads over the
   opened diamonds and the budget over the retained set, the Rust's collapse changes no admitted
   face and no staged deposit's joint reading, a refusal included.

At rest (`Opens::AtRest`) each admitted receiver keeps `Diamond::of` at its own `e_last`, and a
word's diamond is that diamond at the same phases when its receiver is admitted (`opened_mono`: the
retained set grows with `e` and with the receivers, so a word read at `e ≤ e_admitted` lies inside).

[agent-inferred] The Rust counts distances on the ring graph and the Lean on the block graph
(rings and contacts), where one contact hop is two block hops; the statements hold at every `e`,
so the inclusion does not depend on how `e_last` is scaled.

The computational object is the helical pair interaction's medium; of the winding guide's six
general objects this touches **faces and placement** (the retained loci, the receiver's faces) and
the **cell holonomy** only through the walks the diamond reads; the helix, the pair, the tube and
the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.WordDiamond

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.Word
open Holonics.HNN.LocusMap

universe u

/-! ## 1. Reach and observe from seeds the sources reach -/

section Walks

variable {B : Type*} [Fintype B] {adj : B → B → Prop}

/-- [proved-derived; formal-checked] **A seed the sources reach adds no reach**: a block within `j`
hops of `S ∪ U`, every block of `U` reached from `S`, is within `|B| − 1` hops of `S`. -/
theorem reach_lift {S U : Set B} (hU : U ⊆ reachAll adj S) {j : ℕ} {b : B}
    (hb : b ∈ reachWithin adj (S ∪ U) j) : b ∈ reachWithin adj S (Fintype.card B - 1) := by
  obtain ⟨x, hx, n, hn, hr⟩ := hb
  rcases hx with hx | hx
  · exact reachWithin_card S n ⟨x, hx, n, le_rfl, hr⟩
  · obtain ⟨t, x₀, hx₀, n₀, -, hr₀⟩ := hU hx
    exact reachWithin_card S (n₀ + n) ⟨x₀, hx₀, n₀ + n, le_rfl, hr₀.trans hr⟩

/-- [proved-derived; formal-checked] A block that observes a receiver of `Rw ⊆ R` observes `R`
within `|B| − 1` hops. -/
theorem observes_lift {Rw R : Set B} (hR : Rw ⊆ R) {y : B} {m : ℕ}
    (hy : Observes adj Rw y m) : Observes adj R y (Fintype.card B - 1) := by
  obtain ⟨ρ, hρ, n, hn, hr⟩ := hy
  exact observes_card ⟨ρ, hR hρ, n, hn, hr⟩

omit [Fintype B] in
/-- [proved-derived; formal-checked] The causal diamond grows with its seeds, its receivers and its
epoch bound. -/
theorem inDiamond_mono {S S' R R' : Set B} {e e' : ℕ} (hS : S ⊆ S') (hR : R ⊆ R') (he : e ≤ e')
    {z y : B} (h : InDiamond adj S R e z y) : InDiamond adj S' R' e' z y := by
  obtain ⟨j, m, ⟨x, hx, n, hn, hr⟩, ⟨ρ, hρ, k, hk, hr'⟩, hjm⟩ := h
  exact ⟨j, m, ⟨x, hS hx, n, hn, hr⟩, ⟨ρ, hR hρ, k, hk, hr'⟩, by omega⟩

end Walks

/-! ## 2. The word's diamond inside the continuing collapse -/

section Loci

variable {Ring Contact : Type u} [Fintype Ring] [Fintype Contact] {endRing : Contact × Bool → Ring}

local notation "N" => Fintype.card (Ring ⊕ Contact)

omit [Fintype Ring] [Fintype Contact] in
theorem reachWithin_seeds_mono {S S' : Set (Ring ⊕ Contact)} (hS : S ⊆ S') {j : ℕ}
    {b : Ring ⊕ Contact}
    (h : b ∈ reachWithin (blockAdj endRing) S j) : b ∈ reachWithin (blockAdj endRing) S' j := by
  obtain ⟨x, hx, n, hn, hr⟩ := h
  exact ⟨x, hS hx, n, hn, hr⟩

omit [Fintype Ring] [Fintype Contact] in
theorem observes_receivers_mono {R R' : Set (Ring ⊕ Contact)} (hR : R ⊆ R') {y : Ring ⊕ Contact}
    {m : ℕ} (h : Observes (blockAdj endRing) R y m) : Observes (blockAdj endRing) R' y m := by
  obtain ⟨ρ, hρ, n, hn, hr⟩ := h
  exact ⟨ρ, hR hρ, n, hn, hr⟩

/-- [proved-derived; formal-checked] **The word's opened diamond lies in the continuing collapse's
retained set** (`Reach::loci ⊆ retention::retained` under the carry): for every epoch bound `e`,
every carried support `U` the sources reach and every word receiver set `Rw` inside the admitted
receivers `R`, a locus the word's diamond retains (seeded at `S ∪ U`, observed from `Rw`) is one
the Rust's continuing collapse retains (`Retained S R (2|B|)`). -/
theorem opened_retained {S U Rw R : Set (Ring ⊕ Contact)} (hU : U ⊆ reachAll (blockAdj endRing) S)
    (hR : Rw ⊆ R) {e : ℕ} {ℓ : Locus Ring Contact} (h : Retained endRing (S ∪ U) Rw e ℓ) :
    Retained endRing S R (2 * N) ℓ := by
  cases ℓ with
  | element r =>
    obtain ⟨j, m, hz, hy, -⟩ := h
    have hpos : 0 < N := Fintype.card_pos_iff.mpr ⟨.inl r⟩
    exact ⟨N - 1, N - 1, reach_lift hU hz, observes_lift hR hy, by omega⟩
  | junction r =>
    obtain ⟨j, m, hz, hy, -⟩ := h
    have hpos : 0 < N := Fintype.card_pos_iff.mpr ⟨.inl r⟩
    exact ⟨N - 1, N - 1, reach_lift hU hz, observes_lift hR hy, by omega⟩
  | channel a =>
    obtain ⟨j, m, s, s', hz, hy, -⟩ := h
    have hpos : 0 < N := Fintype.card_pos_iff.mpr ⟨.inr a⟩
    exact ⟨N - 1, N - 1, s, s', reach_lift hU hz, observes_lift hR hy, by omega⟩
  | conductance a =>
    have hpos : 0 < N := Fintype.card_pos_iff.mpr ⟨.inr a⟩
    rcases h with ⟨j, m, s, s', hz, hy, -⟩ | ⟨s, j, m, hz, hy, -⟩
    · exact Or.inl ⟨N - 1, N - 1, s, s', reach_lift hU hz, observes_lift hR hy, by omega⟩
    · exact Or.inr ⟨s, N - 1, N - 1, reach_lift hU hz, observes_lift hR hy, by omega⟩

omit [Fintype Ring] [Fintype Contact] in
/-- [proved-derived; formal-checked] **The at-rest diamond grows with its seeds, receivers and
epoch bound** (`Opens::AtRest`: an admitted receiver keeps `Diamond::of` at its own `e_last`, and a
word read at the same receiver and at most that bound lies inside it). -/
theorem opened_mono {S S' R R' : Set (Ring ⊕ Contact)} (hS : S ⊆ S') (hR : R ⊆ R') {e e' : ℕ}
    (he : e ≤ e') {ℓ : Locus Ring Contact} (h : Retained endRing S R e ℓ) :
    Retained endRing S' R' e' ℓ := by
  cases ℓ with
  | element r => exact inDiamond_mono hS hR he h
  | junction r =>
    obtain ⟨j, m, hz, hy, hjm⟩ := h
    exact ⟨j, m, reachWithin_seeds_mono hS hz, observes_receivers_mono hR hy, by omega⟩
  | channel a =>
    obtain ⟨j, m, s, s', hz, hy, hjm⟩ := h
    exact ⟨j, m, s, s', reachWithin_seeds_mono hS hz, observes_receivers_mono hR hy, by omega⟩
  | conductance a =>
    rcases h with ⟨j, m, s, s', hz, hy, hjm⟩ | ⟨s, j, m, hz, hy, hjm⟩
    · exact Or.inl ⟨j, m, s, s', reachWithin_seeds_mono hS hz, observes_receivers_mono hR hy,
        by omega⟩
    · exact Or.inr ⟨s, j, m, reachWithin_seeds_mono hS hz, observes_receivers_mono hR hy,
        by omega⟩

/-- [proved-derived; formal-checked] **With the ring loci** (`RingLoci.RustRetained`, the Rust's
`Diamond::retains` with the standing, source port and receiving map): the word's opened diamond lies
in the continuing collapse's retained set. A standing is retained by an element, a source port by
its observe distance, which the admitted receivers keep within `|B| − 1`. -/
theorem opened_rust_retained {Src : Set Ring} {S U Rw R : Set (Ring ⊕ Contact)}
    (hU : U ⊆ reachAll (blockAdj endRing) S) (hR : Rw ⊆ R) {e : ℕ}
    {ℓ : RingLoci.RLocus Ring Contact} (h : RingLoci.RustRetained endRing Src (S ∪ U) Rw e ℓ) :
    RingLoci.RustRetained endRing Src S R (2 * N) ℓ := by
  cases ℓ with
  | base ℓ => exact opened_retained hU hR h
  | standing g =>
    rcases h with h | ⟨a, s, hs, h⟩
    · exact Or.inl (opened_retained hU hR h)
    · exact Or.inr ⟨a, s, hs, opened_retained hU hR h⟩
  | sourcePort g =>
    obtain ⟨hg, m, hm, -⟩ := h
    exact ⟨hg, N - 1, observes_lift hR hm, by omega⟩
  | receivingMap g => trivial

variable (endRing) in
/-- [definition] **Any word's opened diamond** (`Reach::loci` at every deposit the admitted family
can stage): the loci `Retained (S ∪ U) Rw e` retains for some epoch bound `e`, some carried support
`U` the sources reach and some word receivers `Rw` among the admitted `R`. -/
def OpenedDiamond (S R : Set (Ring ⊕ Contact)) (ℓ : Locus Ring Contact) : Prop :=
  ∃ U Rw e, U ⊆ reachAll (blockAdj endRing) S ∧ Rw ⊆ R ∧ Retained endRing (S ∪ U) Rw e ℓ

/-- [proved-derived; formal-checked] **Every word's diamond is retained**: `OpenedDiamond S R` lies
in the Rust's continuing collapse's retained set, and contains it (the word at rest with the
admitted receivers at `2|B|`), so the two are the same set. -/
theorem word_diamond_retained (S R : Set (Ring ⊕ Contact)) (ℓ : Locus Ring Contact) :
    OpenedDiamond endRing S R ℓ ↔ Retained endRing S R (2 * N) ℓ := by
  constructor
  · rintro ⟨U, Rw, e, hU, hR, h⟩
    exact opened_retained hU hR h
  · intro h
    refine ⟨∅, R, 2 * N, Set.empty_subset _, subset_rfl, ?_⟩
    rwa [Set.union_empty]

end Loci

/-! ## 3. The carried support -/

section Support

variable {B : Type*} {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con : Type*} {Ref : B → Type*} {Λ Mo : Type*}

/-- [proved-derived; formal-checked] **The carried interior's support is reached from the sources**
(`EndChange::support` on a valid resident): the blocks where the carried change is nonzero. -/
theorem carried_support {S : Set B} {res : TickStanding.TickResident K M Con Ref Λ Mo}
    (hv : TickStanding.Valid adj S res) :
    {b | res.carried.change b ≠ 0} ⊆ reachAll adj S := fun b hb => by
  by_contra h
  exact hb (hv.1 b h)

/-- [proved-derived; formal-checked] **Every pending word's opened support is reached from the
sources** (the opening a comparison's deposit reads, `WordOpening::support`). -/
theorem pending_support {S : Set B} {res : TickStanding.TickResident K M Con Ref Λ Mo}
    (hv : TickStanding.Valid adj S res) {p} (hp : p ∈ res.pending) :
    {b | p.opening.change b ≠ 0} ⊆ reachAll adj S := fun b hb => by
  by_contra h
  exact hb (hv.2 p hp b h)

end Support

end Holonics.HNN.WordDiamond

#print axioms Holonics.HNN.WordDiamond.reach_lift
#print axioms Holonics.HNN.WordDiamond.observes_lift
#print axioms Holonics.HNN.WordDiamond.opened_retained
#print axioms Holonics.HNN.WordDiamond.opened_mono
#print axioms Holonics.HNN.WordDiamond.opened_rust_retained
#print axioms Holonics.HNN.WordDiamond.word_diamond_retained
#print axioms Holonics.HNN.WordDiamond.carried_support
#print axioms Holonics.HNN.WordDiamond.pending_support

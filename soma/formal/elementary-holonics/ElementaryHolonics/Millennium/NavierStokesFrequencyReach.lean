import ElementaryHolonics.Millennium.NavierStokesFourierTriads
import ElementaryHolonics.Millennium.NavierStokesDyadicShellProjectors

/-!
# The periplus: relevance reaches the tail only shell by shell

The only nonlinear channel between frequency populations is the closed triad `p + q + k = 0`
(`NavierStokesFourierTriads.AddressedClosedFourierTriad`).  This owner proves that the channel has
finite reach.  Two modes addressed within cube radii `a` and `b` can feed a receiver only within
radius `a + b`; hence a mode beyond twice the band radius `N` has no triad with both legs in the
band, and the tail beyond `2N` is fed only through the tail.  Iterating, `m` interactions from the
band reach at most radius `2^m · N`.

This is the directionality Brandon named: the leader must step through the shells; there is no
any-to-any transfer.  Relevance propagates outward one face at a time, and the open obligation of
`NavierStokesTailRelevance.TailRelevanceControl` is exactly whether infinitely many shell steps can
be completed before the terminal time.  Nothing here bounds the cost of a step; it proves that the
steps exist and are ordered.
-/

namespace Soma.Holonics.Millennium.NavierStokesFrequencyReach

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads

theorem add_mem_frequencyCube {a b : ℕ} {p q : SpatialFrequency}
    (hp : p ∈ frequencyCube a) (hq : q ∈ frequencyCube b) :
    p + q ∈ frequencyCube (a + b) := by
  rw [mem_frequencyCube_iff] at hp hq ⊢
  intro coordinate
  have h1 := hp coordinate
  have h2 := hq coordinate
  simp only [Pi.add_apply]
  push_cast
  omega

theorem neg_mem_frequencyCube {a : ℕ} {p : SpatialFrequency} (hp : p ∈ frequencyCube a) :
    -p ∈ frequencyCube a := by
  rw [mem_frequencyCube_iff] at hp ⊢
  intro coordinate
  have h1 := hp coordinate
  simp only [Pi.neg_apply]
  omega

/-- **Finite reach of one closed triad.**  Legs within radii `a` and `b` feed a receiver only
within radius `a + b`. -/
theorem receiver_mem_frequencyCube_of_closed {a b : ℕ} {p q k : SpatialFrequency}
    (hclosed : p + q + k = 0) (hp : p ∈ frequencyCube a) (hq : q ∈ frequencyCube b) :
    k ∈ frequencyCube (a + b) := by
  have hk : k = -(p + q) := eq_neg_of_add_eq_zero_right hclosed
  rw [hk]
  exact neg_mem_frequencyCube (add_mem_frequencyCube hp hq)

/-- The same statement on Sol's addressed triad. -/
theorem AddressedClosedFourierTriad.receiver_mem {a b : ℕ}
    (triad : AddressedClosedFourierTriad)
    (hadvecting : triad.advecting ∈ frequencyCube a)
    (htransported : triad.transported ∈ frequencyCube b) :
    triad.receiver ∈ frequencyCube (a + b) :=
  receiver_mem_frequencyCube_of_closed triad.closed hadvecting htransported

/-- **The tail beyond twice the band is fed only through the tail.**  A receiver outside the cube
of radius `2N` has no closed triad with both legs inside the band of radius `N`. -/
theorem tail_fed_only_through_tail {N : ℕ} {p q k : SpatialFrequency}
    (hclosed : p + q + k = 0) (hk : k ∉ frequencyCube (2 * N)) :
    p ∉ frequencyCube N ∨ q ∉ frequencyCube N := by
  by_contra h
  push Not at h
  apply hk
  have := receiver_mem_frequencyCube_of_closed hclosed h.1 h.2
  rwa [← two_mul] at this

/-- The population reachable from the band of radius `N` in `m` closed-triad interactions. -/
def reach (N : ℕ) : ℕ → Set SpatialFrequency
  | 0 => (frequencyCube N : Set SpatialFrequency)
  | m + 1 => {k | ∃ p ∈ reach N m, ∃ q ∈ reach N m, p + q + k = 0}

/-- **Iterated reach is dyadic.**  `m` interactions from the band reach at most radius `2^m · N`:
the leader steps shell by shell. -/
theorem reach_subset_frequencyCube (N : ℕ) : ∀ m, reach N m ⊆ (frequencyCube (2 ^ m * N) : Set _)
  | 0 => by simp [reach]
  | m + 1 => by
    rintro k ⟨p, hp, q, hq, hclosed⟩
    have hp' := reach_subset_frequencyCube N m hp
    have hq' := reach_subset_frequencyCube N m hq
    have := receiver_mem_frequencyCube_of_closed hclosed hp' hq'
    have hpow : 2 ^ m * N + 2 ^ m * N = 2 ^ (m + 1) * N := by ring
    rwa [hpow] at this

section Audit

#print axioms receiver_mem_frequencyCube_of_closed
#print axioms tail_fed_only_through_tail
#print axioms reach_subset_frequencyCube

end Audit

end Soma.Holonics.Millennium.NavierStokesFrequencyReach

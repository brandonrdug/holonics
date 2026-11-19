import HolonicsResearch.HNN.GroupKeys

/-!
# A configuration breaks a contact on every frustrated loop, so a menu breaks at least its packing of disjoint frustrated loops

Sources: `HNN/GroupKeys` (atlas `key.group-holonomy-keys`), `Geometry/Frustration`,
`Geometry/TwistedCycle` (atlas `key.gauge-orbit`, `key.connection-cheeger`,
`key.twisted-cycle-square-root`); atlas `key.unique-games-frontier` and `contact.odd-alternation`,
which have no Lean owner; an outside reader's reply of November 19 (its blueprint "frustration
unicity": the bound for any group and the gauge fibre, the second of which
`GroupKeys.keys_eq_orbit` already holds for keys).

`GroupKeys` proves that a menu with a key closes every loop.  This module is the count on the other
side: a configuration that is not a key breaks contacts, and how many at least.

**What is proved.**

1. `Holds` [definition]: contact `e` holds under `x` when `x (tgt e) = g e · x (src e)`
   (`isKey_iff_holds`: a key is a configuration under which every contact holds).
2. `walk_transports_of_holds`: if every contact a walk uses holds, the configuration is carried
   along the walk, `x w = hol g ws · x u` (only the walk's own contacts are asked to hold).
3. `broken_on_frustrated_loop`: on a closed walk with `hol g ws ≠ 1`, every configuration breaks a
   contact the walk uses.
4. `packing_bound`: for a finite family of closed walks with nontrivial holonomy, no contact used by
   two of them, every configuration breaks at least as many contacts as the family has walks.
5. `holds_gauge`, `broken_gauge`: right multiplication by one element moves no contact between held
   and broken, so the broken set of `x` and of `gauge x k` are equal.
6. `odd_ring_breaks`: on the ring of `n` contacts (`ringContacts`, `i → i + 1` in `Fin n`), each carrying
   `−1 : ℤˣ`, `n` odd, every configuration breaks a contact (proved directly: the product of
   `x (i + 1) / x i` round the ring is `1`, while holding everywhere makes it `(−1)^n = −1`).
   `even_ring_has_key` is its counterexample in the other direction: for `n` even the alternating
   configuration breaks nothing.

[interpretation] A loop of contacts whose transports do not compose to the identity forces a slip
somewhere on it, whatever configuration is read; disjoint such loops force as many; the count is a
floor under what any section of the menu can close, and it is blind to the gauge.

**Limits.**  A lower bound only (the packing number is not the optimum in general).  Walks may
repeat a contact.  Nothing on finding the loops, on weights, or on the spectral reading (Cheeger),
which is `key.connection-cheeger`'s.

Computational object: the helical pair interaction; touches the pair (a contact's transport) and
the cell holonomy (a closed walk's product); the helix, faces and placement, the tube and the tower
thread stay attached.

**Consumers.**  The atlas rows `key.loop-packing-floor`, `key.unique-games-frontier` and
`contact.odd-alternation`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.LoopPacking

open Holonics.Geometry.Frustration Holonics.HNN.GroupKeys

variable {V E G : Type*} [Group G] (Γ : Contacts V E)

/-- [definition] **Contact `e` holds under the configuration `x`**: `x (tgt e) = g e · x (src e)`. -/
def Holds (g : E → G) (x : V → G) (e : E) : Prop := x (Γ.tgt e) = g e * x (Γ.src e)

variable {Γ}

/-- [definition] Whether a contact holds is decidable when equality in `G` is. -/
instance [DecidableEq G] (g : E → G) (x : V → G) : DecidablePred (Holds Γ g x) :=
  fun e => inferInstanceAs (Decidable (x (Γ.tgt e) = g e * x (Γ.src e)))

/-- [definition] Restated: a key is a configuration under which every contact holds. -/
theorem isKey_iff_holds (g : E → G) (x : V → G) : IsKey Γ g x ↔ ∀ e, Holds Γ g x e := Iff.rfl

/-- [proved-derived; formal-checked] A held contact carries the configuration across one step, along it or against it. -/
theorem holds_step {g : E → G} {x : V → G} {s : E × Bool} (hs : Holds Γ g x s.1) :
    x (stepTgt Γ s) = stepElt g s * x (stepSrc Γ s) := by
  obtain ⟨e, _ | _⟩ := s
  · simp only [stepTgt, stepSrc, stepElt]
    rw [hs, inv_mul_cancel_left]
  · exact hs

/-- [proved-derived; formal-checked] **A configuration is carried along a walk whose own contacts
hold**: `x w = hol g ws · x u`. -/
theorem walk_transports_of_holds {g : E → G} {x : V → G} :
    ∀ {u w : V} {ws : List (E × Bool)}, IsWalk Γ u ws w → (∀ s ∈ ws, Holds Γ g x s.1) →
      x w = hol g ws * x u
  | u, w, [], h, _ => by
      simp only [IsWalk] at h
      subst h
      simp [hol]
  | u, w, s :: ws, h, hh => by
      obtain ⟨hs, hrest⟩ := h
      rw [walk_transports_of_holds hrest fun s' hs' => hh s' (List.mem_cons_of_mem _ hs'),
        holds_step (hh s List.mem_cons_self), hs, hol, mul_assoc]

/-- [proved-derived; formal-checked] **A frustrated loop breaks a contact.**  On a closed walk whose
holonomy is not `1`, every configuration breaks a contact the walk uses. -/
theorem broken_on_frustrated_loop {g : E → G} (x : V → G) {u : V} {ws : List (E × Bool)}
    (hw : IsWalk Γ u ws u) (hol1 : hol g ws ≠ 1) : ∃ s ∈ ws, ¬ Holds Γ g x s.1 := by
  by_contra hno
  push Not at hno
  exact hol1 (mul_eq_right.mp (walk_transports_of_holds hw hno).symm)

/-- [proved-derived; formal-checked] **The packing bound.**  For a finite family of closed walks
with nontrivial holonomy, no contact used by two of them, every configuration breaks at least as
many contacts as the family has walks. -/
theorem packing_bound [Fintype E] [DecidableEq G] {κ : Type*} [Fintype κ] {g : E → G}
    (ws : κ → List (E × Bool)) (u : κ → V) (hw : ∀ i, IsWalk Γ (u i) (ws i) (u i))
    (hfr : ∀ i, hol g (ws i) ≠ 1)
    (hdisj : ∀ i j, i ≠ j → ∀ s ∈ ws i, ∀ s' ∈ ws j, s.1 ≠ s'.1) (x : V → G) :
    Fintype.card κ ≤
      (Finset.univ.filter fun e => ¬ Holds Γ g x e).card := by
  classical
  choose s hs hbr using fun i => broken_on_frustrated_loop x (hw i) (hfr i)
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn (fun i => (s i).1) (fun i _ => ?_) fun i _ j _ hij => ?_
  · simpa using hbr i
  · by_contra hne
    exact hdisj i j hne (s i) (hs i) (s j) (hs j) hij

/-- [proved-derived; formal-checked] **The gauge moves no contact between held and broken.** -/
theorem holds_gauge (g : E → G) (x : V → G) (k : G) (e : E) :
    Holds Γ g (gauge x k) e ↔ Holds Γ g x e := by
  simp only [Holds, gauge, ← mul_assoc, mul_left_inj]

/-- [proved-derived; formal-checked] **The broken set is blind to the gauge**: `x` and `gauge x k`
break the same contacts. -/
theorem broken_gauge [Fintype E] [DecidableEq G] (g : E → G) (x : V → G) (k : G) :
    (Finset.univ.filter fun e => ¬ Holds Γ g (gauge x k) e) =
      Finset.univ.filter fun e => ¬ Holds Γ g x e := by
  classical
  ext e
  simp [holds_gauge]

/-! ## The odd ring -/

/-- [definition] The ring of `n` contacts: contact `i` runs from port `i` to port `i + 1`. -/
def ringContacts (n : ℕ) [NeZero n] : Contacts (Fin n) (Fin n) := ⟨id, fun i => i + 1⟩

/-- [proved-derived; formal-checked] **An odd ring of sign-reversing contacts breaks a contact.**
On the ring of `n` contacts, each carrying `−1 : ℤˣ`, with `n` odd, every configuration breaks a
contact. -/
theorem odd_ring_breaks (n : ℕ) [NeZero n] (hn : Odd n) (x : Fin n → ℤˣ) :
    ∃ e, ¬ Holds (ringContacts n) (fun _ => (-1 : ℤˣ)) x e := by
  by_contra hno
  push Not at hno
  have hshift : ∏ i, x (i + 1) = ∏ i, x i :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ fun _ => rfl
  have hall : ∏ i, x (i + 1) = (-1) ^ n * ∏ i, x i := by
    rw [show ((-1 : ℤˣ) ^ n) = ∏ _i : Fin n, (-1 : ℤˣ) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin], ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hno i
  rw [hshift, hn.neg_one_pow] at hall
  have h1 : (-1 : ℤˣ) = 1 := (mul_eq_right.mp hall.symm)
  exact absurd h1 (by decide)

/-- [counterexample; formal-checked] **An even ring has a key**: for `n` even the alternating
configuration `(−1)^i` holds every contact, so `odd_ring_breaks` uses that `n` is odd. -/
theorem even_ring_has_key (n : ℕ) [NeZero n] (hn : Even n) :
    ∃ x : Fin n → ℤˣ, ∀ e, Holds (ringContacts n) (fun _ => (-1 : ℤˣ)) x e := by
  refine ⟨fun i => (-1) ^ (i : ℕ), fun e => ?_⟩
  simp only [Holds, ringContacts, id]
  rw [← pow_succ']
  rcases Nat.lt_or_ge ((e : ℕ) + 1) n with h | h
  · rw [Fin.val_add_one_of_lt' h]
  · have he : (e : ℕ) + 1 = n := le_antisymm (by omega) h
    rw [he, hn.neg_one_pow]
    have : e + 1 = 0 := by
      rw [Fin.ext_iff, Fin.val_add, Fin.val_one', Nat.add_mod_mod, he, Nat.mod_self, Fin.val_zero]
    rw [this, Fin.val_zero, pow_zero]

end Holonics.HNN.LoopPacking

section Audit

open Holonics.HNN.LoopPacking

#print axioms walk_transports_of_holds
#print axioms broken_on_frustrated_loop
#print axioms packing_bound
#print axioms holds_gauge
#print axioms broken_gauge
#print axioms odd_ring_breaks
#print axioms even_ring_has_key

end Audit

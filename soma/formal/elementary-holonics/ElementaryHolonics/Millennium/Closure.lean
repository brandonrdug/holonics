import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
# Closure: the return group is finite exactly when two mark families take turns, under every restretching

**The recognition instrument, ported to kernel grain: the decision is sorting integers, and the
anchors are `decide`-class — every classical row is computed by the test, never looked up.**

The Rust owner is `crates/holonic-engine/src/hypergeometric_closure.rs`, and this file rebuilds
its exact core rather than its report.  A second-order transport law on the plane with three
turning sites carries three dials `a, b, c`; the local turn numbers are `λ = 1 − c` at zero,
`μ = c − a − b` at one, `ν = a − b` at infinity.  Put the dials on a circle: the **numerator
family** is the pair of marks for `a` and `b`, the **denominator family** is the pair for `c` and
for the whole turn, which sits at position zero because a whole turn is no turn.  Over a common
denominator `N` every mark is an integer in `[0, N)`, so **no root is extracted, no angle is
taken, no matrix is built, and no float appears.**

The reading is: **the two families take turns around the circle — numerator, denominator,
numerator, denominator — with no two of one kind adjacent, and they must keep taking turns under
every restretching of the circle**, i.e. after multiplying every mark's position by any residue
sharing no factor with `N`.  Survive every restretching and the return group is finite and the
solution closes; fail one and it is infinite.  Classically this is the interlacing criterion of
Beukers–Heckman (*Invent. Math.* **95**, 1989), the restretchings being the Galois conjugates
indexed by the units mod `N`; the fifteen classically closing rows are Schwarz's list (1873).

**Measured absence, 2026-08-21:** `grep -rln "interlac\|Beukers" ElementaryHolonics/` → 0 and
`grep -rln "restretch\|Galois conjugat" ElementaryHolonics/` → 0, over the 55 `.lean` files that
`find ElementaryHolonics -name '*.lean'` reports.  `Reflection.lean` says of itself that *the
hypergeometric closure … remain[s] Rust-only; their Lean line is owed*, and `Chronology.lean`
that *nothing here formalizes a hypergeometric equation; only the closure shape*.  This file is
that owed line, and it takes only the combinatorial decision.

The wave's receiver question is **the reading equals the population**, and it is answered three
times over.  The reading *retains* the population: the sorted circle walk is a permutation of the
marks drawn, so it counts exactly `num.length + den.length` marks and exactly `num.length` of
them numerator ones — nothing is created and nothing is deleted by the sort.  The reading *walks*
exactly the population: the restretching family is exactly the units below the circle, and its
size is `Nat.totient N`, proved for every `N ≥ 2`.  And the reading is *indifferent to which
member of that population it is read from*: the closure predicate is invariant under every
restretching, so the verdict is not a fact about the frame the marks were drawn in.

What is proved:

* **the sorted walk is the drawn population, permuted** — `List.insertionSort` on positions, with
  its length and its numerator count both preserved, and the walk monotone in position, so
  "adjacent" means adjacent on the circle;
* **the restretching family is exactly the units below the circle**, and `(restretchings N).length
  = Nat.totient N` for every `N ≥ 2` — the count the test reports is the order of the unit group,
  not a loop bound;
* **restretching is a group action on the marks**: spinning by `k₁` then `k₂` is spinning by
  `k₁k₂ mod N`, the family is closed under that product, and every member is invertible in it;
* **the closure reading is restretching-invariant** — `closesOn N (spin N k num) (spin N k den) =
  closesOn N num den` for every unit `k`.  This is what makes "under every restretching" a
  receiver-family condition rather than a list of unrelated checks, and it is the frame
  independence the horizon law asks of any reading that crosses a boundary;
* **the anchors, all `decide`-class over ℕ, each re-verified in exact integer arithmetic before
  encoding**: four named classical rows close (tetrahedral, octahedral, icosahedral, and the
  equal-turn icosahedral row), and all fifteen rows of the classical table close; two triples fail
  *as drawn*, at multiplier one (the equal-quarter saddle, whose exhibited obstruction is the
  numerator pair `1, 3` on the circle of eight, and the elliptic row, whose turn numbers all
  vanish); **two triples alternate as drawn and fail only once spun** — `a = 1/30, b = 17/30,
  c = 1/2` survives multipliers `1` and `7` and dies at `11`, and `a = 1/30, b = 18/30, c = 1/2`
  dies at `7`; and two flat triples split rather than merely failing;
* **the drawn arrangement is the weak half**: closure implies alternation as drawn, and the
  converse is refuted by the two spun-only anchors, so the restretching loop is load-bearing and
  its agreement is not decorative;
* **the dials fed to the reading are forced by their turn numbers, not authored** — the exact
  rational derivation `c = 1 − λ`, `a = (1 − λ − μ + ν)/2`, `b = (1 − λ − μ − ν)/2` is proved to
  invert the turn reading, and each named anchor's fraction pair is proved over ℚ to be the one
  its classical turn triple determines;
* **the signed turn sum is `1 − 2b` exactly**, which is why a flat triple forces a dial to zero
  and so lands on the denominator family's mark at zero — the flat locus *is* the splitting locus.

**Refused / not claimed.**  No monodromy group is constructed, no representation is built, no
local solution is written down, and nothing here is a proof of the Beukers–Heckman criterion:
that alternation under every restretching is *equivalent* to finiteness of the return group is a
named-open proposition, parameterized by the finiteness predicate this file declines to build,
and it is never assumed.  The file owns the combinatorial decision procedure and its witnesses,
nothing above them.  No claim is made that the classical fifteen rows *exhaust* the closing
spherical table; the table is a control on the computed test, exactly as the Rust owner insists,
and a table consulted to classify its own rows would return the preimage of an authored field.
The third verdict species — a numerator mark landing on a denominator mark, so the equation
splits and the criterion does not apply — is returned by name and is neither "closes" nor "does
not close".  The geometry face (spherical, flat, saddle) is computed on absolute turn numbers and
is a quotient by the three-fork orientation word; it is stated here for the anchors only and
decides nothing.  Nothing about any Millennium problem is claimed.

Every theorem is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.Closure

/-! ## 1. The marks: exact fractions landed as integers on a common circle -/

/-- A dial as an exact fraction: an integer numerator over a natural denominator, carried as a
pair and never divided.  `ℚ` is deliberately not the computational carrier — its kernel
reduction gets stuck, measured, so every decided statement below runs on `ℤ` and `ℕ`. -/
abbrev Fraction : Type := ℤ × ℕ

/-- The fraction's denominator in lowest terms. -/
def reducedDen (f : Fraction) : ℕ := f.2 / Nat.gcd f.1.natAbs f.2

/-- The fraction's numerator in lowest terms. -/
def reducedNum (f : Fraction) : ℤ := f.1 / (Nat.gcd f.1.natAbs f.2 : ℤ)

/-- The mark a dial lands on, on a circle of `N` positions: reduce, rescale to the circle, and
take the residue in `[0, N)`.  A whole turn is no turn, which is why a negative dial lands where
its positive complement does. -/
def markOfFraction (N : ℕ) (f : Fraction) : ℕ :=
  (reducedNum f * ((N / reducedDen f : ℕ) : ℤ) % (N : ℤ)).toNat

/-- The smallest circle every dial lands on exactly: the least common multiple of the reduced
denominators.  The whole-turn mark contributes denominator one and is absorbed. -/
def circleOf (a b c : Fraction) : ℕ :=
  Nat.lcm (Nat.lcm (reducedDen a) (reducedDen b)) (reducedDen c)

/-- The numerator family: the marks for the two dials `a` and `b`. -/
def numeratorMarks (N : ℕ) (a b : Fraction) : List ℕ := [markOfFraction N a, markOfFraction N b]

/-- The denominator family: the whole turn, at position zero, and the mark for `c`. -/
def denominatorMarks (N : ℕ) (c : Fraction) : List ℕ := [0, markOfFraction N c]

/-- One mark on the circle: where it sits, and which family drew it. -/
structure Mark where
  /-- Its position on the circle, an integer in `[0, N)`. -/
  position : ℕ
  /-- Whether the numerator family drew it. -/
  fromNumerator : Bool
deriving DecidableEq, Repr

/-- The order the circle walk is taken in: by position alone.  Family never enters the order — a
tie *between* families is refused as a split before the walk is taken, and a tie *within* one
family is the adjacency being looked for either way. -/
def MarkLe (x y : Mark) : Prop := x.position ≤ y.position

instance : DecidableRel MarkLe := fun x y => inferInstanceAs (Decidable (x.position ≤ y.position))

instance : Std.Total MarkLe := ⟨fun x y => Nat.le_total x.position y.position⟩

instance : IsTrans Mark MarkLe := ⟨fun _ _ _ h₁ h₂ => Nat.le_trans h₁ h₂⟩

/-! ## 2. The alternation reading, and the population it retains -/

/-- The drawn marks, sorted into one walk around the circle. -/
def circleWalk (num den : List ℕ) : List Mark :=
  List.insertionSort MarkLe
    ((num.map fun p => ⟨p, true⟩) ++ (den.map fun p => ⟨p, false⟩))

/-- The walk's own successor list: the cyclic shift, so the last mark's neighbour is the first. -/
def rotateOne : List Mark → List Mark
  | [] => []
  | m :: rest => rest ++ [m]

/-- **The alternation predicate.**  Walk the circle once and require every mark's cyclic
successor to be drawn by the other family.  A lone mark is its own successor and therefore
fails, which is the correct reading rather than an edge case. -/
def alternates (ms : List Mark) : Bool :=
  (ms.zip (rotateOne ms)).all fun p => p.1.fromNumerator != p.2.fromNumerator

/-- The families take turns in the arrangement as drawn. -/
def alternatesAsDrawn (num den : List ℕ) : Bool := alternates (circleWalk num den)

/-- **The sorted walk is the drawn population, permuted.**  The reading rearranges; it neither
creates a mark nor deletes one. -/
theorem theWalkIsThePopulationPermuted (num den : List ℕ) :
    (circleWalk num den).Perm
      ((num.map fun p => ⟨p, true⟩) ++ (den.map fun p => ⟨p, false⟩)) :=
  List.perm_insertionSort _ _

/-- **The reading counts exactly the marks drawn** — the wave's receiver question at the grain
where it is checkable. -/
theorem theWalkCountsExactlyTheMarksDrawn (num den : List ℕ) :
    (circleWalk num den).length = num.length + den.length := by
  rw [(theWalkIsThePopulationPermuted num den).length_eq]
  simp

/-- **And it counts each family exactly.**  The numerator marks in the walk are exactly the
numerator marks drawn, so a family count read off the walk is a count of the realized population
and not of the reading's own bookkeeping. -/
theorem theNumeratorPopulationIsRetainedByTheReading (num den : List ℕ) :
    ((circleWalk num den).filter (·.fromNumerator)).length = num.length := by
  have hkeep : ∀ l : List ℕ,
      List.filter (fun x : Mark => x.fromNumerator) (l.map fun p => (⟨p, true⟩ : Mark))
        = l.map fun p => (⟨p, true⟩ : Mark) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih]
  have hdrop : ∀ l : List ℕ,
      List.filter (fun x : Mark => x.fromNumerator) (l.map fun p => (⟨p, false⟩ : Mark)) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih]
  rw [((theWalkIsThePopulationPermuted num den).filter _).length_eq, List.filter_append,
    List.length_append, hkeep, hdrop]
  simp

/-- **The walk is monotone in position**, so "adjacent in the walk" means adjacent on the circle
and the alternation predicate is reading the circle rather than a list order. -/
theorem theWalkIsMonotoneInPosition (num den : List ℕ) :
    (circleWalk num den).Pairwise MarkLe :=
  List.pairwise_insertionSort _ _

/-! ## 3. The restretching action -/

/-- Spin every mark by a multiplier and land it back on the circle. -/
def spin (N k : ℕ) (ms : List ℕ) : List ℕ := ms.map fun p => p * k % N

/-- The restretchings: the residues below the circle that share no factor with it.  Classically
the Galois conjugates; mechanically, spin the marks by a coprime multiple and look again. -/
def restretchings (N : ℕ) : List ℕ :=
  (List.range N).filter fun k => 0 < k && Nat.gcd k N == 1

/-- **The restretching family is exactly the units below the circle** — stated as a membership
condition so the family is a description of a population rather than a loop range. -/
theorem theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle (N k : ℕ) :
    k ∈ restretchings N ↔ 0 < k ∧ k < N ∧ Nat.gcd k N = 1 := by
  simp only [restretchings, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  tauto

/-- **The reading walks exactly the unit population**: the number of restretchings checked is the
order of the unit group mod `N`.  The count the test reports is a measured population, not an
aperture someone chose. -/
theorem theRestretchingCountIsTheUnitPopulation (N : ℕ) (hN : 2 ≤ N) :
    (restretchings N).length = Nat.totient N := by
  have bridge : Nat.totient N
      = ((List.range N).filter (fun m => decide (Nat.Coprime N m))).length := by
    unfold Nat.totient
    simp [Finset.filter, Finset.card, Finset.range, Multiset.range]
  rw [bridge, restretchings]
  congr 1
  apply List.filter_congr
  intro m hm
  rw [List.mem_range] at hm
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · have hz : ¬ Nat.Coprime N 0 := by
      simp only [Nat.Coprime, Nat.gcd_zero_right]
      omega
    simp [hz]
  · by_cases h : Nat.gcd m N = 1
    · have h' : Nat.Coprime N m := by
        unfold Nat.Coprime
        rw [Nat.gcd_comm]
        exact h
      simp only [hpos, decide_true, Bool.true_and, h, beq_self_eq_true]
      exact (decide_eq_true h').symm
    · have h' : ¬ Nat.Coprime N m := by
        unfold Nat.Coprime
        rw [Nat.gcd_comm]
        exact h
      have hL : (Nat.gcd m N == 1) = false := by simp [h]
      simp only [hpos, decide_true, Bool.true_and, hL, decide_eq_false h']

/-- **Restretching is an action**: spinning by `k₁` and then by `k₂` is spinning once, by the
product taken on the circle.  This is what makes the family of checks a group orbit. -/
theorem theRestretchingsCompose (N k₁ k₂ : ℕ) (ms : List ℕ) :
    spin N k₂ (spin N k₁ ms) = spin N (k₁ * k₂ % N) ms := by
  simp only [spin, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply]
  rw [Nat.mod_mul_mod, Nat.mul_mod_mod, Nat.mul_assoc]

/-- **The family is closed under its own product.** -/
theorem theRestretchingFamilyIsClosedUnderProduct (N k₁ k₂ : ℕ) (hN : 2 ≤ N)
    (h₁ : k₁ ∈ restretchings N) (h₂ : k₂ ∈ restretchings N) :
    k₁ * k₂ % N ∈ restretchings N := by
  rw [theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle] at h₁ h₂ ⊢
  have hcop : Nat.gcd (k₁ * k₂) N = 1 :=
    Nat.Coprime.mul_left (by simpa [Nat.Coprime] using h₁.2.2)
      (by simpa [Nat.Coprime] using h₂.2.2)
  have hrec : Nat.gcd (k₁ * k₂ % N) N = 1 := by
    have := Nat.gcd_rec N (k₁ * k₂)
    rw [Nat.gcd_comm N (k₁ * k₂)] at this
    omega
  refine ⟨?_, Nat.mod_lt _ (by omega), hrec⟩
  rcases Nat.eq_zero_or_pos (k₁ * k₂ % N) with hz | hp
  · rw [hz] at hrec
    simp only [Nat.gcd_zero_left] at hrec
    omega
  · exact hp

/-- **Every restretching is invertible inside the family.**  Classically: the Galois conjugates
form a group, so no member of the family is a privileged frame. -/
theorem theRestretchingIsInvertibleInTheFamily (N k : ℕ) (hN : 2 ≤ N)
    (hk : k ∈ restretchings N) :
    ∃ j ∈ restretchings N, k * j % N = 1 := by
  rw [theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle] at hk
  obtain ⟨j, hjlt, hj⟩ :=
    Nat.exists_mul_mod_eq_one_of_coprime (by simpa [Nat.Coprime] using hk.2.2) (by omega)
  have hprod : Nat.gcd (k * j) N = 1 := by
    have := Nat.gcd_rec N (k * j)
    rw [Nat.gcd_comm N (k * j), hj] at this
    simpa using this
  have hjcop : Nat.gcd j N = 1 :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left j k) (by simpa [Nat.Coprime] using hprod)
  refine ⟨j, ?_, hj⟩
  rw [theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle]
  refine ⟨?_, hjlt, hjcop⟩
  rcases Nat.eq_zero_or_pos j with rfl | hp
  · simp only [Nat.mul_zero, Nat.zero_mod] at hj
    omega
  · exact hp

/-! ## 4. The closure reading, and its indifference to the frame it is read from -/

/-- The families take turns under every restretching. -/
def alternatesUnderEveryRestretching (N : ℕ) (num den : List ℕ) : Bool :=
  (restretchings N).all fun k => alternatesAsDrawn (spin N k num) (spin N k den)

/-- **The closure reading**: a nonempty restretching family, every member of which alternates.
A circle admitting no restretching is refused rather than passed by default — alternation must
be put under a second frame or it has not been read at all. -/
def closesOn (N : ℕ) (num den : List ℕ) : Bool :=
  !(restretchings N).isEmpty && alternatesUnderEveryRestretching N num den

/-- Every restretching in the family maps onto the family by multiplication: the orbit of the
checks under one spin is the family itself. -/
theorem theSpunFamilyCoversTheFamily (N k : ℕ) (hN : 2 ≤ N) (hk : k ∈ restretchings N)
    (j : ℕ) (hj : j ∈ restretchings N) :
    ∃ i ∈ restretchings N, k * i % N = j := by
  obtain ⟨kinv, hkinv, hkk⟩ := theRestretchingIsInvertibleInTheFamily N k hN hk
  refine ⟨kinv * j % N, theRestretchingFamilyIsClosedUnderProduct N kinv j hN hkinv hj, ?_⟩
  have hjlt : j < N := ((theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle N j).mp hj).2.1
  calc k * (kinv * j % N) % N = k * (kinv * j) % N := Nat.mul_mod_mod _ _ _
    _ = k * kinv * j % N := by rw [Nat.mul_assoc]
    _ = (k * kinv % N) * j % N := (Nat.mod_mul_mod _ _ _).symm
    _ = j := by rw [hkk, Nat.one_mul, Nat.mod_eq_of_lt hjlt]

/-- **The closure reading is restretching-invariant.**  Reading the marks after a spin returns
what reading them as drawn returns: the verdict is not a fact about the frame the marks happened
to be drawn in.  This is the whole content of "under *every* restretching" — it makes the family
of checks one receiver-family condition instead of a list of unrelated ones. -/
theorem theClosureReadingIsRestretchingInvariant (N k : ℕ) (hN : 2 ≤ N)
    (hk : k ∈ restretchings N) (num den : List ℕ) :
    closesOn N (spin N k num) (spin N k den) = closesOn N num den := by
  unfold closesOn alternatesUnderEveryRestretching
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h j hj
    obtain ⟨i, hi, hik⟩ := theSpunFamilyCoversTheFamily N k hN hk j hj
    have := h i hi
    rwa [theRestretchingsCompose, theRestretchingsCompose, hik] at this
  · intro h j hj
    rw [theRestretchingsCompose, theRestretchingsCompose]
    exact h _ (theRestretchingFamilyIsClosedUnderProduct N k j hN hk hj)

/-- **Closure implies alternation as drawn**: the drawn arrangement is one member of the family,
so it is the weak half of the criterion.  The converse is refuted below by two anchors that
alternate as drawn and die once spun. -/
theorem theClosingReadingAlternatesAsDrawn (N : ℕ) (hN : 2 ≤ N) (num den : List ℕ)
    (hnum : ∀ p ∈ num, p < N) (hden : ∀ p ∈ den, p < N)
    (h : closesOn N num den = true) : alternatesAsDrawn num den = true := by
  have h1 : 1 ∈ restretchings N := by
    rw [theRestretchingFamilyIsExactlyTheUnitsBelowTheCircle]
    exact ⟨Nat.one_pos, by omega, Nat.gcd_one_left N⟩
  have hall : alternatesAsDrawn (spin N 1 num) (spin N 1 den) = true := by
    unfold closesOn alternatesUnderEveryRestretching at h
    rw [Bool.and_eq_true, List.all_eq_true] at h
    exact h.2 1 h1
  have hs : ∀ ms : List ℕ, (∀ p ∈ ms, p < N) → spin N 1 ms = ms := by
    intro ms hms
    unfold spin
    rw [List.map_congr_left (g := id) fun p hp => by
      simpa using Nat.mod_eq_of_lt (by simpa using hms p hp)]
    exact List.map_id ms
  rwa [hs num hnum, hs den hden] at hall

/-! ## 5. The verdict, with its three species -/

/-- What the alternation test returned.  Three species, not two: a numerator mark landing on a
denominator mark is outside the criterion's aperture and is returned by name. -/
inductive ClosureVerdict where
  /-- Every restretching alternated: the return group is finite and the solution closes. -/
  | closes
  /-- A restretching put two marks of one family next to each other; `1` means it failed as
  drawn, without needing any spin at all. -/
  | doesNotClose (failingRestretching : ℕ)
  /-- A numerator mark landed on a denominator mark, so the equation splits.  Neither verdict. -/
  | splits (coincidentMark : ℕ)
  /-- The circle admits no restretching, so alternation was never put under a second frame. -/
  | noRestretchingFamily
deriving DecidableEq, Repr

/-- **The decision.**  Split first, then require a nonempty restretching family, then return the
first multiplier whose spin broke the alternation — the exhibited obstruction, not a verdict. -/
def readClosure (N : ℕ) (num den : List ℕ) : ClosureVerdict :=
  match num.find? (fun p => den.contains p), (restretchings N).isEmpty,
      (restretchings N).find? fun k => !alternatesAsDrawn (spin N k num) (spin N k den) with
  | some p, _, _ => .splits p
  | none, true, _ => .noRestretchingFamily
  | none, false, some k => .doesNotClose k
  | none, false, none => .closes

/-- The reading entered by three dials: land them on their common circle and decide. -/
def readDials (a b c : Fraction) : ClosureVerdict :=
  readClosure (circleOf a b c) (numeratorMarks (circleOf a b c) a b)
    (denominatorMarks (circleOf a b c) c)

/-- **A closing verdict is the alternation reading and nothing else** — the verdict does not
carry information the reading did not produce. -/
theorem theClosingVerdictIsTheAlternationReading (N : ℕ) (num den : List ℕ)
    (h : readClosure N num den = ClosureVerdict.closes) : closesOn N num den = true := by
  unfold readClosure at h
  split at h
  · simp at h
  · simp at h
  · simp at h
  · rename_i hE hF
    unfold closesOn alternatesUnderEveryRestretching
    rw [hE]
    simp only [Bool.not_false, Bool.true_and]
    rw [List.all_eq_true]
    intro k hk
    simpa using List.find?_eq_none.mp hF k hk

/-! ## 6. The anchors

Every anchor below was re-verified in exact integer and rational arithmetic — `fractions.Fraction`
and `math.lcm`, no floats — before it was encoded, and each is discharged by kernel computation
rather than by a table lookup.  The classical table is a **control** on the computed test: a table
consulted to classify its own rows would return the preimage of an authored field. -/

/-- **The tetrahedral row closes.**  Turn numbers `(1/2, 1/3, 1/3)`; dials `1/4, −1/12, 1/2`;
circle twelve; numerator marks `3, 11` against denominator marks `0, 6`; four restretchings, all
alternating. -/
theorem theTetrahedralRowCloses :
    readDials (1, 4) (-1, 12) (1, 2) = ClosureVerdict.closes := by decide

/-- **The octahedral row closes.**  Turn numbers `(1/2, 1/3, 1/4)`; circle twenty-four; marks
`5, 23` against `0, 12`; eight restretchings. -/
theorem theOctahedralRowCloses :
    readDials (5, 24) (-1, 24) (1, 2) = ClosureVerdict.closes := by decide

/-- **The icosahedral row closes.**  Turn numbers `(1/2, 1/3, 1/5)`, whose absolute sum `31/30`
is the entire margin the sphere has; circle sixty; marks `11, 59` against `0, 30`; sixteen
restretchings, all alternating. -/
theorem theIcosahedralRowCloses :
    readDials (11, 60) (-1, 60) (1, 2) = ClosureVerdict.closes := by decide

/-- **The equal-turn icosahedral row closes.**  Turn numbers `(2/5, 2/5, 2/5)`; circle ten; marks
`3, 9` against `0, 6`; four restretchings. -/
theorem theEqualTurnIcosahedralRowCloses :
    readDials (3, 10) (-1, 10) (3, 5) = ClosureVerdict.closes := by decide

/-- The dials of the fifteen classically closing rows (Schwarz 1873), each pair derived from its
turn triple by the exact rational inversion below, none of them consulted by the test. -/
def classicalClosingTable : List (Fraction × Fraction × Fraction) :=
  [((1, 6), (-1, 6), (1, 2)), ((1, 4), (-1, 12), (1, 2)), ((1, 6), (-1, 6), (1, 3)),
   ((5, 24), (-1, 24), (1, 2)), ((1, 6), (-1, 12), (1, 3)), ((11, 60), (-1, 60), (1, 2)),
   ((3, 10), (-1, 30), (3, 5)), ((1, 6), (-1, 30), (1, 3)), ((3, 20), (-1, 20), (1, 2)),
   ((2, 15), (-1, 15), (2, 5)), ((3, 10), (-1, 10), (3, 5)), ((1, 10), (-1, 10), (1, 3)),
   ((1, 10), (-1, 10), (1, 5)), ((13, 60), (-7, 60), (1, 2)), ((1, 6), (-1, 6), (2, 5))]

/-- Whether a verdict is the closing species. -/
def isClosing : ClosureVerdict → Bool
  | .closes => true
  | _ => false

/-- **The table is a population of fifteen, and the test returns closing on every one of them.**
The reading equals the population: fifteen rows in, fifteen closing verdicts out, each computed
by the alternation test alone. -/
theorem theClassicalTableComputesAsClosingOnEveryRow :
    classicalClosingTable.length = 15 ∧
    (classicalClosingTable.map fun r => isClosing (readDials r.1 r.2.1 r.2.2)).count true = 15 := by
  constructor <;> decide

/-- **The equal-quarter saddle fails as drawn.**  Turn numbers `(1/4, 1/4, 1/4)`, absolute sum
`3/4 < 1`; dials `3/8, 1/8, 3/4`; circle eight; marks `3, 1` against `0, 6`, so the walk reads
`0` denominator, `1` numerator, `3` numerator, `6` denominator — the numerator pair `1, 3` sits
adjacent with no spin required, and the failing multiplier is one. -/
theorem theEqualQuarterSaddleFailsAsDrawn :
    readDials (3, 8) (1, 8) (3, 4) = ClosureVerdict.doesNotClose 1 ∧
    circleOf (3, 8) (1, 8) (3, 4) = 8 ∧
    numeratorMarks 8 (3, 8) (1, 8) = [3, 1] ∧
    denominatorMarks 8 (3, 4) = [0, 6] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The elliptic row fails as drawn**, and it is the standing negative control: its turn
numbers all vanish, its dials are `1/2, 1/2, 1`, and both denominator marks collapse onto zero,
so the walk carries a denominator pair with nothing between them. -/
theorem theEllipticRowFailsAsDrawn :
    readDials (1, 2) (1, 2) (1, 1) = ClosureVerdict.doesNotClose 1 ∧
    circleOf (1, 2) (1, 2) (1, 1) = 2 := by
  refine ⟨by decide, by decide⟩

/-- **The first spun-only refusal**: `a = 1/30, b = 17/30, c = 1/2`.  Its marks `1, 17` against
`0, 15` **alternate as drawn**, and they still alternate after the spin by seven; the family dies
at eleven, where the numerator marks land at `11` and `7` with both denominator marks at `0` and
`15` outside them.  Without material of this shape the restretching loop could be deleted and
every other anchor would still pass, which would make the second frame decorative. -/
theorem theFirstSpunOnlyRefusal :
    alternatesAsDrawn (numeratorMarks 30 (1, 30) (17, 30)) (denominatorMarks 30 (1, 2)) = true ∧
    alternatesAsDrawn (spin 30 7 (numeratorMarks 30 (1, 30) (17, 30)))
      (spin 30 7 (denominatorMarks 30 (1, 2))) = true ∧
    alternatesAsDrawn (spin 30 11 (numeratorMarks 30 (1, 30) (17, 30)))
      (spin 30 11 (denominatorMarks 30 (1, 2))) = false ∧
    readDials (1, 30) (17, 30) (1, 2) = ClosureVerdict.doesNotClose 11 := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **The second spun-only refusal**: `a = 1/30, b = 18/30, c = 1/2`, whose second dial reduces
to `3/5` and still lands on the circle of thirty.  Its marks `1, 18` against `0, 15` alternate as
drawn and die at the spin by seven. -/
theorem theSecondSpunOnlyRefusal :
    alternatesAsDrawn (numeratorMarks 30 (1, 30) (18, 30)) (denominatorMarks 30 (1, 2)) = true ∧
    alternatesAsDrawn (spin 30 7 (numeratorMarks 30 (1, 30) (18, 30)))
      (spin 30 7 (denominatorMarks 30 (1, 2))) = false ∧
    readDials (1, 30) (18, 30) (1, 2) = ClosureVerdict.doesNotClose 7 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **So alternation as drawn is strictly weaker than closure**, exhibited rather than asserted:
both spun-only anchors alternate in the frame they were drawn in and neither closes. -/
theorem theDrawnAlternationDoesNotDecideClosure :
    alternatesAsDrawn (numeratorMarks 30 (1, 30) (17, 30)) (denominatorMarks 30 (1, 2)) = true ∧
    closesOn 30 (numeratorMarks 30 (1, 30) (17, 30)) (denominatorMarks 30 (1, 2)) = false ∧
    alternatesAsDrawn (numeratorMarks 30 (1, 30) (18, 30)) (denominatorMarks 30 (1, 2)) = true ∧
    closesOn 30 (numeratorMarks 30 (1, 30) (18, 30)) (denominatorMarks 30 (1, 2)) = false := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- **Two flat triples split rather than merely failing to close.**  Turn numbers `(1/3, 1/3,
1/3)` and `(1/2, 1/4, 1/4)` each force a dial to zero, and a dial at zero lands on the
denominator family's whole-turn mark at zero.  A flat triple is outside the criterion, not
refused by it, and reporting it as a refusal would report the wrong species. -/
theorem theFlatTriplesSplitRatherThanRefuse :
    readDials (1, 3) (0, 1) (2, 3) = ClosureVerdict.splits 0 ∧
    readDials (1, 4) (0, 1) (1, 2) = ClosureVerdict.splits 0 := by
  refine ⟨by decide, by decide⟩

/-- **The restretching counts the anchors actually walked are the unit populations of their
circles**, computed both ways and agreeing. -/
theorem theAnchorRestretchingCountsAreTheUnitPopulations :
    (restretchings 12).length = Nat.totient 12 ∧
    (restretchings 24).length = Nat.totient 24 ∧
    (restretchings 60).length = Nat.totient 60 ∧
    (restretchings 30).length = Nat.totient 30 ∧
    (restretchings 8).length = Nat.totient 8 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide⟩

/-! ## 7. The dials are forced by their turn numbers, not authored -/

/-- The rational a fraction pair denotes. -/
def fractionValue (f : Fraction) : ℚ := (f.1 : ℚ) / (f.2 : ℚ)

/-- The first dial, read off the three local turn numbers. -/
def dialAOfTurns (l m n : ℚ) : ℚ := (1 - l - m + n) / 2

/-- The second dial, read off the three local turn numbers. -/
def dialBOfTurns (l m n : ℚ) : ℚ := (1 - l - m - n) / 2

/-- The third dial, read off the turn number at zero. -/
def dialCOfTurns (l : ℚ) : ℚ := 1 - l

/-- **The dials and the turn numbers are one reading from two sides**, exactly: `λ = 1 − c`,
`μ = c − a − b`, `ν = a − b` recovers the triple the inversion started from.  A `ring`-class
identity over ℚ, so the inversion is not an approximation of one. -/
theorem theTurnsAndTheDialsAreOneReadingFromTwoSides (l m n : ℚ) :
    1 - dialCOfTurns l = l ∧
    dialCOfTurns l - dialAOfTurns l m n - dialBOfTurns l m n = m ∧
    dialAOfTurns l m n - dialBOfTurns l m n = n := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (simp only [dialAOfTurns, dialBOfTurns, dialCOfTurns]; ring)

/-- **The signed turn sum is `1 − 2b` exactly.**  A `ring`-class identity, and it is why the flat
locus *is* the splitting locus: a turn sum of one forces the second dial to zero, and a dial at
zero lands on the denominator family's mark at zero, which is the coincidence that splits the
equation.  The flat anchors above are that identity, computed. -/
theorem theSignedTurnSumIsOneMinusTwiceTheSecondDial (a b c : ℚ) :
    (1 - c) + (c - a - b) + (a - b) = 1 - 2 * b := by ring

/-- **The four named anchors' dials are the ones their classical turn triples force**, proved
over ℚ so that no fraction pair fed to the reading above is authored.  Tetrahedral `(1/2,1/3,1/3)`,
octahedral `(1/2,1/3,1/4)`, icosahedral `(1/2,1/3,1/5)`, equal-turn icosahedral `(2/5,2/5,2/5)`. -/
theorem theAnchorDialsAreForcedByTheirTurnNumbers :
    (fractionValue (1, 4) = dialAOfTurns (1/2) (1/3) (1/3) ∧
      fractionValue (-1, 12) = dialBOfTurns (1/2) (1/3) (1/3) ∧
      fractionValue (1, 2) = dialCOfTurns (1/2)) ∧
    (fractionValue (5, 24) = dialAOfTurns (1/2) (1/3) (1/4) ∧
      fractionValue (-1, 24) = dialBOfTurns (1/2) (1/3) (1/4)) ∧
    (fractionValue (11, 60) = dialAOfTurns (1/2) (1/3) (1/5) ∧
      fractionValue (-1, 60) = dialBOfTurns (1/2) (1/3) (1/5)) ∧
    (fractionValue (3, 10) = dialAOfTurns (2/5) (2/5) (2/5) ∧
      fractionValue (-1, 10) = dialBOfTurns (2/5) (2/5) (2/5) ∧
      fractionValue (3, 5) = dialCOfTurns (2/5)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    (simp only [fractionValue, dialAOfTurns, dialBOfTurns, dialCOfTurns]; norm_num)

/-- **The geometry face, on the anchors only.**  The absolute turn sum against one: the
icosahedral row is spherical by the margin `31/30`, the equal-quarter saddle sums to `3/4`, and
the flat row sums to exactly `1`.  It is a magnitude face — the quotient by the three-fork
orientation word — and it decides nothing here. -/
theorem theAnchorGeometryFacesAreSphericalSaddleAndFlat :
    |(1 : ℚ)/2| + |(1 : ℚ)/3| + |(1 : ℚ)/5| = 31/30 ∧ (1 : ℚ) < 31/30 ∧
    |(1 : ℚ)/4| + |(1 : ℚ)/4| + |(1 : ℚ)/4| = 3/4 ∧ (3 : ℚ)/4 < 1 ∧
    |(1 : ℚ)/3| + |(1 : ℚ)/3| + |(1 : ℚ)/3| = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 8. What is left open, and never assumed -/

/-- **Beukers–Heckman**, named open and never assumed (*Invent. Math.* **95**, 1989).  For a
three-site turning equation whose numerator and denominator marks are disjoint on the circle, the
**return group is finite exactly when the two families alternate under every restretching**.

The statement is parameterized by `FiniteReturnGroup` because **this file constructs no monodromy
group**: it owns the combinatorial decision and its witnesses, and the predicate the criterion is
about is precisely the object it declines to build.  Instantiating this at the genuine
monodromy-finiteness predicate is the classical theorem; nothing here supplies it. -/
def TheAlternationDecidesTheReturnGroup
    (FiniteReturnGroup : ℕ → List ℕ → List ℕ → Prop) : Prop :=
  ∀ (N : ℕ) (num den : List ℕ), 2 ≤ N → (∀ p ∈ num, p ∉ den) →
    (FiniteReturnGroup N num den ↔ closesOn N num den = true)

/-- **A closing reading balances the two families**, named open: a cyclically alternating walk
must carry as many numerator marks as denominator ones, so a closure verdict already asserts an
equality of populations.  This is a statement about the definitions in this file and holds on
every anchor above by computation; the general proof over lists of arbitrary length is not
given. -/
def TheClosingReadingBalancesTheFamilies : Prop :=
  ∀ (N : ℕ) (num den : List ℕ), closesOn N num den = true → num.length = den.length

/-- **Alternation forces an even population**, named open: a walk whose every mark is followed
cyclically by the other family has exactly twice as many marks as numerator marks.  The reading
equals the population, in the sharpest form the file can state and does not prove. -/
def TheAlternatingWalkIsTwiceItsNumeratorPopulation : Prop :=
  ∀ ms : List Mark, alternates ms = true →
    2 * ((ms.filter (·.fromNumerator)).length) = ms.length

end Soma.Holonics.Millennium.Closure

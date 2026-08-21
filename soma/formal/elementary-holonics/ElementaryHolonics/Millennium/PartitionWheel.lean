import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The partition wheel: the shift is a radix, and its radical is where the criterion goes blind

`p(n)` is the number of partitions of `n`.  Newman's conjecture (M. Newman, 1960; **open**) asks
that every residue class mod every modulus be hit infinitely often.  Ono's route to it
(*Distribution of the partition function modulo m*, Annals of Mathematics **151** (2000), 293–307)
runs through a *good prime* condition carrying the literal shift `24`, because the partition
function enters the theory as the coefficient of `1/η(24z)` at index `24n − 1`.

**What is proved here, and most of it is `decide`-class.**  Ono's search index exists at all exactly
when the shift is a unit — `∃ n, 24 ∣ m·n + 1 ↔ gcd(m,24) = 1` — and when it exists the index it
produces satisfies `24·N ≡ 1 (mod m)`, so *Ono's progression is the Ramanujan progression and its
offset is forced*.  Every unit mod `24` squares to one, `24` is the largest modulus with that
property below `61`, and consequently Ono's exponent `(m^{2k} − 1)/24` is integral off the aperture.
Inside the aperture — at `m = 2` and `m = 3`, the radical of the shift — the criterion is not merely
hard but **refutable**: `¬ OnoGoodPrime 2` and `¬ OnoGoodPrime 3` are theorems here.

**The exact carrier.**  `p(n) mod m` is computed by Euler's pentagonal recurrence over a base-`2^w`
digit packing of the whole history, so every lookup is a shift and a mask on exact naturals and the
kernel can run it.  It is anchored two ways: against an independent brute-force enumeration of the
partitions themselves, and against the alternating sign count over partitions into distinct parts,
which is required to reproduce the same pentagonal coefficient table the recurrence uses.  Thirteen
is then exhibited as the smallest modulus at which Ono's criterion is both statable and satisfiable:
the progression `13t + 6` attains all thirteen residues for `t < 54` and not for `t < 53`, while
`5t + 4`, `7t + 5`, `11t + 6` return only zero across the checked reach.

**What this file does NOT claim.**  It does not move Newman's conjecture, which stays a named `Prop`
with real quantifiers; `m = 13` was settled by Atkin, Newman and Kolberg by 1960 and nothing here is
new mathematics.  It does not prove Euler's pentagonal number theorem, which mathlib does not carry
(measured: `grep -rln "pentagonal\|Pentagonal" Mathlib/ Archive/` under
`soma/formal/elementary-holonics/.lake/packages/mathlib`, 2026-08-21, returns nothing), so the link
from the computable wheel to `Fintype.card (Nat.Partition n)` is a **named hypothesis**, discharged
nowhere, and the two theorems that use it carry it explicitly in their statements.  It proves
nothing about half-integral weight forms, the Shimura correspondence, Galois representations or
Chebotarev — the machinery Ono's proof actually runs on.

**And the deed's own falsifier fires, so it is recorded rather than hidden.**  The reading "the
aperture is where the conjecture is open" is **false**: `m = 2` lies in the radical of the shift and
Newman's conjecture is nonetheless *true* there (Kolberg 1959; Radu, J. reine angew. Math. **672**
(2012), refines it to every arithmetic progression).  What the theorems below establish is the
weaker and exact statement that *this criterion* is blind inside the radical, which is close to
tautological given that the criterion has `24` written into it.  The residual open case at prime
moduli is `m = 3`, and no theorem here reaches it.

Every theorem is discharged and none depends on `sorryAx`.
-/

set_option maxRecDepth 100000

namespace Soma.Holonics.Millennium.PartitionWheel

/-! ## The aperture of the shift

Nothing in this section mentions partitions.  It is arithmetic about the number `24`, and it decides
where Ono's criterion can even be posed.
-/

/-- **Every unit modulo the shift squares to one.**  This is the fact that makes the shift's
aperture as large as it is, and it is the whole reason `(m² − 1)/24` is an integer for `m` coprime
to six. -/
theorem theShiftSquaresToOneOnEveryUnit (m : ℕ) (h : Nat.Coprime m 24) : m ^ 2 % 24 = 1 := by
  have key : ∀ r < 24, Nat.gcd r 24 = 1 → r ^ 2 % 24 = 1 := by decide
  have hr : m % 24 < 24 := Nat.mod_lt _ (by norm_num)
  have hg : Nat.gcd (m % 24) 24 = 1 := by
    have hrec : Nat.gcd 24 m = Nat.gcd (m % 24) 24 := Nat.gcd_rec 24 m
    rw [Nat.gcd_comm] at hrec
    rw [← hrec]; exact h
  rw [Nat.pow_mod]
  exact key _ hr hg

/-- **Ono's search index exists at all exactly when the shift is a unit.**  The condition
`m · n ≡ −1 (mod 24)` — the one that opens the good-prime definition — is solvable precisely when
`gcd(m, 24) = 1`, and the witness is explicit: `n = 23m` works, because `m² ≡ 1`. -/
theorem theOnoIndexExistsExactlyWhenTheShiftIsAUnit (m : ℕ) :
    (∃ n : ℕ, 24 ∣ m * n + 1) ↔ Nat.Coprime m 24 := by
  constructor
  · rintro ⟨n, hn⟩
    have h1 : Nat.gcd m 24 ∣ m * n := Dvd.dvd.mul_right (Nat.gcd_dvd_left m 24) n
    have h2 : Nat.gcd m 24 ∣ m * n + 1 := dvd_trans (Nat.gcd_dvd_right m 24) hn
    exact Nat.dvd_one.mp ((Nat.dvd_add_right h1).mp h2)
  · intro h
    obtain ⟨q, hq⟩ : ∃ q, m ^ 2 = 24 * q + 1 := ⟨m ^ 2 / 24, by
      have := theShiftSquaresToOneOnEveryUnit m h; omega⟩
    refine ⟨23 * m, 23 * q + 1, ?_⟩
    have hm : m * (23 * m) = 23 * m ^ 2 := by ring
    rw [hm, hq]; ring

/-- **And the index it produces is the shift's inverse.**  Writing `N = (m·n + 1)/24` gives
`24N = m·n + 1`, hence `24N ≡ 1 (mod m)` — so Ono's progression is `N ≡ 24⁻¹ (mod m)`, which is
exactly the Ramanujan progression. -/
theorem theIndexLandsAtTheShiftInverse (m n N : ℕ) (h : 24 * N = m * n + 1) :
    (24 : ZMod m) * (N : ZMod m) = 1 := by
  have hc := congrArg (fun x : ℕ => (x : ZMod m)) h
  push_cast at hc
  simpa [ZMod.natCast_self] using hc

/-- **The aperture is the radical of the shift.**  At `2` and `3` no index exists at all; at every
prime not dividing `24` one does.  Decided through the unit criterion, so these are unbounded
statements and not a search up to some ceiling. -/
theorem theApertureIsTheRadicalOfTheShift :
    (¬ ∃ n : ℕ, 24 ∣ 2 * n + 1) ∧ (¬ ∃ n : ℕ, 24 ∣ 3 * n + 1)
      ∧ (∃ n : ℕ, 24 ∣ 5 * n + 1) ∧ (∃ n : ℕ, 24 ∣ 7 * n + 1)
      ∧ (∃ n : ℕ, 24 ∣ 11 * n + 1) ∧ (∃ n : ℕ, 24 ∣ 13 * n + 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide
  · rw [theOnoIndexExistsExactlyWhenTheShiftIsAUnit]; decide

/-- **The shift's unit group has exponent two.**  `rfl`-class: decided by exhausting
`(ZMod 24)ˣ`. -/
theorem theShiftUnitGroupHasExponentTwo : ∀ u : (ZMod 24)ˣ, u ^ 2 = 1 := by decide

/-- **And the shift is maximal among moduli with that property, below sixty-one.**  `rfl`-class.
The moduli whose every unit squares to one are exactly the divisors of `24`; verified here as the
divisibility conclusion over the whole range `0 < n < 61`.  *This is a coincidence recorded without
a direction of causation: the `24` in `η` comes from `Δ = η²⁴` being the weight-twelve level-one
form, a fact about the modular group, not about `(ℤ/24)ˣ`.* -/
theorem theShiftIsMaximalAmongSuchModuli :
    ∀ n < 61, 0 < n → (∀ a < n, Nat.gcd a n = 1 → a ^ 2 % n = 1) → n ∣ 24 := by decide

/-- **Ono's exponent is integral off the aperture.**  `δ(m,k) = (m^{2k} − 1)/24` is a natural number
whenever `m` is coprime to the shift, for every `k`. -/
theorem theOnoExponentIsIntegralOffTheAperture (m k : ℕ) (h : Nat.Coprime m 24) :
    24 ∣ m ^ (2 * k) - 1 := by
  have hm : m ^ (2 * k) % 24 = 1 := by
    rw [pow_mul, Nat.pow_mod, theShiftSquaresToOneOnEveryUnit m h, one_pow]
    norm_num
  have h1 : 1 ≤ m ^ (2 * k) := Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    obtain ⟨rfl, -⟩ := Nat.pow_eq_zero.mp hz
    simp [Nat.Coprime] at h)
  omega

/-- **The offset is forced by the modulus law; the vanishing is not.**  `24⁻¹` mod
`5, 7, 11, 13, 17, 19, 23` is `4, 5, 6, 6, 5, 4, 1`.  Ramanujan's offsets `4, 5, 6` at `5, 7, 11`
are exactly the first three.  **At thirteen the offset is still `6` and no congruence holds** — so
the modulus law reaches the offset and stops there. -/
theorem theOffsetIsForcedButTheVanishingIsNot :
    (24 * 4 : ZMod 5) = 1 ∧ (24 * 5 : ZMod 7) = 1 ∧ (24 * 6 : ZMod 11) = 1
      ∧ (24 * 6 : ZMod 13) = 1 ∧ (24 * 5 : ZMod 17) = 1 ∧ (24 * 4 : ZMod 19) = 1
      ∧ (24 * 1 : ZMod 23) = 1 := by decide

/-! ## The exact carrier

`p(n)` is computed by Euler's pentagonal recurrence

`p(n) = Σ_{k ≥ 1} (−1)^{k+1} [ p(n − k(3k−1)/2) + p(n − k(3k+1)/2) ]`,

with the whole history packed into one natural number as base-`2^w` digits, so that reading
`p(n − g)` is a shift and a mask.  Every operation is on exact naturals; nothing is approximated and
no float appears.

**The encoding carries a boundary and it is stated rather than assumed.**  A digit must fit in `w`
bits.  For the modular runs below `w = 4` and the moduli are at most `13`, so digits are at most
`12 < 16`.  For the exact run `w = 32` and the values are `p(n) < 2^32`, which holds for `n ≤ 127`;
the exact table below stops far short of that.
-/

/-- The `i`-th base-`2^w` digit of `s`. -/
def digitAtBase (w s i : ℕ) : ℕ := (s >>> (w * i)) % 2 ^ w

/-- The generalized pentagonal gaps not exceeding `n`, each tagged `true` when its index `k` is odd,
which is when the recurrence adds rather than subtracts. -/
def pentagonalGaps (n : ℕ) : List (ℕ × Bool) :=
  (List.range (n + 1)).flatMap (fun j =>
    let k := j + 1
    let g₁ := k * (3 * k - 1) / 2
    let g₂ := k * (3 * k + 1) / 2
    (if g₁ ≤ n then [(g₁, decide (k % 2 = 1))] else []) ++
      (if g₂ ≤ n then [(g₂, decide (k % 2 = 1))] else []))

/-- The added and subtracted halves of one recurrence step, read out of the packed history. -/
def gapSums (w s n : ℕ) (ts : List (ℕ × Bool)) : ℕ × ℕ :=
  ts.foldl (fun a t =>
    if t.1 ≤ n then
      (if t.2 then (a.1 + digitAtBase w s (n - t.1), a.2)
       else (a.1, a.2 + digitAtBase w s (n - t.1)))
    else a) (0, 0)

/-- The signed difference of the two halves, reduced.  Modulus `0` means *no reduction*, matching
`ZMod 0 = ℤ`, and is how the exact values are obtained. -/
def reduceDifference (m a b : ℕ) : ℕ := if m = 0 then a - b else (a % m + (m - b % m)) % m

/-- The packed history of `p(0), …, p(n)` reduced mod `m`, as base-`2^w` digits. -/
def wheelFold (w m : ℕ) (ts : List (ℕ × Bool)) (n : ℕ) : ℕ :=
  (List.range n).foldl (fun s i =>
    let j := i + 1
    let ab := gapSums w s j ts
    s + (reduceDifference m ab.1 ab.2) <<< (w * j)) (1 % m)

/-- The packed history at width `w` and modulus `m`, out to index `n`. -/
def wheelState (w m n : ℕ) : ℕ := wheelFold w m (pentagonalGaps n) n

/-- `p(n) mod m`, at digit width `w`. -/
def partitionWheel (w m n : ℕ) : ℕ := digitAtBase w (wheelState w m n) n

/-- `p(n)` itself, at digit width thirty-two. -/
def partitionExact (n : ℕ) : ℕ := partitionWheel 32 0 n

/-! ### The independent anchor

The recurrence is not trusted on its own.  A second, structurally unrelated computation enumerates
the partitions as non-increasing lists and counts them, and the two are required to agree.
-/

/-- Every non-increasing list of positive parts summing to `n`, with no part exceeding `b`.
The first argument is fuel; each step consumes at least one. -/
def partsAtMost : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, 0, _ => [[]]
  | f + 1, n + 1, b =>
      (List.range' 1 (min (n + 1) b)).flatMap (fun k =>
        (partsAtMost f (n + 1 - k) k).map (fun t => k :: t))

/-- The brute-force enumeration of the partitions of `n`. -/
def partitionsOf (n : ℕ) : List (List ℕ) := partsAtMost (n + 1) n n

/-- The same with strictly decreasing parts. -/
def distinctAtMost : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, 0, _ => [[]]
  | f + 1, n + 1, b =>
      (List.range' 1 (min (n + 1) b)).flatMap (fun k =>
        (distinctAtMost f (n + 1 - k) (k - 1)).map (fun t => k :: t))

/-- The brute-force enumeration of the partitions of `n` into distinct parts. -/
def distinctPartitionsOf (n : ℕ) : List (List ℕ) := distinctAtMost (n + 1) n n

/-- The alternating sign count over partitions into distinct parts — the coefficient face of
`∏(1 − qⁿ)`. -/
def distinctNet (n : ℕ) : ℤ :=
  ((distinctPartitionsOf n).map (fun t => (-1 : ℤ) ^ t.length)).sum

/-- The Euler coefficient the recurrence is built from: `(−1)^k` at the generalized pentagonal
number `k(3k∓1)/2`, and zero everywhere else. -/
def eulerCoeff (n : ℕ) : ℤ :=
  if n = 0 then 1
  else match (pentagonalGaps n).find? (fun t => t.1 == n) with
    | some t => if t.2 then -1 else 1
    | none => 0

/-- **The enumeration is sound at ten.**  `rfl`-class.  Every listed object really is a
non-increasing list of positive parts summing to ten, and no object is listed twice.  *Completeness
is by construction and is not proved: the recursion admits every part from one to the current bound,
so nothing can be missed, but that is an argument about the definition rather than a theorem.* -/
theorem theEnumerationIsSoundAtTen :
    (∀ t ∈ partitionsOf 10, t.sum = 10 ∧ t.Pairwise (· ≥ ·) ∧ ∀ x ∈ t, 0 < x)
      ∧ (partitionsOf 10).Nodup := by
  refine ⟨by decide, by decide⟩

/-- **The distinct enumeration is sound at ten.**  `rfl`-class, same reading. -/
theorem theDistinctEnumerationIsSoundAtTen :
    (∀ t ∈ distinctPartitionsOf 10, t.sum = 10 ∧ t.Pairwise (· > ·))
      ∧ (distinctPartitionsOf 10).Nodup := by
  refine ⟨by decide, by decide⟩

/-- **The recurrence returns the known partition numbers.**  `rfl`-class. -/
theorem theWheelReturnsTheKnownValues :
    (List.range 13).map partitionExact = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77] := by
  decide

/-- **And the brute-force enumeration returns the same table.**  `rfl`-class, and this is the
anchor: two computations sharing no structure land on one list. -/
theorem theEnumerationReturnsTheSameValues :
    (List.range 13).map (fun n => (partitionsOf n).length)
      = [1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77] := by
  decide

/-- **The population is not the net.**  `rfl`-class.  Partitions of `n` into distinct parts number
`1,1,1,2,2,3,4,5,6,8,10,12,15` for `n ≤ 12` while their alternating sign counts are
`1,−1,−1,0,0,1,0,1,0,0,0,0,−1`.  *The lacunarity of `∏(1 − qⁿ)` is a total cancellation of a sign
population, not an absence of material.*  **This is an illustration and not an audit** — an
alternating sum having more terms than its value is true of every alternating sum, and no claim
about `p(n)` is separated by it. -/
theorem thePopulationIsNotTheNet :
    (List.range 13).map (fun n => (distinctPartitionsOf n).length)
        = [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15]
      ∧ (List.range 13).map distinctNet = [1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1] := by
  refine ⟨by decide, by decide⟩

/-- **The sign count reproduces the recurrence's own coefficient table.**  `rfl`-class, and this is
the load-bearing half of the pentagonal reading: the gaps and signs the recurrence runs on are not
authored, they are what the brute-force sign count over distinct partitions returns. -/
theorem theEulerCoefficientIsTheDistinctNet :
    (List.range 13).map distinctNet = (List.range 13).map eulerCoeff := by decide

/-! ## The three strata

The progression `N ≡ 24⁻¹ (mod m)` is empty inside the radical of the shift, returns only zero at
`5, 7, 11`, and returns everything from `13` upward.  Only the first two are tables.
-/

/-- The packed history mod thirteen out to the index the witness table needs. -/
def thirteenWheel : ℕ := wheelState 4 13 695

/-- `p(13t + 6) mod 13` for `t < 54`. -/
def thirteenResidues : List ℕ :=
  (List.range 54).map (fun t => digitAtBase 4 thirteenWheel (13 * t + 6))

/-- `p(5t + 4) mod 5` for `t < 50`. -/
def fiveResidues : List ℕ :=
  (List.range 50).map (fun t => digitAtBase 4 (wheelState 4 5 249) (5 * t + 4))

/-- `p(7t + 5) mod 7` for `t < 50`. -/
def sevenResidues : List ℕ :=
  (List.range 50).map (fun t => digitAtBase 4 (wheelState 4 7 348) (7 * t + 5))

/-- `p(11t + 6) mod 11` for `t < 50`. -/
def elevenResidues : List ℕ :=
  (List.range 50).map (fun t => digitAtBase 4 (wheelState 4 11 545) (11 * t + 6))

/-- **The saturated stratum returns only zero, across the checked reach.**  `rfl`-class.
`p(5t+4) ≡ 0 (5)`, `p(7t+5) ≡ 0 (7)`, `p(11t+6) ≡ 0 (11)` for every `t < 50` — Ramanujan's three
congruences, on the progressions the modulus law forces.  *The reach is fifty terms each; nothing
here proves the congruences, and Ahlgren–Boylan's theorem that these three exhaust their shape is
imported below, not established.* -/
theorem theSaturatedStratumReturnsOnlyZero :
    fiveResidues = List.replicate 50 0
      ∧ sevenResidues = List.replicate 50 0
      ∧ elevenResidues = List.replicate 50 0 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **And the stratum fails at thirteen at the first five terms.**  `rfl`-class.  The offset is the
same `24⁻¹ = 6` the law forces, and the progression opens `11, 9, 3, 6, 12` — five distinct nonzero
classes before anything else happens. -/
theorem theStratumFailsAtThirteenImmediately :
    thirteenResidues.take 5 = [11, 9, 3, 6, 12] := by decide

/-- **Every residue mod thirteen is attained on the progression below fifty-four.**  `rfl`-class,
and this is the deed: the smallest modulus at which Ono's criterion is both statable — `13` is
coprime to the shift — and satisfiable. -/
theorem theThirteenProgressionIsSurjectiveBelowFiftyFour :
    ∀ r < 13, r ∈ thirteenResidues := by decide

/-- **And fifty-four is sharp.**  `rfl`-class: the first fifty-three terms miss a class, so the
largest first-attainment index really is `N = 13·53 + 6 = 695`. -/
theorem theThirteenTableIsSharpAtFiftyFour :
    ¬ (∀ r < 13, r ∈ thirteenResidues.take 53) := by decide

/-! ## What is imported, and what stays open

Each of the following is a real statement with real quantifiers.  None is proved here, and none is
`True` wearing a name.  `partitionCount` is mathlib's combinatorial partition count, which is the
object all of these are about; the computable wheel above is joined to it only through the named
hypothesis `TheWheelCarriesThePartitionFunctionAtThirteen`.
-/

/-- The partition function, as mathlib defines it. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- **Newman's conjecture** (M. Newman, 1960).  **OPEN.**  At prime moduli the residual case is
`m = 3`: Ahlgren–Boylan settled every other prime, and Ono's own computation covered every prime
below one thousand except three. -/
def NewmanConjecture : Prop :=
  ∀ m : ℕ, 0 < m → ∀ r : ZMod m, {n : ℕ | (partitionCount n : ZMod m) = r}.Infinite

/-- **Ono's good-prime condition** (Ono 2000, p. 295): every residue is reached on the progression
the shift admits. -/
def OnoGoodPrime (m : ℕ) : Prop :=
  ∀ r : ZMod m, ∃ n : ℕ, 24 ∣ m * n + 1 ∧ (partitionCount ((m * n + 1) / 24) : ZMod m) = r

/-- **Ono's Theorem 3**: a good prime satisfies Newman's conjecture.  A theorem (Ono, Annals **151**
(2000), 293–307), proved by placing the generating functions in one of two half-integral weight
cusp form spaces with Nebentypus, then applying the Shimura correspondence, Serre's theorem on
Galois representations, and Chebotarev.  Imported here, established nowhere in this file. -/
def OnoCriterion : Prop :=
  ∀ m : ℕ, m.Prime → 5 ≤ m → OnoGoodPrime m →
    ∀ r : ZMod m, {n : ℕ | (partitionCount n : ZMod m) = r}.Infinite

/-- **The hole in this file's carrier chain, named.**  The wheel runs Euler's pentagonal recurrence;
that the recurrence computes `p(n)` is Euler's pentagonal number theorem, which mathlib does not
carry.  Rather than assume it silently, the finite instance actually needed is stated here and
carried as a hypothesis by the two theorems below. -/
def TheWheelCarriesThePartitionFunctionAtThirteen : Prop :=
  ∀ t < 54, (partitionCount (13 * t + 6) : ZMod 13)
    = ((digitAtBase 4 thirteenWheel (13 * t + 6) : ℕ) : ZMod 13)

/-- **The brute-force enumeration exhausts the partitions.**  True and unproved here: a bijection
between non-increasing lists and `Nat.Partition` is real work this file does not do. -/
def TheEnumerationExhaustsThePartitions : Prop :=
  ∀ n : ℕ, (partitionsOf n).length = partitionCount n

/-- **Euler's pentagonal number theorem** (Euler, 1750), in its coefficient form: the alternating
sign count over partitions into distinct parts is the pentagonal indicator.  A theorem; **not in
mathlib**, and stated here as imported. -/
def EulerPentagonalNumberTheorem : Prop :=
  ∀ n : ℕ, (∑ p ∈ Nat.Partition.distincts n, (-1 : ℤ) ^ (Multiset.card p.parts)) = eulerCoeff n

/-- **Franklin's involution** (Franklin, 1881) — the reconstruction fiber of the cancellation above:
a sign-reversing pairing on partitions into distinct parts whose fixed points are exactly the
pentagonal terms.  A theorem; not in mathlib, stated here as imported. -/
def FranklinInvolution : Prop :=
  ∀ n : ℕ, ∃ f : Nat.Partition n → Nat.Partition n,
    (∀ p, f (f p) = p) ∧
    (∀ p ∈ Nat.Partition.distincts n, f p ∈ Nat.Partition.distincts n) ∧
    (∀ p ∈ Nat.Partition.distincts n, f p ≠ p →
      (-1 : ℤ) ^ (Multiset.card (f p).parts) = -(-1 : ℤ) ^ (Multiset.card p.parts))

/-- **Ahlgren–Boylan exhaustion** (Inventiones **153** (2003), 487–502): Ramanujan's three are the
only congruences of the shape `p(ℓn + β) ≡ 0 (mod ℓ)` at a prime `ℓ`.  A theorem, imported; cited
from secondary sources and not read in the original. -/
def AhlgrenBoylanExhaustion : Prop :=
  ∀ ℓ β : ℕ, ℓ.Prime → β < ℓ → (∀ n : ℕ, (partitionCount (ℓ * n + β) : ZMod ℓ) = 0) →
    (ℓ = 5 ∧ β = 4) ∨ (ℓ = 7 ∧ β = 5) ∨ (ℓ = 11 ∧ β = 6)

/-- **Ahlgren–Boylan for Newman** (2003): every prime except possibly three.  A theorem, imported;
secondary. -/
def AhlgrenBoylanNewman : Prop :=
  ∀ m : ℕ, m.Prime → m ≠ 3 → ∀ r : ZMod m, {n : ℕ | (partitionCount n : ZMod m) = r}.Infinite

/-- **Kolberg at two** (Kolberg, 1959): Newman's conjecture holds at `m = 2` — *inside* the radical
of the shift, where Ono's criterion is refutable.  A theorem, imported, and it is what refutes the
strong reading of this file's aperture. -/
def KolbergAtTwo : Prop :=
  ∀ r : ZMod 2, {n : ℕ | (partitionCount n : ZMod 2) = r}.Infinite

/-- **Radu in every progression** (J. reine angew. Math. **672** (2012)): every arithmetic
progression contains infinitely many `N` with `p(N) ≢ 0 (mod 3)`.  A theorem, imported; secondary.
*Note what it does not say: whether infinitely many `n` have `p(n) ≡ 0 (mod 3)` is the open
case.* -/
def RaduInEveryProgression : Prop :=
  ∀ M r : ℕ, 0 < M → {n : ℕ | n % M = r ∧ (partitionCount n : ZMod 3) ≠ 0}.Infinite

/-! ## What the aperture actually decides -/

/-- **Ono's criterion is refutable inside the radical of the shift.**  Not merely hard at `2` and
`3` — *unsatisfiable*, because the condition `m·n ≡ −1 (mod 24)` that opens it has no solution
there.

**And this is where the deed's own reading fails, so it is recorded here and not in a footnote.**
`KolbergAtTwo` says Newman's conjecture is *true* at `m = 2`.  So an empty search space does not
make a case open; it makes *this criterion* blind, and the criterion has `24` written into it. -/
theorem theCriterionIsUnsatisfiableInsideTheRadical :
    ¬ OnoGoodPrime 2 ∧ ¬ OnoGoodPrime 3 := by
  constructor
  · intro h
    obtain ⟨n, hn, -⟩ := h 0
    exact theApertureIsTheRadicalOfTheShift.1 ⟨n, hn⟩
  · intro h
    obtain ⟨n, hn, -⟩ := h 0
    exact theApertureIsTheRadicalOfTheShift.2.1 ⟨n, hn⟩

/-- **Thirteen is a good prime, on the named hypothesis and on nothing else.**  The witness index is
`n_r = 24t + 11`, because `13·(24t + 11) + 1 = 24·(13t + 6)`, so the Ono index and the Ramanujan
index are the same index in two charts.  *The hypothesis is Euler's pentagonal number theorem in the
one finite instance this table needs; it is not proved here and it is not hidden.* -/
theorem theBridgeMakesThirteenGood
    (hb : TheWheelCarriesThePartitionFunctionAtThirteen) : OnoGoodPrime 13 := by
  intro r
  have hrv : r.val < 13 := ZMod.val_lt r
  obtain ⟨t, ht, hte⟩ :=
    List.mem_map.mp (theThirteenProgressionIsSurjectiveBelowFiftyFour r.val hrv)
  have ht54 : t < 54 := List.mem_range.mp ht
  refine ⟨24 * t + 11, ⟨13 * t + 6, by ring⟩, ?_⟩
  have hdiv : (13 * (24 * t + 11) + 1) / 24 = 13 * t + 6 := by omega
  rw [hdiv, hb t ht54, hte]
  simp [ZMod.natCast_val, ZMod.cast_id]

/-- **And with Ono's Theorem 3 beside it, Newman's conjecture holds at thirteen.**  Both hypotheses
are named, imported and unproved here; the content this file adds is the witness table alone.
*`m = 13` was settled by Atkin, Newman and Kolberg by 1960 — nothing here is new mathematics.* -/
theorem theBridgeAndTheCriterionReachNewmanAtThirteen
    (hb : TheWheelCarriesThePartitionFunctionAtThirteen) (hc : OnoCriterion) :
    ∀ r : ZMod 13, {n : ℕ | (partitionCount n : ZMod 13) = r}.Infinite :=
  hc 13 (by norm_num) (by norm_num) (theBridgeMakesThirteenGood hb)

end Soma.Holonics.Millennium.PartitionWheel

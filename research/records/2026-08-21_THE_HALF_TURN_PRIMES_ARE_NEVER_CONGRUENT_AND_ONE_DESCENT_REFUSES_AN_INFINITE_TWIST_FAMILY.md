# The half-turn primes are never congruent, and one descent refuses an infinite twist family

**Date:** 2026-08-21
**Kind:** the second-frame deed (D4 of the ratified ladder) — Brandon: *"Go for D4.  Do not
hedge … you have more than enough momentum to rip through the classical walls like paper."*
Solo orchestrator work, one Lean file, no agents; the full case analysis derived and checked
before encoding.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for the eleven Lean
theorems (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`);
`proved-standard` for the classical attribution (Genocchi 1855), cited.

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/Congruum.lean`.  Measured after the merge:
`Millennium/` is **66 files, 21,751 lines, 1,010 top-level `theorem` declarations**
(`grep -h "^theorem " ElementaryHolonics/Millennium/*.lean | wc -l`, 2026-08-21; three files
are Sol's in the shared tree); the library builds at **3,391 jobs**.

**`theHalfTurnPrimesAreNotCongruent`** — for **every** prime `p ≡ 3 (mod 8)`: no rational
right triangle has area `p`.  Genocchi's theorem, kernel-checked — the first statement in
this tree that closes the realized side of **infinitely many quadratic twists**
`y² = x³ − p²x` at once, where every previous realized-side theorem held one curve.  The
first three members are instanced (three, eleven, nineteen), and the triangle-to-progression
fold is exact: `((a ± b)/2)² = (c/2)² ± p`, so `p` congruent is precisely a **congruum**
`p·e²` — three integer squares in arithmetic progression — existing, and
**`theCongruumNeverForms`** refuses it by infinite descent:

- **an odd scale dies at the frame of eight** (`theOddScaleDiesAtEight`, kernel
  enumeration): `3·(odd)²` cannot separate two squares twice;
- **an even scale walks Fermat's own staircase**: the progression folds to a primitive
  Pythagorean pair (`r² + s² = u₁²`, `rs = 2pe′²`), the classification hands down `m, n`,
  and the four pairwise-coprime factors obey `m·n·(m−n)·(m+n) = p·e′²`;
- **the prime sits in exactly one factor, and three placements are refused by the two
  invisibility facts**: the quarter-turn invisible (`p ≡ 3 mod 4` — sums of two squares
  descend to the frame, `theSumOfSquaresDescendsToTheFrame`) kills `p ∣ m` and `p ∣ m+n`;
  two invisible (`p ≡ 3 mod 8` — doubled squares descend,
  `theDoubledSquareDescendsToTheFrame`) kills `p ∣ m−n`;
- **the fourth placement descends**: `p ∣ n` reproduces the progression at scale `b` with
  `4·|b| ≤ |e|` — a strictly descending chain on well-founded terrain, the third such
  refusal in the tree (heights for the rank, depths for the torsion, scales for the twist
  family).

## 2. The mechanism identity this deed exposes

**The same two invisibility facts that integrated the reflection census are the ones that
refuse the descent branches.**  In `ReflectionCensus.lean`, `¬IsSquare(−1)` made every blind
frame's count vanish; here `¬IsSquare(−1)` and `¬IsSquare(2)` kill three of four placements
of the prime.  The analytic side's phase law and the realized side's descent law are one
mechanism read on two materials — which is the route's standing claim (*the two sides are
readings of one transport*) arriving as a shared proof engine rather than a correspondence.

In the second-frame program this is the entry deed: the twist family is the second axis, and
this theorem is its first **family-wise** realized-side law — one congruence class of the
family resolved wholesale, where the per-`n` theta laboratory reads one instance at a time.

## 3. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the sibling family `p ≡ 5 (mod 8)` (classically non-congruent as well): the branch pattern runs through the minus-two character (`ZMod.exists_sq_eq_neg_two_iff`), a fourth invisibility | a placement the minus-two character fails to refuse |
| the curve-point face: `y² = x³ − p²x` has rank zero for these primes — the bridge from the triangle statement through the curve population, as `RankZero.lean` did at one | a rational point off the half-turns for some `p ≡ 3 mod 8` |
| the Rédei/governance layer: the 2-Selmer matrix of the family as exact 𝔽₂ linear algebra, joining this wholesale refusal to Smith's distribution frame | a twist whose governance matrix disagrees with its census |
| the Tunnell cross-check at three (`theCensusesDifferAtThree`) now has its unconditional realized side from this family — recorded as agreeing; extend the agreement table as instances accrue | an instance where the family theorem and the theta census disagree |

## 4. Boundaries

One congruence class of primes; the statement is the triangle (congruent-number) face, and
the curve-rank face is owed, not claimed.  The file raises the compile heartbeat budget —
an apparatus dial for elaboration compute, no semantic content.  Nothing about Selmer
structure, the obstruction group, or the Birch–Swinnerton-Dyer conjecture is claimed; the
family's analytic side (root numbers, central values) is untouched here beyond the
already-deposited theta instances.

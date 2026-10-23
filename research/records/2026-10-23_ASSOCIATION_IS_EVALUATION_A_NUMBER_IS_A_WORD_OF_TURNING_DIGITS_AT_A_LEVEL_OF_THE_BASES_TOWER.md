# Association is evaluation: a number is a word of turning digits at a level of the base's tower

**Date:** 2026-10-23. **Occasion:** The design thread had said that Athena's arithmetic was
association rather than evaluation: a result such as 60 after `2*30` was read from contexts it had met.
Brandon answered with four lenses that afternoon:
- Association and evaluation are equivalent in compression and navigation. To associate faces is to
  evaluate the constraints and causal potentials that produce them, as with the digits of a mantissa
  and the conservation of faces.
- Arithmetic is learned from the distributions of many interacting digits, the way he does mental
  arithmetic and recognizes primes: bitwise operations moving the parts about each other. His example:
  `9·x` ends in ten minus the last digit of `x` (`9·7 = 63`, `9·23 = 207`). Number theory from Fermat on
  is rebasing and geometry.
- Composition is combinatorial potential and thermodynamics: atoms and their ingredients, with binary
  potentials integrating.
- The correction that sets this record's level: what a numeral ends in hardly matters. 12,400 is the
  digits `{1, 2, 4}` modulated by `10²`. Every numeral system (Roman, decimal, hexadecimal) is symbols on
  cycles that rotate, like staircases or towers (Iwasawa), with potentials partitioned by which factors
  can reach which axes (coprimality), caustics and invariants. The learning logic is that, and it is not
  complicated.

The first version of this record (through `feec464`) built a longer apparatus around the last digit.
This version is pared to the picture. The identities stay in their atlas rows.

**Joins.** The picture was already in the repository; this record joins it.
- The level: `radix.exact-chart` (Lean `Foundation/PrimeValuationRadixAtlas`), and the
  [helix record](2026-09-28_A_NUMBER_IS_A_HELIX_ITS_BASE_IS_A_FACE_AND_A_FAMILY_WINS_WHERE_IT_IS_CLOSEST.md)
  for `log_b n = k + θ`.
- The staircase: `tower.padic-plural` and `tower.padic-fibre-splitting` (Lean `Foundation/PadicTower`,
  `Foundation/ContinuingTower`).
- The crossings: `radix.local-winding-split`, `radix.cheap-faces`, `radix.trailing-unit-rings`, and
  `tower.cyclotomic-coprime-irreducible` beside `tower.ramified-layer-reducible` (Lean
  `Foundation/IwasawaTower`).
- The caustic: `prime.additive-caustic` (Lean `Foundation/PrimeValuationRadixAtlas`) and
  `radix.multiplication-table`.
- The producer and its consumer: `radix.digit-convolution` and `radix.carry-cascade-consumer` (Lean
  `Mathematics/ArithmeticContract`), the
  [arithmetic contract](2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md),
  `radix.leading-fibre` (Lean `Mathematics/RadixWindowReceiver`), and the carry as
  `release.carried-residue` (Lean `Foundation/CarriedRelease`).
- The fibre: `info.preimage-fibre`.
- The gas and Fermat: `heat.zeta-gibbs` (Lean `Zeta/PaletteLaw`) and `landmark.primitive-cycle-count`
  (Lean `Compression/Landmark/PrimitiveCycle`).
- The [code-length record](2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md),
  whose lens is measured in §3 and corrected in §6.

**Truth discipline:** `[proved-standard]` marks a classical result, `[proved-derived]` a short
derivation given here, `[measured]` an exterior reading with its receipts, `[interpretation]` a
correspondence and `[design]` a consequence for Athena. The digit laws and congruences are exact
integer checks; the code lengths are exterior float reads.

## 1. The picture

**A number is a word at a level** `[proved-standard]`. `n = b^d · r` with `b ∤ r`, and `d` and `r` are
unique (`radix.exact-chart`, formal-checked). 12,400 is the word 124 at level 2: trailing zeros are the
level, not digits of the word. On the helix, `log_b n = k + θ`: the leading digits are the phase `θ` on
the base's circle and the length `k` is the winding.

**Each digit turns on a cycle, and the places are a staircase** `[proved-standard]`. A digit is a
symbol on a cycle of `b` states (0 to 9, 0 to f, I to X). A full turn steps one stair up: the carry.
The places form the tower `ℤ/b ← ℤ/b² ← ℤ/b³ ← …`, each level covering the one below `b` to one
(`tower.padic-fibre-splitting` for a prime base). Base 10's tower is two prime towers crossing,
`ℤ/10ⁿ ≅ ℤ/2ⁿ × ℤ/5ⁿ`.

**Operations turn the cycles and climb the stairs** `[proved-standard]`.
- A product turns the phase, `θ(xy) = θ(x) + θ(y)` modulo a full turn, with the overflow carried into
  the length. It adds the levels, `d(xy) = d(x) + d(y) + d(r_x r_y)`; the words' own product can climb,
  as `2·5 = 10`.
- A sum turns each place and steps the carries up. Its level is the lower one when the two differ. It
  climbs only where equal levels meet and the words cancel at the bottom, which is the additive caustic
  (`prime.additive-caustic`, formal-checked at a prime).

**Coprime crossings partition what can be produced** `[proved-standard]`. On a cycle `ℤ/q`,
multiplying by `m` lands on `q/gcd(m, q)` values. A factor coprime to `q` turns the cycle, a
permutation. A factor that shares a prime with `q` collapses it.
- `9 ≡ −1 (mod 10)` is the half-turn, so `9x ≡ −x` and `9·x` ends in ten minus the last digit of `x`.
  On base 10's two cycles, 9 is the identity on the 2-cycle and the half-turn on the 5-cycle.
- The base's own primes read only a fixed number of last digits. Every cycle coprime to the base reads
  all the digits through a winding of period `ord_q(b)` (`radix.local-winding-split`,
  `radix.cheap-faces`). `10 ≡ 1 (mod 9)`, so the 9-cycle reads the digit sum; `10 ≡ −1 (mod 11)`, so the
  11-cycle reads the alternating sum; the 7-cycle winds with period 6.
- So which values two operands can produce along an axis is fixed by which of their factors cross
  that axis's cycle. `[interpretation]` These are the horizontal (coprime) and vertical (the base's own
  prime) layers of the Iwasawa tower (`tower.cyclotomic-coprime-irreducible`,
  `tower.ramified-layer-reducible`).

**Caustics and invariants.** Where many producing pairs converge on one value, the map has a caustic
`[proved-standard]`. A product's last digit is 0 for 27 of the 100 digit pairs, 5 for 9, each other odd
digit for 4 and each other even digit for 12 (`radix.multiplication-table`), and values with many
divisors are the caustics of multiplication over the whole numbers. `[interpretation]` Caustics are
landmarks, the faces where navigator paths converge. The invariants are the faces an operation keeps
(§2).

## 2. Association is evaluation `[proved-derived]`

An operation is a constraint, the graph of `T : X × X → X`. A **face** is a receiver's quotient
`q : X → F`: a cycle `ℤ/q`, the leading digits with the length, the level.
- To associate faces `f` and `g` of the operands with a face of the result is to read the result faces
  the constraint admits, `Fib_q(f, g) = q(T(q⁻¹f × q⁻¹g))`. Until it closes it is a plural Preimage Fibre
  (`info.preimage-fibre`).
- `q` is **kept** by `T` when every such fibre is one point. Then `q ∘ T = T_q ∘ (q × q)`: the operation
  descends to the face, and `T_q` is the face's own operation.
- To **evaluate** `T` at `(x, y)` is to associate a family of faces that is jointly injective on the
  result's range.

So evaluation is association whose fibre has closed. In compression a result costs at most
`log₂ |Fib|` given the associated faces; in navigation each added face narrows the fibre, and the paths
converge on the value where it closes. Brandon's equivalence holds in both.

What lets an associator reach operands it has not met is not the act. It is whether the faces it
associates are kept by the operation, and whether their `T_q` is small enough to be met often. A whole
calculation read as one string is a jointly injective face, but its `T_q` is `T` itself, one entry per
string. The faces arithmetic keeps are few and small:

| face | sum and difference | product |
|---|---|---|
| any cycle `ℤ/q` (the last `k` digits are `q = b^k`, the digit sum `q = b − 1`) | kept | kept |
| phase `θ`, the leading digits | sum: up to the carry fibre; difference: not kept | turned by `θ(y)`, up to the carry fibre |
| length `k` | up to one carry; a difference can drop many | `k_x + k_y`, up to one carry |
| level `d`, the trailing zeros | the lower level; climbs only at a caustic | `d_x + d_y`, plus what the words' product adds |

The leading face is kept only up to the fibre that the unread lower places send up
(`radix.leading-fibre`); each further leading digit is a finer face and narrows it. A difference cancels
its leading face: if `x ≥ y` both have length `n` and share `j` leading digits, then
`0 ≤ x − y < b^(n−j)` `[proved-derived]`. Brandon's conservation of faces is literal: an operation keeps
the cycles exactly, the phase up to what the carry carries, and the level up to its caustics.

## 3. Measured: Athena's lens associates whole strings `[measured]`

The lens is the code-length record's online released tree with its ring lock, unchanged: an exact reach
of six bytes, a mixture horizon of `2^13` cells, and a lock over the whole passage. The passage is the
GSM8K training partition, with 21,268 calculations `<<expr=result>>`, 20,466 of them with integer
results. A calculation is **met** when the same expression occurred earlier in the passage.

Bits a result digit (a uniform decimal digit costs `log₂ 10 = 3.32`):

| result digit | met: digits | met: bits | unmet: digits | unmet: bits |
|---|---|---|---|---|
| leading (results of two or more digits) | 8,194 | 1.105 | 8,347 | 3.536 |
| middle | 2,362 | 0.911 | 6,696 | 3.365 |
| last (results of two or more digits) | 8,194 | 0.657 | 8,347 | 3.397 |

The last-digit row counts a result's trailing zeros, which are its level, together with the word's last
digits; the table does not split them.

**The faces' own budget**, over the single-operation integer calculations `x op y`. The leading fibre is
the exact interval enclosure of `radix.leading-fibre`, not a sample.

| | sum | product | difference |
|---|---|---|---|
| calculations | 3,815 | 6,284 | 3,388 |
| last digit, given the operands' last digits | one digit, always | one digit, always | one digit, always |
| leading digit, given one leading digit and the lengths: mean `log₂` fibre | 0.743 | 0.799 | 1.735 |
| the same, share closed to one digit | 25.7% | 47.5% | 8.6% |
| leading digit, given two leading digits and the lengths: mean `log₂` fibre | 0.015 | 0.008 | 0.212 |
| the same, share closed to one digit | 98.5% | 99.2% | 81.9% |

**Reading.**
- On unmet calculations the lens pays more than a uniform digit at every place, although the cycle law
  fixes the result's last digit in every one of 13,491 single-operation calculations, all 153 products by
  9 obey `9x ≡ −x`, and all 228 products of two digits coprime to 10 obey the turn on the unit cycle. Its
  faces are whole strings, and arithmetic keeps no face of a whole string, so it evaluates only what it
  has met.
- Text writes the leading digit first, so the phase arrives before the level and the length are known;
  both close when the numeral ends.
- The passage offers the cycles thinly. Of its 6,284 products, 2,729 have an operand with trailing zeros
  (a shorter word at a higher level) and only 228 have both last digits coprime to 10. Its sums carry out
  of 21% of their two-digit places, where uniform digits would carry out of about half.

## 4. Composition: atoms, cycles and binary potentials `[proved-standard; interpretation where marked]`

Each identity is one atlas row.
- **Atoms.** A word is a multiset of prime atoms, `n = ∏ p^(v_p)`, and its level reads the base's own
  atoms, `v_p(n) = d·v_p(b) + v_p(r)` (`radix.exact-chart`). Weighted by `n^(−σ)` the integers are a gas
  whose energy `log n` is the helix's height (`heat.zeta-gibbs`), and its leading-digit law tends to
  Benford's as `σ → 1⁺` (`radix.leading-face-gas`).
- **Fermat on a cycle of p sites.** Rotating a necklace of `p` sites returns every configuration, and
  the non-constant ones fall into full orbits of `p`, so `a^p ≡ a (mod p)`. For any integer transfer
  matrix, `tr(A^p) ≡ tr(A) (mod p)` (`arith.fermat-ring-partition`, joined to Lean `PrimitiveCycle`). On
  base 10's two crossing cycles this gives `n⁵ ≡ n (mod 10)`.
- **Binary potentials at a place.** Two digits generate a carry (sum at least `b`), kill it (at most
  `b − 2`) or pass it on (exactly `b − 1`); in base 2 these are AND and XOR. A carry still unread after
  `m` places has probability `b^(−m)`, and over many summands its long-run law is Eulerian
  (`radix.carry-chain-eulerian`). `[interpretation]` The carry is a held remainder whose uncertainty
  fades by a factor of `b` a place.
- `[interpretation]` The digit distributions Brandon reads in mental arithmetic are these maps pushing
  the operands' distributions forward: turns, collapses and climbs.

## 5. What this means for Athena `[design]`

1. **One mechanism.** Association through contacts is evaluation wherever the faces it reads are kept
   by the operation. Nothing separate is needed.
2. **Three things to locate:** each digit's turn on the base's cycle, the level (so 12,400 and 124 are
   one word), and the crossings (which cycles a factor turns and which it collapses). Her diagonal
   complex modes are turns, so they can carry all three once learning places the digits on them. No new
   object is needed.
3. **A product is a pair contact** between two operands' words, with their levels added. A carry is a
   held remainder stepping one stair up (`release.carried-residue`), never rounded away.
4. **Terrain.** Sums, products and differences of many words at many levels, generated exactly, with
   uniform digits so that carries are exercised and with operand pairs held out. A terrain may generate
   its truth exactly.
5. **Nothing authored inside:** no calculator, digit-to-phase table, place counter or carry routine.
6. **Readings each run, beside the generations:** the held-out code of result digits on unmet
   calculations, by place, against §3's budget (the lens pays over 3.3 bits at every place); whether a
   word and the same word at another level are read as one; and whether multiplying by 9 acts on her
   digit modes as the half-turn. No single place is the acceptance: the last digit is one cycle among
   many.

## 6. Corrections to the code-length record

- **§2** called the lens's result digits "a table at the lens's grain, not arithmetic". It is evaluation
  at faces that arithmetic does not keep, so it reaches only the calculations met (§3 here). The
  sentence there now says so and points here.
- **§1 and §6** read `w` as unchanged under the casts. That holds for constant casts: bits to nats, cell
  to byte, and a region's steady share of the passage. A clock whose units change length is not a
  constant cast (Epime's review note of October 23). In general `w′ = w · d ln V/d ln V′`. With `N_k`
  bytes for `k` founded units, `w_unit = w_byte · d ln N_k/d ln k`, so a region at its byte floor reads
  `w_unit < −1` while its units lengthen. That phantom reading is the cast, not hardening, and it agrees
  with §1's law that expansion needs the material to change. A report on a unit clock declares its cast
  (`code.clock-cast`).

## 7. Owed

- **Lean** (one box in #410):
  - a kept face descends (`q ∘ T = T_q ∘ (q × q)` exactly when every fibre is one point), and a jointly
    injective face family evaluates `T`;
  - the level laws of a product and a sum in the exact chart, and the cancellation of a difference's
    leading face;
  - multiplication by `m` on `ℤ/q` has `q/gcd(m, q)` values, with `9x ≡ −x` and `n⁵ ≡ n (mod 10)`, and the
    trailing digit law's factorization over the base's primes;
  - `tr(A^p) ≡ tr(A) (mod p)` for integer matrices, extending #410's box on necklace integrality (the map
    case is `PrimitiveCycle`);
  - the carry chain's Eulerian law and spectrum, and `b^(−m)` for an unread carry;
  - the clock cast of `w`.
- The chart, the tower, the coprime and ramified layers and the additive caustic are already
  formal-checked.
- **Atlas rows:** `arith.association-is-evaluation`, `radix.level-laws`,
  `radix.difference-leading-cancellation`, `radix.multiplier-face-action`,
  `radix.product-digit-law-factors`, `arith.fermat-ring-partition`, `radix.leading-face-gas`,
  `radix.carry-chain-eulerian` and `code.clock-cast`.

## Receipts

`2026-10-23_ASSOCIATION_IS_EVALUATION_receipts/`.

**Programs:**
- `assoc.py` reads the code-length record's lens output beside the passage and writes `assoc.json`.
  The lens output is the per-cell bits of the whole passage (169,352,064 bytes), which is not committed;
  that record's `run.sh` regenerates it.
- `fibre.py` computes the leading fibres by interval enclosure and writes `fibre.json`.
- `digits.py` reads the products' trailing and leading digit laws and writes `digits.json`.
- `fermat.py` checks §4's identities exactly, including 3,600 congruence checks over random integer
  matrices, with no failure.
- `carries.py` checks the carry chain (stationary law and eigenvalues for two to four summands in bases
  2, 3 and 10) and carry lookahead exactly, reads the passage's carries, and writes `carries.json`.

**Run receipts** `run_assoc.txt`, `run_fibre.txt`, `run_digits.txt`, `run_fermat.txt` and
`run_carries.txt`.

**Time.** The runs were unmeasured beforehand, so they were planned under the one-to-three-minute rule,
with deadlines of 120 s (`assoc.py`) and 60 s (the others).
- `assoc.py` took 16.9 s with a cold read and 1.5 s warm, with a peak of 260 MiB, 0.14 of its deadline.
- `fibre.py` took 0.1 s, `digits.py` under a second, `fermat.py` 2.2 s and `carries.py` 0.3 s.

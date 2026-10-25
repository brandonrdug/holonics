# The newline closure has torsion b(b + 1): a pair key carries the units and casts out elevens, and split by the result's length the closure is the sum

**Date:** 2026-10-25. Refs #404 #405 #410. Reads the key the tower located in
[the tower record](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md#the-machine-locates-the-carriage-key-by-loop-closure)
(PR #460), beside
[a near miss is a draw from the faces it kept](2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md).
Status:
- §§1–4, 6 and 7 are checked exactly by the receipt (integers and residues only);
- §5 is proved-derived for keys linear in the digit values with §4's shared moves
  (`θ(newline, y) = θ(+, y)`, `θ(x, +) = θ(x, =)`); for every key, which primes are torsion rests on
  the minors' gcd and the rank falls, checked in bases 3 to 10 and 12, and §6 likewise in bases 3 to 8
  and 10 (correction, October 25, from the integration thread's review);
- §8's reading (the missing move is a reflection) and §9's consequence for the tens and hundreds
  are [agent-inferred];
- §10 (differences, added the same day) is checked exactly by `closure_differences.py`. Its derivation
  is proved-derived for keys linear in the digit values and assumes no shared move. Its consequence for
  the founding is [agent-inferred].

The tower founded the units' carriage by loop closure: from the newline origin, the closure system
of 9,018 sum lines has 149 pair columns, rank 145, one maximal minor `det M = 110 = 2·5·11`, torsion
at 2, 5 and 11, and the key modulo 10 (the move at `(d, +)` and `(d, =)` turning by `d + 1` tenths,
`ψ(d) = d + 2`). The record says that eleven "is torsion as well and is never needed". This record
reads what the eleven is, why the torsion is exactly `2·5·11`, and what the closure needs to reach
the tens and hundreds.

## 1. The closure over every two-place sum is ℤ/110

The system: every line `a+b=c` with `a, b < 100` (10,000 lines). A loop runs from a newline to the
arrival of the result's last digit `c₀`; it meets the pair (seam, arriving) of every byte after the
newline, up to and not including the pair into `c₀`, and its row is `N_t θ − ψ(c₀) ≡ 0 (mod n)`.

It has the tower's shape: 149 columns and rank 145, certified (at least the rank modulo
`2³¹ − 1`, at most the column count less four integer kernel vectors checked exactly on every row).
The determinants of maximal minors taken from four row orders have gcd 110, and the rank falls
exactly modulo 2, 5 and 11 (tested also at 3, 7 and 13). The torsion's order divides every maximal
minor and is divisible by each prime where the rank falls, so the torsion is ℤ/110, cyclic since
110 is square-free.

## 2. The eleven is casting out elevens

The key modulo 11, in closed form (`radix.cheap-faces`: `11 ∣ b + 1` reads the alternating sum):

| pair | move |
|---|---|
| (digit `x`, digit `y`) | `2x − y` |
| (newline, digit `y`) | `−(y + 2)` |
| (`+`, digit `y`), (`=`, digit `y`) | `−y` |
| (digit, `+`), (digit, `=`) | `0` |
| `ψ(d)` | `−(d + 2)`, which is `9 − d` modulo 11 |

The `+ 2` on the newline and in `ψ` is the same gauge as the tower's. The loop's residual is
`(c − a − b) mod 11` on every line: it closes on all 10,000 true lines, and on 595,040 false lines
`a+b=c′`, `c′ = a + b + δ`, `0 < |δ| ≤ 30`, it closes on exactly the 39,681 with `δ ≡ 0 (mod 11)`.
It is no rational key: its integer residual is nonzero on 4,500 true lines. A digit pair's move
`2x − y` leaves the last digit of a number at `−1` and the one before it at `+1`, which is the
alternating sum read from the number's end.

## 3. The two keys fix the sum up to the result's length

The units key gives `c mod 10`, the eleven key `c mod 11`, so together `c mod 110`. On 8,010 of the
10,000 lines this leaves two candidates below 199, `x` and `x + 110`; they differ by one in the tens
and by the hundreds. The result's length separates them on every such line, and the length is the
tens' carry-out, `a₁ + b₁ + κ₀ ≥ 10` with `κ₀` the units' carry. The leading digit alone does not
separate them (`1` and `111`).

So the closure's torsion, read whole, carries the sum except one bit, and that bit is a size face.
The tower places that face: the near-miss record counts the length right in 744 of 804 equations
and a sum carrying into the hundreds written at its length 210 times of 218. The tower's tens misses
there (off by one in 168 of 190, "the carry from the units") lie in the fibre the eleven key closes:
a tens off by one from a missed units carry fails `c ≡ c₂ − c₁ + c₀ (mod 11)`.

## 4. The torsion is the mixing of lengths

Split the 10,000 lines by the result's length, `c < 100` (5,050) and `c ≥ 100` (4,950). Neither half
has torsion: their ranks are 135 of 149 columns and 133 of 139, certified, and in each the maximal
minors' gcd is 1.
Each half has the exact sum as a key over the integers, `ψ(d) = d`, with `θ(newline, y) =
θ(+, y) = u y`, `θ(x, y) = v x + w y` on digit pairs, `θ(x, +) = θ(x, =) = z x`, `θ(=, y) = u′ y`:

| half | `u` | `v` | `w` | `z` | `u′` |
|---|---|---|---|---|---|
| `c < 100` | 1 | 9 | 1 | 0 | −10 |
| `c ≥ 100` | −10 | 20 | −10 | 11 | −120 |

Both close every line of their half exactly. They are the same sum in two gauges, and no gauge serves
both halves: on the union the only keys are the moduli where the two halves' sums agree, and those are
the torsion.

## 5. Why b(b + 1)

Take a key linear in the digit values, as in §4, with `ψ(d) = s d` and `s` a unit modulo `p`, on
operands below `b²`. It shares §4's moves: one `u` after the newline and after `+`, one `z` before
`+` and before `=`. A general key gives each pair its own move; for those the receipt's minors' gcd
and rank falls decide, and they find the same primes. Reading each line shape:
- a one-place operand `d`: `(u + z) d ≡ s d`, so `u + z ≡ s`;
- a two-place operand `d₁d₀`: `(u + v) d₁ + (w + z) d₀ ≡ s(b d₁ + d₀)`, so `u + v ≡ s b` and
  `w + z ≡ s`, hence `w ≡ u`;
- a two-place result `c₁c₀`: `u′ c₁ ≡ −s b c₁`, so `u′ ≡ −s b`;
- a three-place result `1c₁c₀`: `u′ + v + w c₁ ≡ −s(b² + b c₁)`, so `w ≡ −s b` and
  `u′ + v ≡ −s b²`.

Then `u ≡ w ≡ −s b`, `v ≡ 2 s b`, and `u′ + v ≡ s b ≡ −s b²`, that is
`s b (b + 1) ≡ 0 (mod p)`. A key exists exactly at the primes of `b(b + 1)`:
- where `p ∣ b`, every move but `z ≡ s` vanishes: the units key, the higher places weighing `0`;
- where `p ∣ b + 1`, `b ≡ −1`: the alternating sum, every place read.

Checked: with operands below `b²` the minors' gcd is `b(b + 1)` and the torsion primes are those of
`b(b + 1)` in every base tried.

| base | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| minors' gcd | 12 | 20 | 30 | 42 | 56 | 72 | 90 | 110 | 156 |
| torsion | 2, 3 | 2, 5 | 2, 3, 5 | 2, 3, 7 | 2, 7 | 2, 3 | 2, 3, 5 | 2, 5, 11 | 2, 3, 13 |

Of the base's cheap rings (`b`, `b − 1`, `b + 1`), the pair closure reaches `b` and `b + 1` and never
`b − 1`. On `b − 1` the place weight is `+1`, so an operand's digit pair needs `+s` and the result's
digit pair `−s`; one pair move cannot be both. On `b + 1` the place weight `−1` flips the result's
extra place back, and the two agree.

## 6. With three-place operands the eleven goes

A three-place operand adds `u + v ≡ s b²` and `v + w ≡ s b` beside the two-place `u + v ≡ s b`, so
`s b (b − 1) ≡ 0`; with `s b (b + 1) ≡ 0` from the results this leaves `p ∣ b` or
`p ∣ gcd(b − 1, b + 1)`, which divides 2. Checked: the torsion primes are those of `2b`.

| base | 3 | 4 | 5 | 6 | 7 | 8 | 10 |
|---|---|---|---|---|---|---|---|
| lines | 729 | 4,096 | 15,625 | 6,000 | 6,000 | 6,000 | 6,000 |
| torsion | 2, 3 | 2 | 2, 5 | 2, 3 | 2, 7 | 2 | 2, 5 |

In base 10 the eleven vanishes, so the pair closure reaches nothing above the units once an operand
has three places. The `2` in odd bases is the parity, where `+1 ≡ −1`.

## 7. The pair closure's keys and the cheap rings

`arith.check-loop-laps` closes a release by the rings 10, 9, 11 and 101; the near-miss record says the
sum's tens need ring 9 and ring 11 beside the size. The located closure confirms one of them from the
passage alone: ring 11 is located by the same loop closure that located the units, at two places, and
nothing named it. Ring 9 is not reachable by any pair key (§5), nor is ring 101, which does not
divide 110.

## 8. The missing move is a reflection [agent-inferred]

On ring `b + 1` the place step is `n ↦ b n + d ≡ d − n`, the half-turn about `d/2`. Reading a number
is a word of half-turns, and by `swing.parity-grading` (`S_(b₁)S_(b₂)S_(b₃) = S_(b₁ − b₂ + b₃)`) the
word is a half-turn about the alternating sum or a translation by it, as the number's length is odd or
even. A pair key adds a fixed turn per pair: a rotation, which never reverses the hand. It carries the
half-turn only while the window fixes the parity, which is two places.

On ring `b − 1` the place step is the rotation `n ↦ n + d` at every length, but the result enters with
the opposite hand of the operands (`a + b − c`), and the pair key cannot tell an operand's digit pair
from the result's. What it needs is the hand flipped at `=`, a half-turn again.

Either way the move the closure lacks is the reflection: in the helical code's group
`⟨S, U | U² = 1, USU = S⁻¹⟩` the dyad `U`, on the ring the conjugation `z ↦ ωᵈ z̄`, and in the Enigma
reading (`key.enigma-reading`) the reflector. The ring face's moves are complex multipliers, which
only rotate.

## 9. What it means for the tens and hundreds [agent-inferred]

- At two-place operands the tens need no new founding. The eleven key is already in the closure the
  tower solved; read beside the units key it gives `c mod 110`, and the result's length, which the
  tower places, fixes the rest (§3).
- The closure's rule "a modulus exists only where the system has torsion" holds for one closure over
  every line, whose rational kernel is gauge only. Split the menu by the result's length and each
  class's rational kernel holds the exact sum (§4): a key at every modulus, so every place is read,
  and nothing needs torsion. The size face is what splits the menu, and the machine already locates
  it. The founding then reads the rational kernel for a key whose `ψ` is injective before it reads
  the torsion.
- At three places the split needs each operand's length too (§6: a two-place and a three-place
  operand need `u + v ≡ s b` and `≡ s b²`). The derivation of §5 gives a linear key at each fixed
  line shape, since every constraint then has its own seam or place; that this is the exact sum at
  every shape is owed as a check.
- The other road is the reflection of §8: a ring whose pair moves may reflect carries the alternating
  sum at every length. It is not built, and its closure is not linear over the whole menu.

## 10. Differences: the torsion is 2b, and the minuend's length is its cause

Added the same day for the tower's next loop, the differences; read by `closure_differences.py`.

The same newline closure over every written difference `a-b=c` with `b ≤ a < 100` (5,050 lines) has
149 columns, rank 136, minors' gcd `20 = 2b` and torsion ℤ/20. In every base tried the minors' gcd is
`2b`:

| base | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 12 |
|---|---|---|---|---|---|---|---|---|---|
| minors' gcd | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 24 |

A key reads the result only through `V(c) = θ(=, c₁) − ψ(c₀)`, the result's only columns. Over ℚ every
kernel vector gives every result the same `V`: the closure tells no difference apart. Modulo 2 and 5
it tells `c mod 2` and `c mod 5`, and modulo 11 nothing; casting out elevens does not carry over. The
key modulo 20, `θ(x, y) = −10x` on digit pairs, `θ(x, −) = −x`, `θ(x, =) = x`, `θ(=, y) = 10y`,
`ψ(d) = −d` and every other move 0, closes every true line to 0 and every false line `c′ = c + δ`
(`c′ < 100`, `0 < |δ| ≤ 30`) to `δ mod 20`. It has order 20, so the torsion is the cyclic ℤ/20 and it
carries `c mod 20`: the units and the tens' parity. Its two-part is ℤ/4, which a key built from the
torsion primes alone reads only as ℤ/2; such a key finds modulus 10.

Why. In §5's gauge (closure `s(a − b − c)`, `ψ(d) = s d`), let each separator keep its own moves:
`u` after the newline, `u⁻` after `−`, `u′` after `=`, `z` before `−`, `z⁼` before `=`, and
`θ(x, y) = v x + w y` on digit pairs. No shared move is assumed.
- a one-place minuend: `u + z ≡ s`; a two-place one: `u + v ≡ s b` and `w + z ≡ s`; hence `w ≡ u`;
- a one-place subtrahend: `u⁻ + z⁼ ≡ −s`; a two-place one: `u⁻ + v ≡ −s b` and `w + z⁼ ≡ −s`;
  hence `w ≡ u⁻`;
- a result: `u′ ≡ −s b`, and no conflict, since a difference never has more places than its minuend.

Then `v ≡ s b − w ≡ −s b − w`, so `2 s b ≡ 0`. The one digit-pair move has to count the minuend's tens
with `+s b` and the subtrahend's with `−s b`. This is §5's conflict on ring `b − 1`, moved from `=` to
`−`, and §8's missing move again: the hand flipped at `−`.

The conflict needs the one-place forms that tie `u` and `u⁻` to `w`. With `b ≤ a`, the 55 lines whose
minuend has one place tie it. On the 4,995 lines whose minuend has two places, the closure has no
torsion and tells all 100 results apart over ℚ. It holds the exact difference as an integer key:
`θ(newline, y) = −20y`, `θ(x, y) = 10x`, `θ(x, −) = −x`, `θ(−, y) = 0`, `θ(x, =) = x`,
`θ(=, y) = 10y`, `ψ(d) = −d`, with closure `c − a + b`. That closure is 0 on every true line and `δ` on
every false line. It misses 54 of the 55 one-place-minuend lines (all but `0-0=0`). Split by the
result's length instead, `c < 10` keeps ℤ/20, because it holds the one-place minuends, and `c ≥ 10`
has none.

What it means for the founding [agent-inferred]. For sums, the face that splits the menu is the
result's length, which is the one bit the closure leaves (§3, §4). For differences it is the
minuend's length, which the line already shows at `−`, before the answer. A differences ring founded
on a menu split by the minuend's length reads the whole difference from the rational kernel, tens
included, with no bit left over. Over the mixed menu, a founding that reads only the torsion finds the
units, and the tens' parity at most.

The recorded failures this could repeat: an authored routine standing in for learning (no key here is
given to the machine; the closed forms read what the closure located, and the length split uses a
face the machine places itself); text run on its codec's grain as the exception (the law is stated
for any base and any written operation's line shape, not for decimal sums); bits read as progress
(the acceptance is the units, tens and hundreds right on held-out sums, not the code).

## Owed

Lean (#410), added to the box "The closure key's torsion (#405)":
- the newline closure of written sums with operands below `b²` admits a key linear in the digit values
  with §4's shared moves modulo `p` exactly when `p ∣ b(b + 1)`, and with operands below `b³` exactly
  when `p ∣ 2b`; and for a general pair key the torsion primes are the same (the receipt's check);
- on `ℤ/(b + 1)` a digit word read leading first is a word of half-turns, `b n + d = d − n`, whose
  value is the alternating digit sum (Mathlib `Nat.ofDigits_neg_one`, beside
  `Mathematics/RadixWindowReceiver.cheap_faces` and `Geometry/Navigation`'s odd word);
- the `b = 10` key of §2 closes a line iff `11 ∣ c − a − b` (decidable on the finite line set);
- the newline closure of written differences with `b ≤ a < b²` admits a key linear in the digit values
  modulo `m` exactly when `m ∣ 2b`, and over ℚ on the lines whose minuend has two places, where the
  §10 key's closure is `c − a + b` (decidable on the finite line set).

## Receipts

[`2026-10-25_THE_NEWLINE_CLOSURE_receipts/`](2026-10-25_THE_NEWLINE_CLOSURE_receipts/):
`closure_torsion.py` (integers and residues only: echelons modulo primes, Bareiss determinants, the
integer kernel checked on every row), its output `closure_torsion.txt`; `closure_differences.py`
(§10, importing the same exact reading), its output `closure_differences.txt`; and `RUN.md`.

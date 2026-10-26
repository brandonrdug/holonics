# The operands are held by located strands, and the result is read on the ring that closes

October 26. Refs #404, #406, #405, #386. The capture loop's navigator was retired because its fold
was column addition written by hand ([the generator record](2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md)
§8). GPT-6's review asked for the smallest seam where the machine, from the text's own contacts,
selects the carrier, the capture and the decoder with no authored hand, fold or result recurrence.
This record derives that seam and fixes the next loop before it is built. Grades: [derived] for
what follows from the objects, [measured] for checks with their receipts, [agent-inferred] for each
choice. Receipts: [`…_receipts/`](2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES_receipts/CHECKS.md).

Computational object: the helical pair interaction. The loop touches the helix (each strand is a
phase a digit turns), the pair (the comparison of two strands is a pair contact's product) and faces
and placement (a result is read on the ring of its own length); cell holonomy, the tube and the
tower thread stay as the turned tower has them.

## 1. What the last loop left

[measured] The towers fail at the equals by holding and by releasing (the gaps read,
[CAPTURE_RUN.md](2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING_receipts/CAPTURE_RUN.md#the-gaps-read)):
their wrong values are values heard after some `=` (96 to 100%), usually of the right size, rarely
close. Handed the result's residue, the retired tower wrote sums and differences three times as
often, yet none of 139 four-digit results. Its chart was the reason: the residue `S − p_k` of the
result less its written prefix put the next digit in mode `4 − L + k`, a mode that moves with both
the result's length `L` and the place `k`, and nothing in the residue said which.

## 2. The derivation

[definition; agent-inferred] **The strands.** A stream carries three strands of residues on every
ring of the staircase `q_L = 10^L − 1`, `L = 1..4` (the base's lower neighbours, record §2 of the
generator: ring `L` is the closure's torsion at period `L`), and one orientation `o ∈ {+1, −1}`,
the dyad's sheet. A digit of located turn `θ` acts on each strand by one of the rotor's three laws,
with `μ` the located step's multiplier (10):

```text
turned   r ← μ r + o·θ        a numeral read as its character (the rotor's modulated law)
stepped  r ← μ r              the generator alone (the rotor's free law)
held     r ← r                still (the rotor's upper levels)
```

Any other byte acts by its located key: each strand's new residue is plus or minus one strand's
residue or zero (a transfer, a reflection, or `E(0)`), and the orientation is kept, flipped or set.
The orientation is the dyad `U` of the helical code's dihedral group, `USU = S⁻¹`: a numeral read
between two reflections turns backwards ([guide](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode)).
**No key adds two residues.** The family has no fold.

[derived] **The comparison chart.** Let `A` be held, `G` stepped and `H` turned, with the keys

```text
before the first numeral (w):   H ← 0,                    o ← +1
between the numerals (u, ∘):    A ← H,  H ← 0,            o ← e_∘
at the equals (v):              G ← H,  H ← −A,           o ← +1
```

Then after `x ∘ y =` and the first `k` digits of `z` (their value `p_k`), `H ≡ p_k − μ^k x` and
`G ≡ μ^k e_∘ y`, so the comparison `H − G ≡ p_k − 10^k (x + e_∘ y)`. Write `S = x + e_∘ y`,
`L` its length and `s_k` its unwritten remainder (`S = p_k 10^(L−k) + s_k`). On ring `L`, where
`10^L ≡ 1`, the comparison is `−10^k s_k`, so

- the conjugate of the comparison's face, `e^(2πi·10^k s_k/q_L)`, has as its tenth (the arc of
  the circle cut in ten, `⌊10·10^k s_k/q_L⌋`) the next digit of `S`, at every `k`, in mode 0 of one
  ring;
- writing that digit moves the face by the base's own expanding map `t ↦ 10t − d`, so the written
  numeral is the face's itinerary under the step;
- at `k = L` the ring closes: `H − G ≡ z − S (mod q_L)`, zero exactly where `z ≡ x + e_∘ y`.

[measured] For every `x, y < 1000` and both hands, every positive result below `10^4` (1,496,496
calculations) is written digit by digit from the tenth of ring `L`'s conjugate face and closes ring
`L` at its end; the 3,003 results of all nines are their ring's zero and are excluded
(`strands.py`). The size is the largest ring whose conjugate face at `k = 0` lies outside the first
tenth: true for all 999,993 results below `10^6` on rings 1 to 6 but the five of all nines
(`check.py`).

[derived] **The hand theorem.** Without the orientation, keys acting per byte as signed transfers
leave `y`'s coefficient after a shared `=` the same for every operator: `y` is read into `H` the
same way after `+` and after `-`, and `=`'s key moves it the same way. The hand would then have to
be read by a three-way product at the readout (the operator's face with two strands' faces). With
the orientation the operator's key sets the sheet `y` is read on, and one comparison `H·conj(G)`
serves both hands.

[agent-inferred] **Why this is not the navigator.** The navigator's fold `K ← K + R` formed the
sum in the state, so the tower was handed the result's residue. Here no state ever holds `x ± y`:
`A` holds `x`, `G` holds `±y` stepped, and `H` holds `−x` read against the digits written after the
equals. The sum exists only in the pair contact's product of two strands' faces, whose block the
tower learns (`W(x̄⊗ȳ)`), and a digit exists only in the readout, which the tower learns. The keys
are located; the laws are the rotor's three.

[agent-inferred] **What the readout must learn.** The tenth of a face is a linear read of its
cosine and sine (ten logits `cos(φ − 2π(d + ½)/10)`), and the comparison is one pair-contact block,
so the digit is one fixed read at every step. What remains is which ring: the result's length,
held from the equals to the result's end. The retired chart needed a mode that moved with both.

## 3. Location, with no operator named

[definition; agent-inferred] **The menu.** Every stretch `w x u y v z t` of the training text with
three numerals (maximal runs of digit bytes) and single bytes between and around them, grouped by
its context `(w, u, v, t)`. No byte is named but the digits (the qualification left: a numeral is
still a run of named digit bytes).

**Hands and turns.** The largest group whose rows close under one of the four sign pairs
`(s_x, s_y)` in `s_x x + s_y y − z ≡ 0` (rank falling modulo a prime, the rotor's closure at its
declared period) gives the turns: the kernel line, lifted and gauged at one, as the rotor locates
them. Every group is then read against those turns on each ring and gets the hand under which all
its rows close, or none when no hand or more than one closes it. Ring `L` is the closure's torsion
at period `L`, its primes joined by the Chinese remainder theorem at the same gauge, and `μ` is the
ratio of the located turns of neighbouring modes. The rotor's own menu becomes the closing groups,
each oriented by its hand: this replaces `loops_of`, which read `<<`, `+`, `-`, `=` and `>>` by name.

**Laws and keys.** A symbolic search from rest over the strands' laws (27) and the keys of the
largest closing group's `u` and `v` bytes (1,372 each: 343 signed transfers and 4 orientation
acts), scored first by closure at the end of `z` on ring `len(z)` and then by the next-symbol read
during `z` (the comparison's operands shifted with `z`, so its conjugate face's tenth is `z`'s next
digit), ties to the fewest changed rows. Then each other closing group's bytes with the keys found
held, then every keyed byte on the real stream (the states before `w` read from the text under the
current keys), until no key changes; `w`'s key is located there. Bytes in no menu position keep the
identity. The next-symbol criterion selects among arrangements that all close; it writes nothing.

**The foil** `PRI`: the same strands, laws and turns with every key the identity, so `H` reads every
numeral of the text in one strand and nothing is held.

## 4. The loop, fixed before it is built

**Owners.** `holonics::hnn::tower::Strands` and its join (the faces of each strand on each ring, at
amplitude one, written into twelve modes of the first level past the rotor's rings; those modes
take no push and no move and carry no covector), and the locator in `tower_rotor` (laws `strands`
and `strands-still`). The equations at the consumer are its tests: the chart above from rest; the
locator on a synthetic menu returns the hands of sums and differences, none for products, and the
keys of §2; the faces sit at amplitude one and the other modes move as on the twin; the covector
matches the code difference.

**The run.** `PRK` (the turned rotor with the located strands) and `PRI` (the foil), founded as
`PRT` was and trained three passes together under the waiting standard; `PRT`'s state and read
stand. Before founding, the locator's lines are read: the hands, rings, laws, keys, and the
closures of each group on the real stream.

**The acceptance** is unchanged: never-met calculations right at the equals above the 8-gram's 34
of 876, by the paired line against `PRI` and `PRT`. Beside it: right writes by result length, the
gaps read, the rings, and the level probe at the equals.

**Decisions fixed before the run.**
1. If the located keys close fewer than 99% of the two largest closing groups' calculations on the
   real stream, nothing is trained: the locator is the subject.
2. If `PRK` passes, the capture is learned, and the next loop is the products (the index chart,
   where a product is a sum of turns) and results past four digits.
3. If `PRK` fails but writes never-met sums and differences right above `PRI` and `PRT`, the
   result's length held from the equals is the subject, read by a level probe of the ring that
   closes.
4. If `PRK` writes as `PRI` does, the comparison is not read at the equals, and the pair contact's
   block between two strands is the subject.

**Owed in #410:** the chart (on ring `L`, after `k` written digits the comparison is
`−10^k s_k`, and the ring closes at `k = L` exactly where `z ≡ x + e_∘ y`); the hand theorem; and
the release (the next digit is the tenth of the conjugate face; the size is the largest ring outside
the first tenth).

## 5. The recorded failures this loop could repeat

- **An authored routine standing in for learning.** The check that missed the navigator read "every
  key is located" as "nothing is authored". This loop asks which operation each key keys: signed
  transfers, reflections, clears and the orientation; none adds. The digit laws are the rotor's.
  The sum is the learned contact's product and the digit the learned readout's.
- **Store or copy machinery.** A strand is a mode's phase, held where its key holds it; nothing is
  addressed, filed or looked up.
- **Text run on its codec's grain.** The strands read any declared alphabet in which some classes
  turn, step or hold; the menu is three runs of a located class with single classes between. The
  same carrier reads a beat counted in audio or a stride in motion.
- **Seen material graded as unseen.** The acceptance counts only never-heard calculations.
- **Bits read as progress.** The held-out code is a condition beside the acceptance.
- **A refusal answered with a larger limit.** Deadlines are fixed from measured rates.

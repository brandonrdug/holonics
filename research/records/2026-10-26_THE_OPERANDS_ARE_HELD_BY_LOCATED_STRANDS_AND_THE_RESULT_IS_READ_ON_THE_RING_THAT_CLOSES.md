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

[agent-inferred, October 27] The group that gives the turns is the first, largest first, whose
closure under one hand carries **strictly more** than under every other hand (the product of its
torsion primes at its best step), not the first that closes under any: a group of short numerals
closes modulo 2 under every hand, since the last digit's parity is a character of period one in
the tens and `−1 ≡ 1 (mod 2)`.

**Laws and keys.** A symbolic search from rest over the strands' laws (27) and the keys of the
largest closing group's `u` and `v` bytes (1,372 each: 343 signed transfers and 4 orientation
acts), scored first by closure at the end of `z` on ring `len(z)` and then by the next-symbol read
during `z` (the comparison's operands shifted with `z`, so its conjugate face's tenth is `z`'s next
digit), ties to the fewest changed rows. Then each other closing group's bytes with the keys found
held, then every keyed byte on the real stream (the states before `w` read from the text under the
current keys), until no key changes; `w`'s key is located there. Bytes in no menu position keep the
identity. The next-symbol criterion selects among arrangements that all close; it writes nothing.

[agent-inferred and measured, October 27; amends the paragraph above] **The search as built**
(`tower_rotor::locate_strands`; `locate-strands TRAIN TRAIN_SHA PERIOD` prints its lines alone):

- **A group closes only where its own rows carry the closure**: under its hand, at the located
  step and the period, their rank over the rationals is the count of columns they touch, so the
  turns that close them make the rank modulo each ring's primes fall below it. One calculation is
  `period` rows over as many columns as its digits times the modes; it closes under a hand by the
  arithmetic of one sum and certifies no ring.
- **The two largest closing groups are searched jointly**, their shared bytes enumerated together.
  Searched one at a time, the first group fixes the equals' sheet from rest, where keeping and
  setting it tie, and the second group's results are then read on the sheet its own `u` reversed.
- **A symbol.** From rest, each strand holds after `x u y v` a signed combination of `x` held, `x`
  stepped through `y`, and `y`; a comparison reads the held strands' sum, the moving strands' sum
  and the result's coefficient. The score depends only on that symbol (`5⁷` of them), so each is
  read once per group. A byte that stands only at a `u` is searched by its classes of action from
  rest (54 or fewer), every other byte by all 1,372 keys.
- **A comparison that does not read the result is dead**: on ring `L` every stepped residue returns
  after `L` digits (`μ^L ≡ 1`), so a held and a stepped copy of one operand cancel at every result's
  end and close the ring whatever the calculation.
- **On the stream**, the bytes no symbolic stage located take their keys first, and a key moves
  only on a strictly better score. The symbolic stages read every calculation from rest, and the
  stream's state before `w` is rest only once `w`'s key is located; moved first, a located key
  takes a key that reads the leftover strands. Keyed bytes that stand together with no located
  digit between them act as one key, their composition.

[measured] On a synthetic menu of 30 products, 25 sums and 20 differences (`<<x∘y=z>>`, the test
`the_located_strands_close_the_menu`), the products close under no hand; the sums are the first
closing group, hand `(1, 1)`, the differences hand `(1, −1)` (on 60, 50 and 40, the test
`the_closing_groups_and_their_hands`, the rings are `9, 99, 999, 9999` with `μ = 10` and the turns
the digits). The joint search returns the laws (turned, stepped, held), the
comparison `r_turned + r_stepped`, and the keys

```text
+   turned ← 0,  stepped kept,  held ← −turned,   sheet flipped
-   turned ← 0,  stepped kept,  held ← −turned,   sheet kept
=   turned kept, stepped ← held, held kept,        sheet set to +1
```

which is §2's chart in the other gauge: the operand read last stays in the turned strand and the
first moves to the stepped one, so after `k` digits the comparison is `p_k − 10^k(x + e_∘ y)` with
the sum's `y` read on the reversed sheet. Moved first on the stream, the sums' `u` key took a key
that reads the leftover strands and the stream closed 4 of 45 calculations; with the unlocated
bytes first, `<` takes `turned ← 0` and all 45 close with all 171 digits written right.

[measured] A development read on a local copy of the GSM8K training problems (3,925,837 bytes, not
the PC's training partition; four threads): 30,018 stretches in 457 groups. The products, the
largest group (7,041), close under no hand; the sums `<+=>` (4,266) are the first closing group,
hand `(1, 1)`, carrying `{3, 11, 101}` at step 1 and nothing under the other hands. The rings are
`9` (`μ = 1`, step 0), `99`, `999 = 3³·37` and `9999` (`μ = 10`), the turns the digits. Six groups
close and are carried by their own rows: the sums and differences in the markup (`<+=>` 4,266,
`<-=>` 3,764, and 61 and 59 more ending in `.`) and in the prose (` += `, 39; ` -= `, 28). Eighteen
more close under one hand but are not carried: seventeen of one calculation and one of three
(ranks 4 and 12 against 8 to 32 columns touched). Admitted, they had pulled the space, the
newline, `$`, `(`, `)`, `,`, `/`, `:` and `*` into the keyed bytes and the stream ran 14 s a byte;
that read was stopped past its deadline and is not used. With them refused, stage 1 returns the
synthetic menu's laws, comparison and keys exactly; symbolically every row of the two largest
groups closes (4,150 and 3,694 with a ring; 116 and 70 results longer than four digits have none).
On the stream the space takes `turned ← 0, sheet set to +1` and `<` takes `turned ← 0`; `.`, `>`
keep the identity; the second round changes nothing. **All 8,031 calculations of the six groups
that a ring carries close on the stream**: 7,844 of the 8,030 in the two largest, 97.7%, the other
186 being results longer than four digits, which no ring carries (§6 on decision 1's denominator).
17,234 of 17,382 result digits are the tenth of the comparison's conjugate face (the rest are the results
of all nines, their ring's zero, §2). Wall time 65 s
([LOCATE_DEV.md](2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES_receipts/LOCATE_DEV.md)).

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
the release (for a positive result, the next digit is the tenth of the conjugate face at every
`k < L`, so all `L` digits are read and none stops where the face's itinerary first returns; the size
is the largest ring outside the first tenth; zero is its own case, inside the first tenth on every
ring).

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

## 6. The run: `PRK` writes as `PRI` does, so decision 4 holds

[measured] Brandon's PC, October 26 ([STRANDS_RUN.md](2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES_receipts/STRANDS_RUN.md)).
On the training partition the located keys close all 7,042 calculations of the two largest closing
groups that a ring carries, with 15,480 of 15,613 of their result digits read as §3 says. The two
groups hold 7,204 calculations: the other 162 (100 sums, 62 differences) are results of five or
more digits, which no ring of length 1 to 4 carries (`rows_on` in `tower_rotor` admits no other
exclusion here: every byte of a numeral is a digit and every digit turns).

**Decision 1's denominator** (GPT-6's receipt question). Decision 1 was meant as the keys' closure
on the calculations a ring carries, and was written without naming its denominator; the brief to
the PC read it on those rows (7,042 of 7,042). On all the two groups' calculations it is 7,042 of
7,204, 97.75%, below its 99%: by its own words decision 1 stopped the loop before founding, and the
training went ahead on the rows' reading. The acceptance below is measured either way. A rule fixed
before a run names its denominator.

Both towers trained three passes together, 407 and 409 s against a projection of 646 and 640 s.
They finished at 1.782 (`PRK`) and 1.797 (`PRI`) held-out bits a byte, against `PRT`'s 1.765.

| Right at the equals | `PRK` | `PRI` | `PRT` | 8-gram |
|---|---|---|---|---|
| never-met calculations (of 876) | 16 | 22 | 24 | 34 |
| sums of two numbers, met or not (of 470) | 24 | 24 | 26 | |
| differences of two numbers, met or not (of 388) | 20 | 23 | 28 | |
| all calculations (of 2,448) | 230 | 214 | 240 | |

Paired on the never-met calculations, 14 are right only for `PRK`, 22 only for `PRT` and 2 for
both. Against `PRI` the counts are 9, 15 and 7. The acceptance fails and `PRK` writes no better
than its foil, so **decision 4 holds**: the comparison is not read at the equals, and the pair
contact's block between two strands is the subject.

**How wrong the writes are** (the gaps read, never-met calculations, `PRK`). Of 857 wrong numbers:
- 293 are within a factor of 2 of the exact result, 715 within a factor of 10, and 23 within a
  tenth of it;
- 589 are smaller and 268 larger; none has the opposite sign;
- 853 are results heard after some `=` in training, the commonest 150 (written 120 times);
- the last digit is right for 315 of 816 against a foil's 214 of 811; on 9, 11, 7 and 13 the
  residues match about as often as the foil (95, 65, 85, 55 against 85, 59, 106, 61);
- by result length, 7 of 102 one-digit results are right, 5 of 374 two-digit, 4 of 244
  three-digit, and none of 156 longer.

`PRI` and `PRT` fail the same way. The tower writes a result it heard, of about the right size,
with the last digit above chance. It does not write the sum of the two operands it holds.

**The level probe** (§4's read beside the acceptance; class means over all 64 modes of a level).
At a numeral's last digit, `PRK`'s first level names the numeral's residue more often than `PRI`'s:
1,052 against 681 of 3,810 on 9, 992 against 625 on 11, 1,068 against 716 on 7. The strands are
written and the level carries them. At the equals, the operand read last (`b`) is named well by
both towers: 272 and 239 of 841 on 9, against a majority of 134. The result is named on 9 at 146
against a majority of 92. The operand read first (`a`) is named at 138 against a majority of 143,
and at 335 against 426 on 10, though the held strand carries `−a` exactly from the operator on
(§3's keys, `held ← −turned`), on ring 9 as its residue. The probe weighs every mode by its
modulus. An earlier tower's level read had its loudest modes at an rms of about 3 to 17 times
amplitude one [agent-inferred, to be read on these states], so the strands may be drowned in the
probe as in the tower's read, which normalizes by the level's power.

**Three reads locate the failure before anything is built** (`tools/gsm8k/numeral_rings.py scale`
and `probe … modes=7:19`, and `read-tower-pair-modes`):
1. how loud each mode is at the equals and at the numerals: the strands' twelve modes against the
   rest;
2. the probe on the strands' twelve modes alone (turned 7..10, stepped 11..14, held 15..18, each
   the rings 9, 99, 999 and 9999): whether `a`, `b` and the result are held there at the equals;
3. where the trained contacts' bilinear weight sits, mode by mode
   (`Tower::bilinear_modes`, block `(k, k′) = Σ_o |A_(o,k)|² |B_(o,k′)|²`): the share on each strand
   group's block, and on each ring's turned × stepped pair, the comparison's own block.

**Decisions fixed before the reads** [agent-inferred, each from the chart]:
- 4a. If the strands-only probe names `a` and `b` on 9 at the equals for 90% or more, but all 64
  modes do not, and the strands' rms is a quarter of the other modes' or less, then the strands are
  drowned. The next loop writes their faces at the level's power, the gauge the read divides by,
  not at amplitude one, and runs again.
- 4b. If the strands are not drowned but the turned × stepped block of each ring holds no more
  than its equal share of the bilinear weight, then the comparison's block never forms. The
  contact opens at `W_b = 0`, and result digits are about 0.4% of the bytes. The next loop opens
  the contact on the located comparison, `r_turned + r_stepped` (§3), the locator's own return.
- 4c. If the strands-only probe does not name `a` on 9, then the strands do not hold the operand on
  the stream where §3 says they do, and the join of the strands to the level is the subject.

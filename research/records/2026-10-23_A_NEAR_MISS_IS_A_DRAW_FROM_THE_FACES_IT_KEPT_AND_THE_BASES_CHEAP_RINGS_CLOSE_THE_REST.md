# A near miss is a draw from the faces it kept, and the base's cheap rings close the rest

**Date:** 2026-10-23. **Occasion:** Athena, trained on generated sums, differences and products
(design thread, #404), wrote held-back results such as `92*65=6090`, `83*27=2309`, `46*15=850`,
`12*35=405`, `71+41=102`, `74-72=1` and `99-56=5`. Brandon read them that afternoon:
- the products are all in the right neighbourhood and slightly off, and so is the language;
- `+` and `−` seem to decide how the result's length expands or contracts, and `99-56=5` looks like a
  result shortened too early, with its 5 taken from `9 + 6 = 15`, a literal slip;
- the last digits of the sums are right while the next place is not, so the release is not yet a
  recursive induction moving coupled edges and corners;
- the law being approached is about faces and combinatorial potentials, like thermodynamics and
  path integrals integrating into complete structures; generalized as conservation of faces and of
  their compositions, it becomes a mechanism of critical thinking once the machine can reconfigure
  its own releases, with no authored "right" or "wrong".

This record derives the near misses at the level of the
[association record](2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER.md):
a number is a word of turning digits at a level of the base's tower, and associating faces evaluates
the constraint up to its fibre. (`73+31=104` is correct.)

**Joins.** `arith.association-is-evaluation` (the fibre `Fib_q`), `radix.cheap-faces` (Lean
`Mathematics/RadixWindowReceiver:cheap_faces`), `radix.digit-convolution` and
`radix.carry-cascade-consumer` (Lean `Mathematics/ArithmeticContract`), `radix.leading-fibre`,
`radix.euclidean-chart` (Lean `Foundation/EuclideanResidueTransport`),
`radix.difference-leading-cancellation`, `radix.carry-chain-eulerian`, `linalg.relational-preimage`
(a middle constraint enters as an intersection), `motion.lag-residue-factorization` (which modes read
which faces), and the
[rereading record](2026-10-22_THE_NATIVE_CONTACT_STEP_IS_CERTIFIED_BY_REREADING_THE_SAME_COMPARISON.md).

## 1. The law

A reader that has located some faces of a result writes a value from the intersection of those
faces' fibres. Where a face is missing, the value can land anywhere in what is left. That is a near
miss: right on every face it kept, off on the face it did not. The answer is the intersection of all
the faces the operands fix, and evaluation is reached when that intersection is one point
(`arith.near-miss-kept-face-fibre`).

## 2. Each operation is first learned where it is one crossing

A number has two charts: its size (`log_b n = level + leading phase`) and its cycles (residues on
`ℤ/q`).
- A product is one crossing in size, `log xy = log x + log y`. Its size is right on 19 of the 20
  products the design thread read. On the cycles it is a pair contact, and the units' cycle
  `ℤ/10 = ℤ/2 × ℤ/5` is two crossings that can be kept separately: `12*35=405` keeps the 5-axis and
  loses the 2-axis, `83*27=2309` keeps the 2-axis and loses the 5-axis.
- A sum is one crossing on every cycle, `(x + y) mod q`. Its units are right. In size it crosses
  through the carries.
- A difference is one crossing on the cycles too, with the second operand turned by the half-turn
  (`−y`). In size its leading face is not conserved (`radix.difference-leading-cancellation`), so the
  result's length, its stair, is the last thing the operands fix.

So products land in the neighbourhood and sums get the last digit: each is right in the chart where
it is a single crossing, and that chart is learned first.

## 3. The middle is hot because many paths feed it

A product's digit at place `k` is `(c_k + carry_k) mod b` with `c_k = Σ_(i+j=k) x_i y_j`. The units
are fed by one path, the middle by the most, and the carry brings every path below. Paths the reader
has not read add independent turns to the digit, whose distribution is their convolution: its Fourier
coefficients multiply, so each unread path flattens it, and its collision entropy is
`H₂ = log₂ b − log₂ Σ_m |P̂(m)|²` (`radix.digit-path-heat`). The digit thermalizes. The design thread
read the product's tens at about 3.3 bits, which is blind.

The base has rings where this does not happen. On `ℤ/q` with `q | b − 1` the base does not turn,
`b ≡ 1`, so every path lands in phase and the whole product is one crossing of the operands' digit
sums. With `q | b + 1` the base is a half-turn, `b ≡ −1`, and the paths alternate in phase. On
`ℤ/101` the base is a quarter-turn (`b² ≡ −1`). Carries drop out on all of them
(`radix.cheap-ring-path-collapse`). Epime's review of the association record states the same thing
as an operational quotient, `q T_a = S_a q`: in a linear chart with a lift `P` and the detail `d` a
face does not see, `c' = C T_a P c + C T_a d + C b_a`, and `C T_a d` is the detail the operation
promotes into the coarser face. A carry is that promotion: lower paths feeding a higher place. On the
cheap rings it vanishes and the face is conserved; at the middle place of a product it is largest.
Each ring divides the remaining fibre by its size. For the 8,100
two-digit products, with the size read as the lengths and one leading digit of each operand:

| Faces kept | Fibre closed to one value | Largest fibre | Mean `log₂` fibre |
|---|---|---|---|
| size | 0 | 1,702 | 9.844 |
| + ring 10 (units) | 0 | 171 | 6.524 |
| + ring 9 (digit sum) | 0 | 19 | 3.353 |
| + ring 11 (alternating sum) | 7,100 | 2 | 0.123 |
| + ring 101 | 8,100 | 1 | 0 |

`92·65`: 1,432 values in the size fibre, 144 with the right units, 16 with the right digit sum, then
5,980 alone. All four products Brandon named are inside the size fibre and all four are off on
ring 9; `6090` keeps ring 11 by chance (1 in 11).

The cost a reader pays per place of a product (operands 0 to 99, leading digit first, in bits; blind
is 3.32) falls the same way when the reader holds the result's ring faces, each predicted from the
operands by one crossing:

| Faces held | thousands | hundreds | tens | units |
|---|---|---|---|---|
| size | 0.667 | 2.270 | 2.498 | 0.753 |
| + ring 2 | 0.659 | 2.229 | 2.094 | 0.445 |
| + ring 5 | 0.621 | 1.996 | 1.282 | 0.094 |
| + ring 10 | 0.572 | 1.704 | 0.925 | 0 |
| + ring 10, ring 9 | 0.299 | 0.618 | 0.024 | 0 |
| + ring 10, ring 9, ring 11 | 0.001 | 0 | 0 | 0 |

This is the path integral and the thermodynamics in Brandon's lens, read exactly: on a generic ring
the paths dephase and the place is hot; on the base's cheap rings they add in phase and the whole
structure is one crossing; the intersection of a few such faces is the complete value.

## 4. The sums and differences

- `71+41=102`. The units `1 + 1 = 2` are right. At the tens `7 + 4 = 11` is one turn plus a residue
  of 1. The draw kept the turn (the hundreds' 1) and lost the residue (it wrote 0). The Euclidean
  chart `x ↦ (x mod m, ⌊x/m⌋)` loses nothing (`radix.euclidean-chart`); the draw kept the quotient
  and dropped the remainder. `23+51=84` is the converse: a turn added at the tens where none
  climbed.
- `74-72=1`. The operands share their leading digit, so the size fibre is `[0, 9]` and only the
  units crossing `4 − 2` can fix the result. The design thread read that it knew the result is one
  digit (the line end cost nothing) and treated its first written symbol as a size: the 1 means
  "small", not a subtraction.
- `99-56=5`. The size fibre is `[31, 49]`, two digits; the draw is one digit, a stair dropped
  before the size was read. Its 5 is the units of `9 + 6`, as Brandon saw: the units crossing with
  the half-turn on the second operand missed. One draw cannot settle where the 5 came from; the test
  is how often a wrong difference's units equal the units of the sum, against 1 in 9.
- `56+3=56` copies the first operand and drops the one-digit operand standing on the units.

Every miss above is off on ring 9; every correct draw (`85-42=43`, `73+31=104`, `8+82=90`,
`47-20=27`) is on it.

## 5. The reread closes the loop

The fibre closes when the release is read back through the same faces. The loop is: compose the
result's faces from the operands' faces (each one crossing on its ring), release, read the release's
own faces with the same modes, and redraw inside the fibre of any face that disagrees. Nothing
authors the answer. The judge is agreement between the faces the operands compose and the faces the
release carries, a mutual comparison in which either side can be the one that moves. A missing face
is then not a wrong answer but an open fibre, and the redraw is the intersection
(`linalg.relational-preimage`).

The modes that read these faces are ones the HNN already has.
`motion.lag-residue-factorization` says that a stream of moves sharing one linear part `M` of order
`N` reaches a state fixed by its symbol counts per lag residue. With the place step `M ≡ b` on `ℤ/q`:
- `M = 1` on ring 9: the state is the digit sum, read by a ring that does not turn;
- `M = −1` on ring 11: the state is the alternating sum, read by the half-turn, the parametron's
  locked sheet;
- `M` a quarter-turn on ring 101.
The result's face is a conjunction of the two operands' faces, so it needs a pair contact (the same
row's last clause). These are navigators of the machine's own kind, located from its passage; an
authored digit-sum routine would be catered machinery.

The same law holds for language. A reply keeps the faces its context fixes: the names, the numbers,
the subject, the tense. A near miss in language keeps some of them and loses one. Rereading one's own
release against the faces its antecedents compose is the general critic: conservation of faces
across a composition, with the plural fibre kept where the faces do not close it.

## 6. What the design thread builds

- The duplex the design thread chose (a second strand reading right to left, meeting the first at
  every place through a pair contact, and a release that redraws any place until its own faces
  agree) is the reread above. Its fixed claim (a product's tens well below blind, products matching
  mod 9 and mod 11 above chance) reads directly against the tables in §3.
- Holding the result's faces before the release (composed from the operands' faces through a pair
  contact) gives a leading-first reader the gain at every place, not only the last (§3's second
  table).
- Readings at every place over all held-back problems: the share inside the size fibre; the units'
  2-axis and 5-axis hit rates separately; the ring 9 and ring 11 hit rates before and after a
  reread; the half-turn test on differences; at a sum's tens, how often a wrong digit keeps the turn
  and loses the residue.

## 7. Owed

- Lean: `radix.cheap-ring-path-collapse` (the convolution's value on `q | b ± 1` is the product of the
  operands' cheap faces), from `cheap_faces` and the digit convolution (#410).
- The readings in §6 on the trained machine.

## Receipts

[`2026-10-23_A_NEAR_MISS_receipts/`](2026-10-23_A_NEAR_MISS_receipts/): `faces.py` (each draw's kept
and lost faces, and per-place costs of sums and differences), `intersect.py` (fibre closure by the
cheap rings), `rings.py` (per-place product cost with ring faces held), their JSON outputs, and
`RUN.md`. Exact integer work; the entropies are exterior readings.

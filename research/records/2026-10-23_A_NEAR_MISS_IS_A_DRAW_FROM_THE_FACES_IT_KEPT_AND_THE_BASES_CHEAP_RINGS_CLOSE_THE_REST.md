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
which faces), `tower.scale-square` and `winding.carry-cocycle` (the carry's composition),
`norm.laplacian-return` (a face's learned return), `receipt.finite-mixed-difference`, and the
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
- A sum is one crossing on every cycle, `(x + y) mod q`, in the phase chart. Where the reader makes
  that crossing its units are right (see the correction below). In size it crosses through the
  carries.
- A difference is one crossing on the cycles too, with the second operand turned by the half-turn
  (`−y`). In size its leading face is not conserved (`radix.difference-leading-cancellation`), so the
  result's length, its stair, is the last thing the operands fix.

So products land in the neighbourhood and sums get the last digit: each is right in the chart where
it is a single crossing, where the reader makes that crossing.

**Correction (October 24, amended the same day).** The first version of this section read a sum's
units as right from the lines quoted above (`71+41=102`, `73+31=104`, `8+82=90`, `23+51=84`),
written by a machine trained on arithmetic alone, and concluded that each operation is learned first
in the chart where it is one crossing. Counted over whole writings, this holds where the reader makes
the crossing and fails where it does not:
- **Arithmetic alone.** The pumped tower of the
  [terrain record](2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_THE_TOWER_COMPUTES_WHAT_IT_NEVER_MET_WHERE_IT_KNOWS_THE_LEVEL.md)
  writes a sum's units right in 191 of 240. Of the 49 misses, 36 keep the parity, so its misses fall
  on ring 5 of `ℤ/10 = ℤ/2 × ℤ/5`. The design thread's per-mode read (October 24; its receipts go
  with the tower record) locates the crossing. The tower crosses the two operands' units when the
  second one arrives, and the sum's units then read straight from its state, at the second operand's
  cell in its lower level, in 370 of 495 held-out sums (459 at the units cell, upper level).
- **Mixed text.** The towers trained on the Holonics text beside the digits write a sum's units at
  chance. The design thread counted every whole equation in the 37 digit-prompt writings of its tower
  record (`tools/answer_digits.py`;
  [`ANSWER_DIGITS.txt`](https://github.com/brandonrdug/holonics/blob/f6a54bc37/research/records/2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK_receipts/ANSWER_DIGITS.txt),
  commit `f6a54bc37`), and the count reproduces exactly from the committed writings:
  - a sum's units are right in 44 of 400 and a difference's in 16 of 135. Where a sum is written at
    its length, its units miss by every step of `ℤ/10` about equally (27 to 50 times each, against 41
    right). The parity is right in 205 of 400 and the residue mod 5 in 83 of 400, both at chance
    (200 and 80; `units_rings.py`).
  - by the same per-mode read, at the cell where the second operand's units arrive, the mixed pair
    tower's lower level (seventh pass) holds both operands' units (476 and 495 of 495) but reads the
    sum's units from them in 134. At the result's units cell its lower level holds the first
    operand's units in 375, the second's in 492 and the sum's in 84, and its upper level 215, 369
    and 79. All counts are of 495 held-out sums, the commonest class at 63. Corrected October 24
    from the design thread's probe outputs, whose receipts go with the tower record.
  - the size is still placed. The length is right in 744 of 804 equations. A sum that carries into
    the hundreds is written at its length 210 times of 218, with its leading 1 right in 209 of them.
    A product's length is right in 238 of 269. A sum's tens is right in 190 of 380 and off by one in
    168 of the rest, the carry from the units.

So §2 stands where the crossing is made. A sum's units are one crossing in the phase chart,
`□((a + b)/q) ≡ 0` (§7). A reader that composes the two operands' unit phases when the second
arrives places them. A reader that holds both strands without composing them must read the units as
one of ten classes, which costs interaction rank 9
([faces on cycles](2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md)),
and it writes them at chance. Holding both strands is not enough without the crossing
[agent-inferred].

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

## 6. The reading order moves where a face pays, not what it pays

The design thread asked which faces a reader that writes left to right can locate, and which need a
reading of every place given all the others. The chain rule answers it. For held faces `F` and any
reading order `σ` of the word's places,
`H(W | F) = Σ_k H(d_σ(k) | d_σ(<k), F)`, so the code of the result given what the reader holds is the
same in every order, and a held face `q` gains `I(W; q | F)` in every order. The order only decides at
which places the gain is paid: the places it leaves free (`radix.held-face-reading-order`).

Products of operands 0 to 99, padded to four places (bits; places from the units):

| Faces held | Leading first | Units first | Each place given all others | Whole word |
|---|---|---|---|---|
| size + ring 10 | 0, 0.902, 1.545, 0.426 | 0, 2.182, 0.689, 0.002 | 0, 0.902, 0.502, 0.002 | 2.873 |
| + ring 9 | 0, 0.023, 0.551, 0.224 | 0, 0.789, 0.009, 0 | 0, 0.023, 0.001, 0 | 0.798 |
| + ring 11 | 0, 0, 0, 0 | 0, 0, 0, 0 | 0, 0, 0, 0 | 0 |

Read leading first, ring 9 pays 0.879 bits at the tens, 0.994 at the hundreds and 0.202 at the
thousands: not only at the last place. So a reader that writes left to right can locate a ring face,
on one condition: it holds the face composed from the operands, `T_q(q a, q b)`, before it writes. A
face of its own release alone gains nothing in any order, since it is a function of what is already
written; it gains only against the operands' composition. The tens of a product are blind in the
measured tower because that composition is not held, not because of the order.

A one-sided reader carries its own release's face as it writes. On `ℤ/q` the face of a word read
leading first is the fold `x ↦ b x + d` (Horner; Mathlib `Nat.zmodeq_ofDigits_digits`), the
lag-residue mode with `M ≡ b`: no turn on ring 9, a half-turn on ring 11, a quarter-turn on ring 101.
The same mode reads the operands' faces, and a pair contact composes them.

Each place given all the others is not a code: its sum (0.024 bits with ring 9) is far below the
word's 0.798. It is the consistency read of the reread: with the faces held, every place is pinned by
the others, so a place whose cost stays high marks the fibre of a failing face, and the learning
covector arrives at every place instead of only the free ones.

**Conservation of faces** is the right name for the law `q ∘ T = T_q ∘ (q × q)`. Every residue ring
is conserved by `+` and `×` (a ring homomorphism), and carries drop out on all of them. What makes 9,
11 and 101 the base's cheap rings is the shortest place period, `ord_q(b) = 1, 2, 4`; ring 7 is
conserved as well but its place mode has period 6. The size is conserved by `×` only up to its
enclosure (`radix.leading-fibre`), and not by `−` (`radix.difference-leading-cancellation`).

**The consumer equation.** For every located face `q`:
`x_q(release) = T_q(x_q(a), x_q(b))` on `ℤ/q`, with `x_q` the fold `x ↦ b x + d`, `T_q` the
operation on the ring (a pair contact for `×`), and the residual `ρ_q = x_q(release) − T_q(x_q(a), x_q(b))`
read through the ring as the phase `e^(2πi ρ_q/q)`. A release is closed when every `ρ_q = 0`; the
reread redraws inside the fibre of a face with `ρ_q ≠ 0`.

## 7. A face needs a pair contact exactly where its four-cycle does not vanish

Epime's second review of this record adds three statements, and each holds. The learned return is a
law the repository already owns, the carry's composition generalizes one it owns, and the binding is
new.

**The binding.** For a face `G(a, b)` of a two-operand operation, the four-cycle
`□G = G(i, j) − G(i, l) − G(k, j) + G(k, l)` vanishes on every rectangle exactly when
`G = f(a) + g(b)`. Then each operand's own face, transported, composes the result by one crossing and
no contact is needed. A nonzero four-cycle is what neither operand shows alone, and it is what a pair
contact carries. Every rectangle is a signed sum of unit squares, so unit squares decide. For
operands 0 to 99 (`binding.py`):

| Face | Chart | Unit squares with `□G ≠ 0` (of 9,801) | Where the binding sits |
|---|---|---|---|
| sum, ring 9, 10 or 11 | phase `(a + b)/q` | 0 | nowhere: `+` is one crossing on every ring |
| sum, tens digit | phase on ring 10 | 1,961, values `±1/10` | every one straddles a carry line `a + b = 10m` |
| product, ring 10, 9, 11 or 101 | phase `ab/q` | 9,801, all equal to `1/q` | everywhere, one constant: the ring's pairing |
| product, units of `ℤ/q` | index (a primitive root) | 0 | nowhere: the index chart makes `×` one crossing |
| product, size (number of digits) | integer | 130 | every one straddles a hyperbola `ab = 10ᵏ` |

This is the exact form of §2: an operation is one crossing in the chart where its four-cycle
vanishes. The binding is not spread evenly. A sum needs none except where the units carry, on the
additive caustic, and a product's size needs none except on its multiplicative caustic. A product's
ring face carries one constant, `□(ab/q) = (i − k)(j − l)/q`, so a pair contact for `×` on ring `q`
holds one number: the ring's pairing. On the units of the ring the index chart removes even that,
and what still binds are the operands that share a prime with `q`, where the product collapses
(`radix.multiplier-face-action`). The four products Brandon named keep their size, which binds only
on its caustic, and lose ring 9, which binds on every square.

**The carry composes along a passage.** Epime writes a coarse reading's defect as
`q T_a = S_a q + D_a`. Then `q T_b T_a = S_b S_a q + D_b T_a + S_b D_a`: the defect of a composite is
the outer defect read at the inner's output plus the inner defect carried by the outer coarse map. It
is an identity of the operator ring, the composition law of the scale square's defect
(`tower.scale-square`, Lean `Holon/Restriction:squareDefect`), checked on rational matrices
(`compose.py`). Its additive instance, with `q` the winding, `T_a = +a` and `S_b` acting on a defect
by its linear part (the identity), is the carry cocycle `carry(x, a) + carry(x + a, b) = carry(a, b) + carry(x, a + b)` (`winding.carry-cocycle`,
formal-checked). A carry changes a word's digit sum by `−(b − 1)` and its alternating sum by
`±(b + 1)`, so on the cheap rings it composes to nothing (§3).

**The learned face's return.** A reader that weighs its located faces by a normalized exponential,
`m = Σ p_i φ_i`, returns to face `i` the covector `p_i Re⟨g, φ_i − m⟩`: its weight times how much
more it agrees with the downstream covector `g` than the mixture does. This is the normalized
exponential's Laplacian return (`norm.laplacian-return`) with `δ_i = Re⟨g, φ_i⟩` (checked in
`compose.py`). It sums to zero, so it moves only the faces' relative weights. Its consumer is the face
selection in the design thread: a ring face is located by this return, never authored.

## 8. What the design thread builds

- The duplex the design thread chose (a second strand reading right to left, meeting the first at
  every place through a pair contact, and a release that redraws any place until its own faces
  agree) is the reread above. Its fixed claim (a product's tens well below blind, products matching
  mod 9 and mod 11 above chance) reads directly against the tables in §3 and §6.
- By §6, the duplex reads consistency and spreads the covector, but it does not create a face that
  is not held. The face that the tens needs is the operands' composition on ring 9 and ring 11,
  held at the release; a leading-first reader holding it pays the gain at the tens and hundreds.
- By §7, the pair contact for `×` on ring `q` carries one constant, the ring's pairing; sums need
  a contact only across a carry, on the caustic.
- Readings at every place over all held-back problems: the share inside the size fibre; the units'
  2-axis and 5-axis hit rates separately; the ring 9 and ring 11 hit rates before and after a
  reread; the half-turn test on differences; at a sum's tens, how often a wrong digit keeps the turn
  and loses the residue.

## 9. Owed

- Lean: `radix.cheap-ring-path-collapse` (the convolution's value on `q | b ± 1` is the product of the
  operands' cheap faces), from `cheap_faces` and the digit convolution, and
  `radix.held-face-reading-order` (the fold reading of a word's face; a held face's gain is the same
  in every order), `arith.binding-four-cycle` (`□G ≡ 0 ⇔ G = f(a) + g(b)`; `□(ab/q) = (i − k)(j − l)/q`)
  and `tower.square-defect-composition` (`squareDefect π (B_f A_f) (B_c A_c) = squareDefect π B_f B_c · A_f
  + B_c · squareDefect π A_f A_c`) (#410). Formal-checked on October 26, except the gain: in
  [`Mathematics/CheapConvolution`](../../lean/HolonicsResearch/Mathematics/CheapConvolution.lean)
  the collapse in any commutative ring, so on every `ℤ/q` (`conv_face_of_one`,
  `conv_face_of_neg_one`), the carries dropping out (`carried_product_face_of_one`,
  `carried_product_face_of_neg_one`, `nine_face`, `eleven_face`) and the leading-first fold
  (`face_is_fold`); in [`Mathematics/BindingFourCycle`](../../lean/HolonicsResearch/Mathematics/BindingFourCycle.lean)
  the binding (`fourCycle_eq_zero_iff`, `unit_squares_decide`, `fourCycle_mul_div`,
  `unit_square_mul_div`, `fourCycle_of_hom`) and the defect's composition (`squareDefect_comp`).
  Still owed: a held face's gain `I(W; q | F)` is the same in every reading order.
- The readings in §8 on the trained machine.

## Receipts

[`2026-10-23_A_NEAR_MISS_receipts/`](2026-10-23_A_NEAR_MISS_receipts/): `faces.py` (each draw's kept
and lost faces, and per-place costs of sums and differences), `intersect.py` (fibre closure by the
cheap rings), `rings.py` (per-place product cost with ring faces held), `order.py` (the same cost in
three reading orders), `binding.py` (the four-cycle of each result face), `compose.py` (the defect
composition, the carry cocycle and the face return, exactly), `units_rings.py` (§2's correction: a
written sum's units on ring 2 and ring 5), their JSON outputs, and `RUN.md`. Exact integer work; the entropies are exterior readings.

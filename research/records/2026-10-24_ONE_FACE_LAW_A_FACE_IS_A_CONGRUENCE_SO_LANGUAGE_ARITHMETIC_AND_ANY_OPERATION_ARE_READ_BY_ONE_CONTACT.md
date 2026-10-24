# One face law: a face is a congruence, so language, arithmetic and any operation are read by one contact

Refs #404 #405 #410. Follows [association is evaluation](2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER.md),
[the near miss](2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md),
[the pocket of reducibility](2026-10-23_A_POCKET_OF_REDUCIBILITY_IS_A_FACE_THAT_COMMUTES_WITH_THE_STEP_AND_THE_RECEIVERS_CHART_DECIDES_WHICH.md)
and [the lap](2026-10-23_A_MOMENT_IS_A_LAP_AROUND_A_SINGULARITY_AND_LOOKING_AGAIN_CLOSES_THE_CHECK_LOOP_ON_ANOTHER_FACE.md).
Status: the law is proved-standard (universal algebra); the census is exact; the build form in §4 is
[definition; agent-inferred, October 24].

Brandon's lens (paraphrased, October 24): conservation of faces simply works out, and it generalizes
across what language and arithmetic have in common and across arbitrary mathematical operations. The
Athena design should not center on arithmetic. The October 23 records stated the law on integers;
this record states it once for any operation, shows its language and general instances, and gives the
design the one mechanism it implies.

## 1. The law

An operation `T` takes operands to a result (binary below; every arity reads the same). A face `q` is
a receiver's reading, a quotient of what it reads. `q` is **conserved** by `T` when the result's face
is a function of the operands' faces:

```text
q(T(x, y)) = T_q(q(x), q(y))
```

Equivalently, `q x = q x'` and `q y = q y'` imply `q(T(x, y)) = q(T(x', y'))`: the kernel of `q` (the
pairs it cannot tell apart) is a **congruence**, an equivalence compatible with the operation, and
`q` is a homomorphism onto the quotient algebra. The repository already owns this law in four charts,
which are one statement:
- for a binary operation, association is evaluation exactly where every fibre `Fib_q` is one point
  (`arith.association-is-evaluation`);
- for a step `A`, it is the commuting scale square `π A = A_c π`, whose defect is the irreducibility
  at that reading (`tower.scale-square`, formal-checked; a pocket of reducibility);
- for the word monoid it is a representation `E T_a = U_a E` (`encoding.reduced-recurrence`): a
  mode's state of a concatenation is composed from its parts' states, `M(xy) = M(y) M(x)`;
- the coarsest reading that still separates every admitted future is the retention quotient, which
  on words is the Myhill–Nerode right congruence (`tower.minimal-realization`; StandingLaw,
  formal-checked).

Conservation of faces, read in these terms, is the statement that a receiver reads any algebra through
its congruences. Three consequences follow for every operation. Each was first stated on integers:
1. **Kept faces and the fibre.** A release that holds the faces `Q` lies in their joint fibre, and a
   near miss is a draw from the fibre of a face it lost (`arith.near-miss-kept-face-fibre`).
2. **Closure.** A family of conserved faces that is jointly injective on the window reads `T` there
   (`arith.association-is-evaluation`). On integers this is the Chinese remainder theorem; for a
   general algebra it is Birkhoff's subdirect representation. The check loop
   `δ_q = q(r) − T_q(q(a), q(b))` and its laps (`arith.check-loop-laps`) are the same for any
   operation.
3. **Binding.** A face that is not conserved needs a pair contact, and its four-cycle locates where
   (`arith.binding-four-cycle`). The refinement that conserves it adds the state at the seam: the
   carry in arithmetic, the seam state in language (§2). On words the coarsest conserved refinement
   is the syntactic congruence.

## 2. Language

Text is an algebra of composition. Concatenation joins spans, and the text also states relations
between spans far apart: a name and its later use, a subject and its verb, a definition and its use,
a function and its argument, an equation's two sides.

**Concatenation** (`faces.py`, all 14,641 = 11⁴ pairs of words of length 0 to 4 over `{t, h, a}`).
Every mode of the tower is a face of concatenation by construction. Its state after `xy` is set by
its state after `x` and the span `y` (a right congruence), and the span's accumulated transfer,
Epime's prefix read, composes on both sides (a congruence).
- Conserved: length, length mod 2, the count of `a` mod 3, and the last letter (no plural fibre).
- Not conserved: "contains `th`". One face pair, neither operand containing `th`, has a plural fibre,
  because `t` + `h` makes `th` across the seam. Over the 3,025 = 5²·11² rectangles of `th`-free words
  of length 1 and 2, its four-cycle is nonzero on 784 = 2⁴·7², and every one of them has a `t|h` seam.
- Refined: carrying the seam state (ends in `t`, starts with `h`) and the unit (the empty word)
  conserves it: 81 face pairs, none plural.
- A reader going left to right keeps the right congruence. Refining "contains `th`", it has exactly
  three classes over 1,093 words and 121 suffixes: no `th` yet, no `th` yet but ending in `t`, and
  has `th`.
- A contact joining two spans needs the two-sided (syntactic) congruence. It has six classes over the
  same words with 40 contexts on each side: the empty word, has `th`, and the four `th`-free classes
  by whether the span starts with `h` and whether it ends in `t`.

That seam state is language's carry: a boundary state that crosses the join, just as a digit's carry
crosses a place.

**Relations at a distance.**
- A copied name, number agreement between a subject and its verb, a rhyme and a repeated quantity
  are all faces whose `T_q` is the identity on one operand's face, read at a located offset. The node
  lock (`hnn.passage-node-lock`) and the copy contact (`hnn.unit-copy-contact`) are this case. On the
  first 1,000 GSM8K problems the located equality saved most in prose, where the answer restates the
  question's words: answer prose fell from 1.580 to 1.466 bits a byte, while new question digits rose
  from 4.338 to 4.540 ([the sheaf record §8](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md)).
- In Lean and Rust an application's type face is composed from the two types alone: `A → B` applied
  to `A` gives `B`, a cancellation like `B/A · A = B` (the ratio object). Lambek's categorial grammar
  reads English the same way: a noun phrase `np` followed by a verb phrase `np\s` gives a sentence
  `s`. The census has 14 types, 196 pairs and 12 well typed.
- Meaning composed from the meanings of parts (Frege, Montague) is the same statement: a meaning is a
  face conserved by the grammar's operations. An idiom is where it fails: its four-cycle is nonzero
  and a pair contact carries the binding.
- Two spans are interchangeable in every context exactly when they are equal in the syntactic
  congruence. This is the exact form of distributional classes (Harris), and it is what retention
  keeps.

## 3. Arbitrary operations

Each line is exact over the stated finite set (`faces.py`).

| Algebra | Conserved | Not conserved | What conserves it |
|---|---|---|---|
| 2×2 matrices, entries −1, 0, 1, product (81 matrices) | `det`: 25 face pairs, none plural | trace: 25 of 25 plural; trace with `det`: 218 = 2·109 of 256 plural | `tr(AB) = ⟨A, Bᵀ⟩`, a pairing of the whole operands (all 6,561 = 3⁸ pairs): a pair contact |
| polynomials of degree ≤ 2, coefficients −1, 0, 1, product, read at 2 (27) | value: 225 = 3²·5² face pairs, none plural | derivative alone: 80 = 2⁴·5 of 81 plural | the jet (value, derivative): 729 = 3⁶ face pairs, none plural; Leibniz on all 729 |
| permutations of 4 points, composition (24) | sign: 4 face pairs, none plural | cycle type: 14 of 25 plural | the permutation itself |
| integers, sum and product | ring faces (`radix.cheap-ring-path-collapse`) | a product's tens digit, a sum's tens across a carry | the carry, the cheap rings |

- The derivative is conserved once it carries the value, as a digit is once it carries the carry. The
  chain rule reads the outer jet at the inner value, a contact at a located address. Forward jets are
  formal-checked (`motion.selected-move-forward-jet`), and the shifted Leibniz rule is owned
  (`series.shifted-leibniz`).
- In other modalities the same law reads the native operations:
  - an image's translation turns its Fourier phases additively, so a phase is a conserved face (a
    character);
  - an acoustic transposition turns pitch class on `ℤ/12` and keeps the octave as its level, so a
    pitch is a word at a level as 12,400 is 124 at level 2;
  - a motor word of screws keeps its lag residue face (`motion.lag-residue-factorization`).

## 4. What it means for Athena

One mechanism serves every section of the text the tower hears (prose, Lean, Rust and arithmetic,
then images, sound and motion):
1. **Faces are located, never authored.** A located face is a mode, a representation of
   concatenation, whose read of a span is composed from its parts' reads. Epime's prefix transfer
   read (`a, b, c`, composed by `modulatedCarrier_compose`) is this composition for one pumped mode,
   and it is the two-sided read a contact between spans needs.
2. **One pair contact.** At a located key (the offset where a related span sits), the contact predicts
   the later span's face from the earlier spans' faces, `r̂ = W(x̄ ⊗ ȳ)` with `x̄ = (x, 1)` and
   `ȳ = (y, 1)`, the contact of Epime's review. Its small table `T_q` is `W`, deposited from the slips.
   `W` has four blocks:
   - constant;
   - one operand alone: copy, agreement, rhyme, a type's codomain;
   - additive: lengths, digit sums, a sum's ring faces, transposition;
   - bilinear: a product's ring faces, typed application, the trace of a product.

   The four-cycle, read from the passage, says which block a face needs. Nothing chooses the block
   per section.
3. **One slip.** `δ = q(r) − r̂` is the same in every section. It is the lap's check (looking again
   reads one more located face) and the covector the contact deposits.
4. **Acceptance with one law.** The lock (`λ` grows or holds, `F*` falls or holds at 0) is read at the
   contact cells and reported per section. A face that pays in several sections is a commonality
   between them; a face that pays in one section is that section's chart. Arithmetic is one section,
   the cleanest probe of the bilinear block, and never the subject.

The recorded failures this avoids:
- an authored routine standing in for learning: no `T_q` is written, and `W` is deposited;
- text as the exception: the law is stated on the algebra, and the census covers words, types,
  matrices, polynomials and permutations beside integers;
- a design thought in arrays: faces are congruences and modes, and the contact is a pairing.

## 5. Owed Lean

One box in #410:
- `q` is conserved by `T` iff it respects `T` on equal faces iff some `T_q` has `q ∘ T = T_q ∘ (q × q)`;
  its kernel is then a congruence (Mathlib `Con`) and `q` factors through the quotient;
- conserved faces jointly injective on a window read `T` on that window (subdirect closure, with the
  Chinese remainder theorem as the integer case);
- the coarsest conserved refinement of a face of concatenation is its syntactic congruence; for
  "contains `th`" over `{t, h, a}` it has six classes, and the right congruence a left-to-right
  reader keeps has three;
- the jet face is conserved by products (Leibniz, dual numbers), and `tr(AB) = ⟨A, Bᵀ⟩`.

## Receipts

[`2026-10-24_ONE_FACE_LAW_receipts/`](2026-10-24_ONE_FACE_LAW_receipts/): `faces.py`, its output
`faces.json` (face pairs and plural fibres for every face above, the right and two-sided
congruences of "contains `th`", its four-cycle census, and the matrix, polynomial, permutation and type counts) and `RUN.md`.
Exact integer work.

# The arithmetic contract: a numeral is a face of a counting navigator, and its producer is a key

> **Retired September 29 as catered machinery** ([antipattern record](2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md)). The build of §8 recognized
> the test's layouts by a hand-written grammar and computed each result by exact routines: a calculator,
> not learning. The code is retired (history at `1b374d46`). The mathematics stays in Lean
> (`Mathematics/ArithmeticContract`, `jet_separates_across_keys`), and the one native finding stays: an
> operator's reading is located by which consequences hold.

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6, restated; the text chart audit's
§4 item 3). **Status.** A derivation stated before any build (§1–§7); the smallest build and its
pinned acceptance run follow in §8, and the acceptance passed. Lean
`HolonicsResearch/Mathematics/ArithmeticContract` proves what is marked formal-checked;
`research/notebook/arithmetic/contract_checks.py` (standard library) checks every finite case
exactly.

**Occasion.** The [audit](2026-09-29_THE_TEXT_CHART_AUDITED_ONE_PREDICTOR_SEEN_CONVERSATIONS_AND_NO_ARITHMETIC.md)
found that the text chart reads digits as opaque bytes (finding 5) and asked for arithmetic
"joined through one shared contract, not a patch for prose". Brandon's lenses, as the audit
records them: arithmetic emerges from counting and calculus and is not a skill to discover;
`2 + 2 = 4` and `2^2 = 4` are different generators with one face, and the generator is causally
relevant; a multiplication table is a map of how digit pairs occur relative to each other in a
base; bases 2, 10 and 16 matter, perhaps odd or prime bases too; integers are carried with their
factorization; no codec is catered to; holonic compression never reconstructs past raw states.

**The contract in five lines.**
1. A numeral is the radix receiver's face `⟨ρ_(b,g)|n⟩` of a counted Holon: an odometer of radix
   `b`, each digit a phase and each carry a winding, read through a glyph map `g`.
2. Its producer is a navigator with its initial configuration (its key): a counter, or a pair of
   digit words joined at a pair port (pointwise for `+`, by convolution for `·`, repeatedly for
   `^`), followed by one carry cascade.
3. Each place's total is a ratio with remainder, `t_j = b·c_(j+1) + d_j`, and its carry is the
   section flux of that place's wheel.
4. The consumer equation at the result port: `decode_b(T_native(encode_b x)) = T(x)`. The decoder
   (base, glyph map, carry word, producer key) and the result's factorization are returned with the
   digits.
5. Provenance is the key, not the face. A computed result adds nothing to its key's code but the
   holds sheet's share (§4a). A numeral costs the cheapest of its presentations: its digits, its
   factorization, or a count from a landmark.

## 1. The object

[definition; agent-inferred] **Counting first.** Counting is causal incidence (the
[August 12 record](2026-08-12_COUNTING_IS_CAUSAL_INCIDENCE_LANGUAGE_IS_ITS_CODEC_THE_MAP_IS_THE_CONTINUING_BODY.md)).
An integer `n` is the windings of a unit clock over an aeon, and its radix chart is the odometer
of radix `b`: level `j` is a wheel of `b` steps, its phase the digit and its winding the carry into
level `j + 1` (`Geometry/PhaseCarry`, `holonics::geometry::winding::Odometer`). A numeral in any
stream is that receiver's face, read through the chart's glyphs. The numeral face turns with the
base, and the factor body remains (the
[July 17 record](2026-07-17_THE_NUMERAL_FACE_TURNS_THE_FACTOR_BODY_REMAINS.md)).

[definition; agent-inferred] **The producers**, each a navigator with its key:

| Producer | Key | Its law on digit words | Owner |
|---|---|---|---|
| counter | start, ticks | the odometer's step, `+1` with carry | `PhaseCarry.digits_succ`; `receiver::population::arithmetic::Counter` |
| sum `a + c` | the two operands | pointwise sum, then the carry cascade | Lean `consumer_add` |
| product `a · c` | the two operands | convolution (digit `i` meets digit `l` at place `i + l`), then the cascade | `RadixWindowReceiver.digit_product_is_carry_of_convolution`, Lean `consumer_mul`; Rust `digit_product`, `CarryEgg` |
| power `a^e` | base, exponent | repeated convolution, each factor carried | Lean `consumer_pow` |
| factorization | the exponent vector | multiplication adds exponent vectors | `PrimeValuationRadixAtlas`; `ratio::surprisal::factor_biguint` |

**The ports.** Two operand ports carry digit words, which are the keys. The pair port joins them
carry-free: this is the helical pair interaction, one digit pair per placed contact. The carry
port runs the cascade. The result port returns the digit word, its carry word, its factorization
(computed, so it costs work, not bits) and the decoder.

[proved-derived; formal-checked] **The carry is the section flux.** The carry a place passes up is
the signed crossing count of its wheel's section `{x | b ∣ x}`, over any aeon of the wheel's lift
from `0` to the place's total (`carry_is_section_flux`, over `Aeon/Clock/Epoch.signed_count_is_flux`).
This is U5's law for a ring (`HNN/Moment.SelectiveDecl.carryIn_is_section_flux`) read at a digit
place. Each emitted digit is the phase and each carry the winding (`carryWord_cons`). The cascade
keeps the value and emits digits below `b` (`carryWord_value`, `carryWord_lt`).

[proved-derived; formal-checked] **The consumer equation.** For `b ≥ 2`,
`decode_b(carryWord_b(encode_b a ⊕ encode_b c)) = a + c`, and the same holds with `∗` and `a · c`
(`consumer_add`, `consumer_mul`). The repeated product gives `a^e` (`consumer_pow`). The square
closes alike in any two bases (`consumer_rebase`). [established-bounded; computational-witness]
The notebook checks sum, product, power, carry-as-crossing-count and rebase on 192 seeded operand
pairs in bases 2, 10 and 16. It also checks Brandon's `7 · 3`: `[1,1,1] ∗ [1,1] = [1,2,2,1]`,
carries `[0,1,1,1]`, `10101₂ = 21`. And `FF₁₆ · FF₁₆`: `[225,450,225]`, carries `[14,29,15]`,
`FE01₁₆`.

## 2. One contract, many charts

[definition; agent-inferred]

| Exterior (the chart) | Native (the contract) |
|---|---|
| the digit glyphs `0–9`, `a–f`/`A–F` (the same bytes in prose, Rust and Lean) | the odometer of radix `b`: phase, winding, carry |
| the base's declaration: a prefix `0x`, `0b`, or none (ten) | the radix receiver's partition, a restriction in the tower thread |
| digit order (most significant first in all three), separators `_` and `,` | the carry cascade, least significant first |
| operator and relation glyphs `+ * × · ^`, `=`, `==` | the producers, their pair ports and their composition |
| words ("two", "times") | not read (§7) |

- **The base is the receiver's partition, not the number.** Bases `2 → 4 → 16` restrict by grouping.
  A base-16 place is four base-2 places, and `len₁₆(2^k) = ⌊k/4⌋ + 1` (`digits_length_two_pow`).
  Base 10 shares only its trailing face mod 2 with base 2.
- **Nothing is written for one chart.** The contract declares producers and the glyphs they may
  wear. The pairing of a glyph to a producer is a **key**, located per stream by which pairing's
  results hold.
  - The case that forces this: `^` is the power in Lean and in prose, and exclusive or in Rust.
  - Exclusive or is the base-2 sum with its carry released: the circle without the helix
    (`PhaseCarry.carried_circle_is_not_the_split_product`).
  - So `^` is located as the power in one stream and as the carry-free sum in the other, by the
    first expression whose results part them. No chart declaration is needed.
  - [open] The glyph map itself is the Enigma plugboard: it can be located by loop closure over
    records that hold. That law is stated here and not built.

## 3. Provenance: the key, not the value

[proved-derived; formal-checked] `2 + 2 = 2 · 2 = 2^2 = 4` (`one_face_three_producers`). The equality
belongs to the scalar receiver (`Foundation/RelationLadder.theEqualityBelongsToTheScalarReceiver`,
atlas `holon.four-and-two-squared`).

- **When the stream carries the expression.** The producer is its key: the operator and the operands.
  The receipt keeps that key. It is the `KeyToContributionRelation` that
  `receiver::population::provenance` lists as missing today.
  - The result costs `0` bits under every producer (§4).
  - So the two producers of `4` part at exactly the operator cell's code, which the stream pays
    anyway. No extra bits are needed.
- **When only faces arrive.** The producers form a plural fibre. The face `4` alone, over operands in
  `[0, 5)`, has ten producers. [computational-witness]
  - A provenance receiver pays `log₂` of the surviving fibre (the chain rule's
    `log₂|K| − log₂ #S`) until a jet parts them. After that it pays nothing, and each dead producer
    leaves a receipt.
  - Along the right operand's clock the jets are `(a + k, 1, 0)`, `(a k, a, 0)` and
    `(a^k, a^k(a − 1), a^k(a − 1)²)` (`jet_add`, `jet_mul`, `jet_pow`). At `(2, 2)` these read
    `(4, 1, 0)`, `(4, 2, 0)` and `(4, 4, 4)`.
  - For `a ≥ 2` the second-order jet parts every two producers (`jet_separates`). The face with the
    first difference ties only `·` and `^`, and only at `(2, 1)` (`mul_pow_first_jet_tie_iff`): how
    many orders are needed depends on where the receiver is.
  - At `a = 0`, `·` and `^` are one species along that clock (`zero_mul_pow_species`). Only the left
    operand's clock parts them (`left_clock_separates`): sameness belongs to a receiver.
- **The generator is causally relevant** (Brandon, September 11: an additive generator is not
  attainable from exponential data).
  - The sum and the product satisfy the recurrence with the double root `1` and no first-order one
    (`add_free_fall`, `mul_free_fall`, `add_no_single_mode`, `mul_no_single_mode`).
  - The state `(f, Δf)` advances by the shear `[[1,1],[0,1]]`: free fall.
  - The power advances by `f ↦ a f` (`pow_boost`), a dilation with a constant log-ratio `log a`:
    a boost on the count, a free fall on the log helix.
  - So the first nonzero second difference kills the free-fall family. [definition; agent-inferred]
    The minimal recurrence is the producer's family face, and within a family the key (velocity,
    start) parts the producers.

## 4. Code length

**(a) A computed result costs zero given its key.** [proved-derived]
- The result's digits, and the numeral's end after them, are a function of the operand words and
  the producer. So the carry egg's face is one-hot there, and `−log₂ 1 = 0`.
- The egg must read both operands whole before emitting. The trailing face needs only the trailing
  digits (a ring homomorphism), but the leading face carries its fibre from every lower place
  (`RadixWindowReceiver.leading_face_fibre`).
- [established-bounded; measured] This is measured on terrain: `0 + 0/16` bits on the trailing,
  middle and leading product cells in bases 2, 10 and 16 over `2^12` records (notebook README,
  "Eggs composed at ports").
- A stream can state a false result. [definition; agent-inferred] So each expression carries a
  **holds sheet**: a two-key keystone `{holds, free}` with a Krichevsky–Trofimov prior across
  expressions. Under `holds` the face is the computed digit. Under `free` it is the byte tree's
  face. A false result kills `holds` for that expression only.
- [proved-derived; the telescope formal-checked] `N` holding results cost at most
  `2N − log₂ C(2N, N)` bits in all. The sheet's faces multiply to `C(2N, N)/4^N`
  (`holds_sheet_telescope`), and the mixture's face on the computed digit is at least `P(holds)`. That is `1 + 0/16` at `N = 1` and
  `6 + 13/16 + ε` at `N = 4096`. It is the price of learning that results hold, whatever the
  operands' length.

**(b) A number: its factorization against its digits.** [proved-derived; computational-witness]
The declared prefix codes are these:
- Elias `γ` (`2⌊log₂ n⌋ + 1` bits);
- the literal: `|γ(k)|` then `k` digits with a nonzero leading one, `|γ(k)| + log₂((b − 1)b^(k−1))`;
- the factorization: `|γ(s)|`, then each prime by its index gap and its exponent in `γ`;
- counting from a landmark: the landmark's factorization, a sign bit and `|γ(|offset| + 1)|`.

The bit length is shown only for reference; it is not a code.

| `n` | bit length | literal base 2 | base 10 | base 16 | factorization | from a landmark |
|---|---|---|---|---|---|---|
| `13122 = 2·3⁸` | 14 | 20 | `21 + 7/16 + ε` | `20 + 14/16 + ε` | **13** | — |
| `13121`, prime (index 1561) | 14 | 20 | `21 + 7/16 + ε` | `20 + 14/16 + ε` | 23 | **17** (`2·3⁸ − 1`) |
| `729 = 3⁶` | 10 | 16 | `12 + 13/16 + ε` | `14 + 14/16 + ε` | **9** | — |
| `8191`, prime | 13 | 19 | `18 + 2/16 + ε` | `20 + 14/16 + ε` | 23 | **13** (`2¹³ − 1`) |
| `65537`, prime | 17 | 25 | `21 + 7/16 + ε` | `24 + 14/16 + ε` | 27 | **15** (`2¹⁶ + 1`) |

- A small support with large exponents is cheapest as exponents. Every comparison is an exact
  integer ordering (for `13122`, `2¹⁶ < 90000 < 2¹⁷` places its base-10 literal).
- A prime is its own factor, so its factorization is dearest. Near a landmark, counting from the
  landmark wins; elsewhere its digits do.
- The winner depends on where the number sits: a family wins where it is closest.
- In base 3 the numeral is the factorization: `729 = 1000000₃` and `13122 = 200000000₃` (atlas
  `radix.exact-chart`).
- [definition] *Carried with its factorization* is the exactness law of the carrier, not a claim
  about the shortest code. The factorization is computed from the received digits, which costs work
  (`Sieve`, trial division), not bits.

**(c) The multiplication table is the map of digit-pair carries.** [proved-derived; formal-checked]
- A pair `(x, y)` maps to its ratio with remainder, `x y = b⌊xy/b⌋ + (xy mod b)` (`table_div_rem`).
- A row `x` is the rate-`x` clock on the circle of `b` steps:
  - its carries advance by the phase carry `PhaseCarry.carry b (xy) x` (`tableCarry_succ`), the
    carry word of `Aeon/Clock/CarryWord` at rate `x/b`;
  - its digits repeat with period `b/gcd(x, b)` (`tableDigit_periodic`). A unit row permutes the
    digits, and a zero divisor's row closes early.
- A product of words is the sum of placed table entries (pair `(i, l)` at place `i + l`), carried.
  The table is the convolution's one-place kernel, and column sums carry beyond it.

[computational-witness] Trailing-digit counts over the `b²` pairs:

| Base | Counts, digits `0` to `b − 1` |
|---|---|
| 2 | `3, 1` |
| 7 | `13, 6, 6, 6, 6, 6, 6` |
| 10 | `27, 4, 12, 4, 12, 9, 12, 4, 12, 4` |
| 16 | `48, 8, 16, 8, 24, …` |

- In base 2 the table never carries: `x · y` is AND, and every binary carry comes from a column sum,
  as in Brandon's `7 · 3`.
- A prime base's table has no zero divisors: `2b − 1` pairs give `0` and `b − 1` give each other
  digit. So its trailing face loses nothing under a unit.
- An odd base reads parity by the digit sum.

**Bases 2, 10 and 16 as receivers of one navigator.** [proved-derived; formal-checked]
- The digit count of `2^k` is the carry word of a rate-`log_b 2` clock.
- It locks in base `2^j`: `len = ⌊k/j⌋ + 1` (`digits_length_two_pow`).
- It never locks in base 10 (`ten_digit_count_never_locks`, through `2^T ≠ 10^S`,
  `two_pow_ne_ten_pow`): a quasicrystal (`CarryWord.never_locks_iff_irrational`).
- [computational-witness] The convergent denominators `10, 93, 196, 485, 2136, 13301` of `log₁₀ 2`
  hold as near-periods and each fails. `2136` first fails at `k = 13300`.

## 5. Where it composes into the population

[definition; agent-inferred]
- **The numeral port** is a keystone of one key, read from the coded past, as the boundary egg's
  part clock is (`receiver::population::boundary`).
  - At each cell it exposes the expression's phase: outside, operand 1 at place `p`, the operator
    key, operand 2, the relation key, result place `j` of `ℓ`, or after.
  - `ℓ` is fixed by the operands and the producer.
  - It locates nothing, so its chain-rule term is `0` (`Composition.chain_rule`). Its keys are
    cells the byte tree codes anyway.
- **The arithmetic egg reads that port**, as `clock ⊳ carry` does (`Composed::products`).
  - On result phases its face is the holds sheet's mixture: `P(holds)·[x = x̂_t] + P(free)·q_tree(x)`,
    where `x̂_t` is the cascade's digit or the numeral's end.
  - Its code telescopes (`Composition.composed_telescope`). The byte tree reads every other cell.
  - The face has the admitted egg's copy-stage form (`staged_code`), with the located byte `x̂_t`
    supplied by the carry cascade instead of the request. The keystone's value, the byte tree's code
    on the result cells against the egg's, is exact.
- **Retention.** While an expression is open the port holds its operand words and partial carries.
  At its close they are released, because no admitted future reads them. Nothing of the raw stream
  is kept.
- **Other eggs at the same port.** The counter (successive numerals differing by one: enumerations,
  line numbers), progressions (free fall), geometric runs (the dilation) and the landmark family
  (§4b) are mixed by Bayes at the port.
- **Generation is egg packing.** A request holds `(producer, operands, base, chart)` at its port.
  - Each result digit is released by the certified draw at tolerance zero, since the face is
    one-hot and the draw is the commit (`Population.certified_draw_is_released_at_zero_tolerance`).
    Its glyphs are `decode_b ∘ T_native ∘ encode_b` in the request's chart.
  - The receipt carries the key, the carry word and the decoder, and the consumer square is checked
    at release, not only UTF-8 validity (audit finding 6).
  - A factorization request emits the exponent vector in the chart's notation (`2 * 3 ^ 8` in Lean,
    `2·3⁸` in prose).

## 6. The build loop's acceptance, fixed before any build

**Streams.** For each base `b ∈ {2, 10, 16}` and each chart, `N = 2^10` expressions are drawn under
a seed named in the pin, with operands never read before. The charts:
- prose: `so 347 × 5102 = 1770394.`;
- Rust: `assert!(0x15B * 0x13EE == 0x1B039A);`;
- Lean: `example : 0x15B * 0x13EE = 0x1B039A := by norm_num`.

The producers are `+`, `·`, `^` (small exponents) and, in Rust, `^` as exclusive or.

- **A1. A result codes at its operands' cost, and the square closes.**
  - On every holding expression the result cells, digits and end together, code within the holds
    sheet: `N` of them in at most `2N − log₂ C(2N, N)` bits in all, checked by exact enclosure.
  - The emitted word decodes to `T(a, c)`, and rebasing to the other two bases gives the same
    value, on every expression.
- **A2. Producers of one face stay distinguishable.**
  - Every expression whose face two admitted producers share (`2 + 2`, `2 · 2`, `2 ^ 2`;
    `10 + 10 = 10 · 10 = 100` in base 2) has a receipt naming the carried producer, with each
    family's contribution.
  - On a faces-only control of seeded sums, products and powers (`a ≥ 2`), the other families die
    by the third face of each run (the second-order jet, `jet_separates`), with death receipts.
    Before the separating face the provenance code is `log₂` of the tied fibre.
- **A3. One contract serves the three streams.**
  - It is one owner with no chart branch, one declared glyph set, and `^` located per stream.
  - It reaches every expression in all three charts, with equal result codes on equal expressions.
  - The keystone's value is reported exactly against the byte tree alone on the same cells.
- **Failure branch.** An expression the port does not reach is counted and named by its glyphs,
  for example Lean's `(2 : ℕ)` or Rust's `2u64`. The port's law is then revised for every chart, or
  the case is recorded as unreached. No chart gets a patch of its own.
- **Projection.** `2^10` expressions and one byte tree a stream: seconds and megabytes, projected
  from the terrain notebook's `2^12` product records, read in 7 seconds a base.

**The smallest build that tests it.**
- `holarchy::terrain::arithmetic::Expressions`: the three chart layouts, each with its exact truth
  (key, word, carry word).
- `receiver::population::arithmetic::{ExpressionPort, ExpressionEgg}`: the port read from the coded
  past, and the egg with the holds sheet. They reuse `digit_product`, `Odometer` and the composition
  law.
- An `hnn_population` mode that runs them.
- This record's Lean.

It touches none of `admitted`, `boundary`, `releasing` or `text_release`, which are the data
protocol's owners. Composing it with the text chart's population follows once that protocol lands.

## 7. What it does not claim

- It does not claim that arithmetic shortens the curated stream: its count of expressions is
  unmeasured, and a stream without expressions gains nothing.
- The provenance theorem covers `+`, `·` and `^` along one operand's clock, not general expression
  families. Subtraction, division, fractions and decimals are not built (the ratio's radix division
  law covers them).

**The lenses it honours and the ones it cannot yet honour.**
- *Arithmetic emerges from counting and calculus* holds in the law, not yet in the machine's
  physics. The eggs are declared counting laws, not learned, which honours *not a skill to
  discover*. But they are not yet the field's rings: an odometer as a chain of ring clocks joined at
  power ports is open (#62, with U1's missing join).
- *`2 + 2` and `2^2` are different generators with one face* is honoured: §3 and A2.
- *The multiplication table as a map of digit pairs* is honoured as a law (§4c). Brandon's mental
  arithmetic, which anchors the two exact faces and solves the middle, is not built as a receiver;
  the egg computes exactly.
- *Bases 2, 10 and 16* are honoured (§2, §4c, A1–A3). For *odd or prime bases*, only the two table
  facts are derived, and no advantage is claimed.
- *Integers carried with their factorization* is honoured at the result port (§1).
- *No codec catered to* is honoured partly. No chart gets a branch, and `^` is located per stream.
  But the digit glyph map is declared, not located, and word numerals and word operators are not
  read.
- *Never reconstruct past raw states* is honoured: the port holds only an open expression's operands
  (§5).

## 8. The build and its acceptance run (September 29)

**Built** (`c17ea7bd`; Refs #73 #148 #63), the smallest build of §6:
- `holarchy::terrain::arithmetic::Expressions`: the three chart layouts in one declared glyph set,
  each line with its exact truth (key, digit word, carry words, `T` and its factorization, the
  result's glyph cells and the numeral's end). `T_native` joins the operands' digit words at the
  pair port and carries them by one cascade (`carry_cascade`, now also `digit_product`'s). The
  carry-free sum is the base-2 sum with its windings released, and the released windings are
  `a ∧ c`.
- `receiver::population::arithmetic::{ExpressionPort, ExpressionEgg}`, with `ExpressionEgg::release`.
- The `arithmetic` mode of `hnn_population` (`research/notebook/hnn_design/hnn_population_arithmetic.rs`).
- Lean `jet_separates_across_keys`: the second-order jet parts two producers whatever keys
  `a, a' ≥ 2` they hold. It is the law of the faces-only control, whose families hold free keys.

**Decisions** [agent-inferred], each with its reason (they are stated in the owners too):
- *The numeral's end is a stage.* Under `holds` the face on the cell after the result is the stage
  `{continues, ends}` with the end certain, and the glyph that ends it is the byte tree's (its face
  within the ending glyphs). The terminator is `.`, `)` or ` ` by chart, so it is not a function of
  the key.
- *The result's start is a stage too.* That a numeral begins after `= ` or `== ` is chart syntax, the
  byte tree's `T(S)`. Within it, the first glyph is the sheet's.
- So every cell's face factors as a chart part (the byte tree's) times a sheet part (the result's).
  A1 is measured on the sheet parts, and the chart parts are reported beside them.
- *The result wears its left operand's base.*
- *The `^` pairing is inside the egg.* Its keys share the port and the byte tree, so it is not a
  `Composed` of copies: a common factor cancels from the posterior.
  - A key dies at a close where another living key's consequence held and its own did not, or was
    not computed. That is the record's "located by which pairing's results hold". A false result
    kills no key.
  - Before a death, the keys' weights move only within the parting expression, so the exact
    posterior stays small. The pairing costs at most `log₂ 2 = 1` bit a stream.
- *Exponents below 64*: a power of two with such an exponent fits the machine word. A power past
  them is not computed.
- *The byte tree at depth 16*: sixteen bytes span the longest run between an operand and the
  result's first glyph (`B * 0x13EE == 0x`).
- *The failure branch, revised during development, before the pin.* On the development seed's
  declared forms the port read `so 1,000 + 1 = 1,001.` as `000 + 1 = 1`, which held. The port's
  law was revised for every chart: a numeral does not begin after a digit and a separator `,`, just
  as it does not begin after an identifier glyph. The form is now unreached and named.

**The pin** (`54925b4c`, committed before its draws were read):
- Seed `2026092903`, one seeded draw for the whole run: bases 2, 10 and 16 in that order, `N = 2^10`
  expressions a base serving its three charts, operands below `2^13`, exponents below 4; then the
  faces-only control; then the release keys.
- The development runs read seed `2026092913`, and the tests read their own seeds.
- The projection: 240 s and 1 GiB for the whole run. The development run took 105877 ms and
  623000 kB on one core, against the caps of ten minutes and 20 GB.

**The run**: `cargo run --release -p holonics --example hnn_population -- arithmetic` took
105886 ms against 240 s projected. Its peak resident set was 614312 kB against 1 GiB. Every code
below is read at `L_R = 16` as `n + k/16 + ε`, `0 ≤ ε < 1/16`; the endpoints are exact in the
output.

| Stream | Cells | Reached | A1: located key's sheet on the result cells (bound `5 + 13/16`) | Egg's sheet, the pairing mixed in (bound `6 + 13/16`) | Square / rebase | `^` located | Shared faces | Result's first glyph: tree → egg | Result's other glyphs: tree → egg | Numeral's end: tree → egg | All cells: tree → egg | Keystone's value |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| prose 2 | 57493 | 1024/1024 | 5 + 10/16 | 6 + 9/16 | 1024 / 1024 | power | 81 | 29 + 1/16 → 26 + 11/16 | 19686 + 3/16 → 5 + 0/16 | 4522 + 11/16 → 1469 + 8/16 | 56710 + 11/16 → 33973 + 15/16 | 22736 + 11/16 |
| Rust 2 | 66042 | 1024/1024 | 5 + 13/16 | 6 + 13/16 | 1024 / 1024 | carry-free sum | 15 | 26 + 14/16 → 23 + 10/16 | 17964 + 2/16 → 6 + 2/16 | 4707 + 5/16 → 1667 + 1/16 | 59579 + 9/16 → 38578 + 2/16 | 21001 + 6/16 |
| Lean 2 | 78649 | 1024/1024 | 5 + 10/16 | 6 + 9/16 | 1024 / 1024 | power | 81 | 21 + 6/16 → 19 + 1/16 | 19680 + 1/16 → 4 + 15/16 | 3077 + 8/16 → 22 + 4/16 | 57147 + 15/16 → 34415 + 3/16 | 22732 + 11/16 |
| prose 10 | 24542 | 1024/1024 | 5 + 10/16 | 6 + 10/16 | 1024 / 1024 | power | 91 | 2871 + 10/16 → 29 + 13/16 | 19527 + 10/16 → 0 + 10/16 | 2674 + 8/16 → 1443 + 15/16 | 56239 + 6/16 → 32639 + 15/16 | 23599 + 6/16 |
| Rust 10 | 31695 | 1024/1024 | 5 + 13/16 | 6 + 13/16 | 1024 / 1024 | carry-free sum | 18 | 3137 + 5/16 → 38 + 11/16 | 16631 + 0/16 → 0 + 12/16 | 2986 + 13/16 → 1750 + 2/16 | 58839 + 12/16 → 37874 + 4/16 | 20965 + 8/16 |
| Lean 10 | 45693 | 1024/1024 | 5 + 10/16 | 6 + 10/16 | 1024 / 1024 | power | 91 | 2872 + 5/16 → 30 + 9/16 | 19542 + 6/16 → 0 + 11/16 | 1282 + 7/16 → 55 + 1/16 | 56741 + 4/16 → 33130 + 7/16 | 23610 + 12/16 |
| prose 16 | 28987 | 1024/1024 | 5 + 11/16 | 6 + 11/16 | 1024 / 1024 | power | 88 | 34 + 7/16 → 27 + 13/16 | 21431 + 7/16 → 5 + 10/16 | 2797 + 5/16 → 1544 + 0/16 | 56071 + 14/16 → 33386 + 1/16 | 22685 + 12/16 |
| Rust 16 | 36209 | 1024/1024 | 5 + 13/16 | 6 + 13/16 | 1024 / 1024 | carry-free sum | 24 | 44 + 0/16 → 35 + 7/16 | 18940 + 10/16 → 5 + 1/16 | 3152 + 3/16 → 1833 + 8/16 | 58693 + 1/16 → 38430 + 3/16 | 20262 + 13/16 |
| Lean 16 | 50186 | 1024/1024 | 5 + 11/16 | 6 + 11/16 | 1024 / 1024 | power | 88 | 28 + 4/16 → 21 + 15/16 | 21455 + 14/16 → 5 + 10/16 | 1381 + 14/16 → 131 + 3/16 | 56598 + 14/16 → 33891 + 11/16 | 22707 + 3/16 |

- **A1 passed on all nine streams.**
  - Under the located key, `A + B ≥ P(holds)` held as an exact rational inequality on each of the
    1024 expressions of every stream. Every prior was `(2i + 1)/(2i + 2)`, and the priors' product
    equals `C(2N, N)/4^N` exactly. So the result cells, digits and end together, cost at most
    `2N − log₂ C(2N, N) = 5 + 13/16 + ε` bits a stream, and the enclosures put the measured code
    below that bound on every stream.
  - The egg's own sheet parts, with the pairing mixed in, lie within the bound plus one bit. The
    product of the per-expression bounds is `C(2N, N)/4^N · 2^−1` exactly: one parting expression a
    stream.
  - The square `decode_b(T_native(encode_b x)) = T(x)`, read back from the numeral's glyphs, held on
    all 9216 expressions, and so did its rebase through the other two bases.
- **A2 passed.**
  - *Shared faces on the streams.* Every expression whose face two admitted producers share has a
    receipt naming its carried producer (the operator glyph's key), with the holds and free
    contributions: 81, 15, 81, 91, 18, 91, 88, 24 and 88 expressions.
    - In prose and Lean the share is `a ^ 1 = a · 1`.
    - In Rust it is a sum or carry-free sum whose operands share no bit, where `a + c = a ⊕ c`.
  - *The record's own cases* (`2 + 2`, `2 · 2`, `2 ^ 2`; `0b10 + 0b10 = 0b100` in base 2), written in
    each chart through a fresh egg:
    - each receipt's fibre is {sum, product, power}, and the carried producer is named;
    - the priors run `1/2`, `3/4`, `5/6`;
    - the `^` line kills the pairing key it contradicts, and Rust's `2 ^ 2 == 0` leaves the fibre
      {carry-free sum}.
  - *The faces-only control*: 64 runs a producer of 4 faces, `a ∈ [2, 16)`, `k ∈ [0, 8)`, each
    family holding all 112 keys.
    - On every one of the 192 runs, every other family died by the third face. The carried family
      never died.
    - Before the separating face the provenance code was `log₂` of the tied fibre: `log₂ 3`, `1`
      or `0` at the first face, `1` at the second on 4 runs, and `0` from the third face on.
    - Each death carries its receipt: the face that killed it and the keys it held. For example, a
      product run `(8, 1)` with faces `8, 16, 24` killed the power's last key at the third face, 24.
- **A3 passed.**
  - One owner reads the three charts: the port has no chart branch, and `^` was located per stream,
    as the power in prose and Lean and as the carry-free sum in Rust.
  - Every stream reached 1024 of its 1024 expressions.
  - On equal expressions across the charts (sums and products in all three, powers in prose and
    Lean), the contract's code `−log₂ Σ_held W·P(holds)` was equal exactly: 1716, 1676 and 1687
    chart pairs in bases 2, 10 and 16, with none unequal.
  - The measured codes differ only by the free key's share, the byte tree's belief, by less than
    `1/16` bit.
  - The keystone's value, the byte tree alone against the egg on the same cells, is the table's last
    column: between `20262 + 13/16` and `23610 + 12/16` bits a stream. On the chart's other cells the
    egg's face equalled the byte tree's exactly, cell by cell.
- **The failure branch.**
  - No pinned expression was unreached.
  - The declared forms outside the layouts, each read through a fresh egg, are recorded unreached:
    Lean's `(2 : ℕ) + 2 = 4`, Rust's `2u64 + 2 == 4`, `1_000 + 1 = 1001`, `1,000 + 1 = 1,001`,
    `0o17 + 1 = 0o20`, `5 - 3 = 2`, `two + two = four` and `2 + 2 + 2 = 6`.
  - `2 ^ 70 = 1180591620717411303424` is keyed, but its power lies past the admitted exponents, so no
    key reaches it.
  - `2 + 2 = 5` is a false result: it held under no key, and the sheet's free key coded it.

**What the run shows beyond the acceptance** [measured]:
- On the result's glyphs after the first, in prose, the byte tree alone pays `19686 + 3/16 + ε` bits
  on 19600 binary glyphs, `19527 + 10/16 + ε` on 5078 decimal glyphs and `21431 + 7/16 + ε` on 6111
  hex glyphs. The egg pays under 7 bits on them in every stream.
- On the numeral's end the egg pays `1469 + 8/16 + ε` bits over 1024 ends in prose base 2, and
  `22 + 4/16 + ε` in Lean base 2. That cost is the chart part, the byte tree's: after a long numeral
  its 16-byte context cannot tell an operand's end (a space) from a result's end (`.` or `)`). Lean
  ends both with a space. The port's phase would part them as the tree's context, but that is not
  built.

**The output product** (synthetic; each request is read at the port of the egg that read its stream,
and its result is released by certified draws at tolerance zero, each cell `[0, 1)`; the control is
the byte tree alone, drawing from its face under the same keys):

| Request | Egg's release | Receipt | Byte tree alone |
|---|---|---|---|
| `so 347 × 5102 = ` (base 10, prose) | `1770394` | product; `1770394 = 2·347·2551`; carry word `[1, 0, 1, 4, 2, 1, 0]`; base 10, no declaration | `5241 ` |
| `assert!(0x15B ^ 0x13EE == ` (base 16, Rust) | `0x12B5` | carry-free sum (the located `^`); `4789`, prime; released windings `[0,1,0,1,0,0,1,0,1,0,0,0,0]` (`330 = 0x15B ∧ 0x13EE`); base 16, `0x` | `0x1FD22FA2 ` |
| `example : 0x15B ^ 0x3 = ` (base 16, Lean) | `0x27D8AA3` | power (the located `^`); `41781923 = 347³`; three carry words `[0,0,0]`, `[7,7,3,0,0]`, `[6,6,6,11,5,1,0]`; base 16, `0x` | `0x52A7 ` |
| `so 0b101011011 × 0b1001111101110 = ` (base 2, prose) | `0b110110000001110011010` | product; `2·347·2551`; carry word `[0,0,1,1,1,2,3,3,3,4,4,4,4,4,3,3,2,1,1,0,0]`; base 2, `0b` | `0b100001110110110101101 ` |
| `so 2 ^ 2 = ` (base 10, prose) | `4` | power; `4 = 2²`; carry words `[0]`, `[0]` | `120 ` |
| the power `2, 2` in Rust | refused: Rust wears no glyph for the power | | |

Each release checked its square and its rebase: all true.

**Verdict.** The acceptance of §6 passed on the pinned run: A1, A2 and A3 on all nine streams, no
pinned expression unreached, and the run within its projection. Two costs are disclosed rather than
claimed away:
- the pairing's one bit a stream;
- the byte tree's cost on the numeral's end in prose and Rust.

Composing this egg with the text chart's population, now that item (1)'s protocol is built, is the
next loop.

## Receipts

- Lean `HolonicsResearch/Mathematics/ArithmeticContract`: 27 audited statements with their
  lemmas (`jet_separates_across_keys` added with the build), no `sorry`, standard axioms only.
  `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,244 jobs, success.
- `python3 research/notebook/arithmetic/contract_checks.py`: every check true.
- The build: `cargo check --workspace --all-targets`; `cargo test -p holonics --lib`, 912 passed
  (the terrain's `the_carry_cascade_keeps_the_value_and_emits_digits`,
  `every_producer_closes_the_consumer_square_and_rebases`,
  `the_three_charts_write_the_records_lines`, and the egg's six tests).
- The run: `hnn_population -- arithmetic` at the pin `54925b4c`.
- Atlas: `radix.carry-cascade-consumer`, `radix.carry-section-flux`, `radix.multiplication-table`,
  `radix.power-digit-lock`, `arith.producer-jets`, `arith.presentation-codes`,
  `code.holds-sheet`, `holarchy.terrain-expressions`, `receiver.population-expression-egg`.

## Owed (#62)

- The odometer as a chain of ring clocks at power ports, whose section fluxes are the carries (joins
  U1's missing join).
- The glyph map located by loop closure: over sum records that hold, the only digit permutation
  preserving the carry law is the identity, for `b ≥ 2`.
- The provenance separation beyond `{+, ·, ^}`: the minimal recurrence as the family face of a finite
  expression family, with the jet order that parts it.
- The holds sheet's composed code as an equality, not only the bound: the composition's telescope
  with the `free` key's likelihood included.
- The pairing located by its results (§8): a keystone whose key dies at a close where another key's
  consequence held and its own did not, rather than at a zero face. Its code is at most
  `log₂ |K|` plus the located key's code; the statement is owed, beside `Composition.chain_rule`.

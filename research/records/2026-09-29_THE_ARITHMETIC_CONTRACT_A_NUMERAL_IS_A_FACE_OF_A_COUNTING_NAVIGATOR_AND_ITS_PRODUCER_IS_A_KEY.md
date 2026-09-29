# The arithmetic contract: a numeral is a face of a counting navigator, and its producer is a key

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6, restated; the text chart audit's
§4 item 3). **Status.** A derivation for Brandon's review, stated before any build. No library Rust
changed. Lean `HolonicsResearch/Mathematics/ArithmeticContract` proves what is marked
formal-checked; `research/notebook/arithmetic/contract_checks.py` (standard library) checks every
finite case exactly.

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

## Receipts

- Lean `HolonicsResearch/Mathematics/ArithmeticContract`: 26 audited statements with their
  lemmas, no `sorry`, standard axioms only. `bash tools/lean_check.sh Holonics HolonicsResearch`:
  10,244 jobs, success.
- `python3 research/notebook/arithmetic/contract_checks.py`: every check true.
- Atlas: `radix.carry-cascade-consumer`, `radix.carry-section-flux`, `radix.multiplication-table`,
  `radix.power-digit-lock`, `arith.producer-jets`, `arith.presentation-codes`,
  `code.holds-sheet`.

## Owed (#62)

- The odometer as a chain of ring clocks at power ports, whose section fluxes are the carries (joins
  U1's missing join).
- The glyph map located by loop closure: over sum records that hold, the only digit permutation
  preserving the carry law is the identity, for `b ≥ 2`.
- The provenance separation beyond `{+, ·, ^}`: the minimal recurrence as the family face of a finite
  expression family, with the jet order that parts it.
- The holds sheet's composed code as an equality, not only the bound: the composition's telescope
  with the `free` key's likelihood included.

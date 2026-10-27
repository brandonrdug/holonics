# The operation is a line in the lift, and the release reads the radix itinerary

October 26. Refs #404, #405, #406. The navigator is retired
([the generator is the modulator](2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md)
§8, PR #523): its fold was column addition modulo 9999 written by hand, and the next loop is
named there in four parts, (a) the operator's coefficient line located jointly with the turns,
(b) the capture as a located handoff to a held ring, (c) the combination through the pair contact
`W(x̄⊗y)`, and (d) the release by size through the phase `frac(10^j S/q)`. This record states the
mathematics of (a), (b) and (d) and proves it in Lean, before any build; the build and its
acceptance stay with that record. Grades: [standard] for textbook mathematics with its source,
[derived] for what follows from the objects, [measured] for a read from a run, with its source,
[computational-witness] for an exact finite check, [agent-inferred] for each choice. Lean:
[`Mathematics/ClosureLine`](../../lean/HolonicsResearch/Mathematics/ClosureLine.lean),
[`Foundation/SeparationDepth`](../../lean/HolonicsResearch/Foundation/SeparationDepth.lean) and
[`Mathematics/RadixItinerary`](../../lean/HolonicsResearch/Mathematics/RadixItinerary.lean).

Computational object: the helical pair interaction. The closure line is a pair contact's
coefficient read on three ring phases; the capture boundary is the quotient a contact's future
readings induce on the tube of histories; the release is one helix turned once per written digit,
its carry the digit. Of the winding guide's six objects this touches the helix (the turn by the
base), the pair (the contact reading three faces), faces and placement (residues and their digit
sectors), the tube (histories as clocked words) and the tower thread (the boundary the next level
reads); the cell holonomy stays attached.

## 1. What the seam must not repeat

[agent-inferred] The retired fold failed in one way that a located key does not cure: the keys
were located, but the operation they keyed was the task's own solution routine. So each part
below has to satisfy three conditions, checked in §6:

- no operation is written: `+`, `−`, `×` and `÷` appear only as kernels the rows close, never as a
  step the machine performs;
- no operator byte is named: a byte has a hand only if its rows close a line;
- no result is computed: the release reads a residue the machine holds, in the base the passage's
  own turn locates, and computes nothing from the operands.

## 2. The rows

[agent-inferred] A row is three faces and the bytes between them. The rotor's located turns give
each digit byte its phase on every ring (`hnn.tower-rotor`). A run of bytes along which that turn
holds leaves a residue on the joined ring `q`; three consecutive runs with one byte between the
first two and one between the second and third give the row `(a, ∘, b, =, c)`, with `a, b, c ∈ ℤ/q`.
The separating bytes enter as operands of the same contact, through their own located faces
`e(∘)` and `e(=)`, and never as indices into a table: the coefficient of a row is the contraction
`p = W(·, e(∘), e(=))` of one tensor `W`, so a byte whose faces contract `W` to zero has no hand. This
is the one-face law's single pair contact (`face.conserved-is-congruence`) reading three faces
instead of two.

## 3. The transformation is a line in the homogeneous lift

[proved-standard; formal-checked] Lift each row to `(1, a) ⊗ (1, b) ⊗ (1, c)`, the coordinates
`[1, a, b, c, ab, ac, bc, abc]`. A coefficient vector `p` closes on a row when its pairing with the
lift is zero (`ClosureLine.pairing`, `pairing_eq_dot`). Then:

- closure is linear in `p` (`pairing_add`, `pairing_smul`), so the vectors closing on a family of
  rows form a submodule: the operation the rows carry is the kernel of the rows, located by which
  closures hold, as the arithmetic contract's one surviving finding said
  ([record](2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md));
- every closure is bi-Möbius, `N(a, b) + D(a, b) c` with `N` and `D` affine in each argument
  (`pairing_eq`). Where `D(a, b)` is a unit exactly one `c` closes, `c = −N/D`
  (`closes_unique_of_unit`); where `D(a, b) = 0`, every `c` closes when `N = 0` (a plural fibre) and
  none when `N ≠ 0` (a refusal) (`closes_of_denom_zero`). This is the ratio's inversion with its
  nonunit fibre, read on three faces;
- the four operations are four lines of the one lift (`sum_closes`, `difference_closes`,
  `product_closes`, `quotient_closes`):

  | operation | line | closes on |
  |---|---|---|
  | sum | `(0, 1, 1, −1, 0, 0, 0, 0)` | `c = a + b` |
  | difference | `(0, 1, −1, −1, 0, 0, 0, 0)` | `c = a − b` |
  | product | `(0, 0, 0, −1, 1, 0, 0, 0)` | `c = ab` |
  | quotient | `(0, 1, 0, 0, 0, 0, −1, 0)` | `a = bc` (denominator `−b`) |

- seven rows locate the line (`sum_line_located`, `product_line_located`): on any commutative ring
  in which `2` is a unit, a vector closing on the sum's rows at `a, b ∈ {0, 1, −1}` is a multiple of
  the sum's line, and one closing on the product's rows there is a multiple of the product's line.
  `q = 9999 = 3²·11·101` is odd, so `2` is a unit on it and on each of its rings;
- ring two needs a deeper lift (`ring_two_not_located`): over `ℤ/2`, where `a² = a`,
  `(0, 1, 0, 0, 1, 1, 0, 0)` closes on every row of the sum without being a multiple of its line. A
  ring with a factor two (ring 10, ring 2) reads the sum only through a lift of higher degree.

[computational-witness] Over `ℤ/9999` each of the four lines closes on every row with operands in
`[−20, 20]` (`[−9, 9]` for the quotient's `b` and `c`); `(0, 1, 0, 0, 1, 1, 0, 0)` closes the sum on
all four rows over `ℤ/2`.

[agent-inferred] **The search is the Bombe's.** Seven rows of one separator pair give a
hypothesis (the kernel of a rank-seven `7 × 8` system over `ℤ/q`, solved ring by ring and joined by
the Chinese remainder theorem); every other row of that pair tests it by closing or not; a pair
whose rows have only the zero kernel is refused, with no hand. The turns and the lines are located
together: the residues `a, b, c` depend linearly on the turns `θ` (a digit run's residue is
`Σ_j θ_j[byte] b^j`) and the pairing depends linearly on `p`, so for fixed turns the line is a
kernel and for a fixed line the turns satisfy the closures as polynomial equations, which is the
joint closure of §8(a). A located line is kept when the code its closing rows save on the result's
digits exceeds its own charge (its eight coefficients on `q` and its separator faces), the founding
rule of `contact.tension-founds-face`.

## 4. The capture boundary is read by depth

[derived] The capture of §8(b) hands an operand's residue to a held ring and releases it later.
What it must hold is fixed by retention: the future-sufficient quotient of the passage
(`compression.future-agreement-greatest-stable`), two pasts being one class exactly when no
admitted history, read by any receiver, separates them. That relation quantifies over every
history; it is read by depth instead (`SeparationDepth.agreeUpTo`): two states agree to depth `d`
when no history of at most `d` moves separates them, and their separation depth is the length of
their shortest separating history.

[proved-standard; formal-checked] Depth agreement is an equivalence that coarsens as the depth
falls (`agreeUpTo_equivalence`, `agreeUpTo_mono`); its transitivity is the ultrametric inequality
for `δ = 2^(−depth)`. The future agreement is every depth at once
(`futureAgreement_iff_forall_agreeUpTo`). A move spends depth: states agreeing to depth `d + k`
agree to depth `d` after any word of `k` moves (`agreeUpTo_transport`), so a word of `k` moves
multiplies `δ` by at most `2ᵏ`. If one more letter separates nothing that `d` letters do not, depth
`d` is already the whole future agreement (`futureAgreement_of_stable`). On a finite state space
each new depth either adds a class or ends the search, so two states agree on every history
exactly when they agree on every history of at most `|states|` moves
(`stable_or_classCount`, `futureAgreement_iff_agreeUpTo_card`; Moore's bound).

[agent-inferred] For a calculation this locates the capture's lifetime without a window, and says
what a release owes. Two pasts that differ only in the first operand's residue are separated at
least until `c` is written, at depth the length of `∘ b = c`. Releasing the residue after `c` is
lawful only where the declared admitted future is shown stable: `futureAgreement_of_stable` needs
depth-`d` agreement to imply depth-`(d + 1)` agreement for every pair of states, over every
admitted receiver and word. A quiet continuation is not that. One pair whose next letter separates
nothing can still be separated later, and an admitted future that can ask about the first operand
again without restating it (a reference back such as "half as many" or "the rest", which text
admits by the referent law) separates the two pasts after `c`. Where the declared future is shown
stable at `c`, the residue dissolves into the kernel there; where it is not, the operand's
distinction is kept past `c`, carried rather than released. The stopping rule is global, the class
count over all pairs (`stable_or_classCount`), never one pair's quiet letter; the bound `|states|`
guarantees that the refinement ends.

## 5. The release reads the radix itinerary

[proved-standard; formal-checked] On the ring `q = bʷ − 1` the `w`-digit move is a translation
(`radix.grain-staircase`), so a residue `S < q` is the whole zero-padded `w`-digit block of its
value. The release reads that block by turning it:

- one turn reads one digit (`RadixItinerary.turn_reads_digit`): a residue `D = t b^(w−1) + r < q`
  turns to `b D = t q + (r b + t)`, so the quotient `⌊b D / q⌋` is the leading digit `t` and the
  remainder is the block rotated left by one place;
- `k` turns rotate the block by `k` places (`block_rotates`), the itinerary advances by one turn
  (`point_succ`: `D_(k+1) = b D_k mod q` for `D_k = bᵏ S mod q`, the phase `frac(bᵏ S/q)`), and every
  point is back after `w` turns (`point_period`);
- the turn has order exactly `w` (`turn_order`: `bᵏ mod q ≠ 1` for `0 < k < w`), but a single point
  can return sooner: on `9999`, `1111` is back after one turn and `1212` after two
  (`early_return_1111`, `early_return_1212`);
- the quotient of the turn at `D_k` is the block's digit `k` from the top (`digit_of_point`);
- a value of `L` digits reads `w − L` zeros and then its nonzero leading digit
  (`digit_zero_above_length`, `digit_nonzero_at_length`), and the block is all zeros exactly when
  the value is `0` (`digits_zero_iff`);
- `S` and `S + q` have the same itinerary (`point_fibre`), so the residue never separates a value
  from one a whole ring larger.

[computational-witness] On `q = 9999`, `b = 10`, `w = 4`: `S = 42` turns through the points
`42, 420, 4200, 2004` and back to `42`, emitting `0, 0, 4, 2`; `1234` emits `1, 2, 3, 4`; `9998`
emits `9, 9, 9, 8`; `10041 = 42 + 9999` emits what `42` emits. For every `S < 9999` the four
emitted quotients are its zero-padded digits, and for every `0 < S < 9999` the first nonzero one
is at place `4 − L`. `1111` turns to itself at once and emits `1` at each of the four turns of the
clock.

[derived] So §8(d)'s "which face to read at each place it writes" has one answer: the same phase,
turned once more by the base. The release runs on the lifted clock
`(D, k) ↦ (b D mod q, k + 1 mod w)`: it reads the quotient at each of the `w` turns, writes them from
the first nonzero one on, writes `0` when none is nonzero, and ends when `k` returns to `0`. The end
is the turn's own order `w`, a cycle read by completeness; it is not the point's return, which comes
early on a block of shorter period (ending there would write `1` for `1111`). The digit is the carry of the turn, the winding of the helix (circle plus
carry); the base `b` is the rotor's located turn, and the digit's sector is the tenth of the circle
the phase falls in, as §8(d) said. The read is on the joined ring, never on one ring alone: the
quotient `⌊b D / q⌋` depends on the whole residue. On `9999 = 9 · 11 · 101` the joined phase is a
monomial of the three rings' phases, `S/9999 ≡ 7S/9 + 8S/11 + 50S/101 (mod 1)`
(`joined_phase_9999`), so `e^(2πi S/9999) = ψ₉(S)⁷ ψ₁₁(S)⁸ ψ₁₀₁(S)⁵⁰`, a product the pair contact
takes exactly.

[measured, the generator record's §8] The capture run's release wrote none of 139 four-digit
results with the residue handed in exactly. A four-digit result other than `9999` itself is below
`q`, so its residue is its whole block: the information was present, and the failure was the readout choosing a face per place. The
itinerary replaces that choice by one turn per written digit. Results of five or more digits (64
in that read) lie at or past `q`; their residue is only a fibre, and their release needs the
archimedean face (the length and leading digits the passage locates), which this record does not
supply.

## 6. What stays open, and the recorded failures each part could repeat

[agent-inferred] Open, each named by what is missing:

- the joint search's cost: turns and lines located together, measured on the held-out problems
  before the build is fixed;
- the separator faces' dimension, and whether one `W` reads every block of §2;
- the release past `q`: the archimedean face that locates a result's length when the residue
  cannot;
- the readout that follows the itinerary inside the tower, and its acceptance, which is §8's:
  never-met calculations right at the equals above the 8-gram's 34 of 876, by the paired line, with
  right writes by result length beside it.

[agent-inferred] The recorded failures
([lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
[prototypes](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md),
[recurrences](2026-10-09_LESSONS_THE_FAILURES_THAT_RECURRED_FROM_SEPTEMBER_30_TO_OCTOBER_9.md)):

- **An authored routine standing in for learning.** The lift is not an operation: it holds every
  bi-Möbius relation, and which one a separator carries is located by closure (§3). The release
  computes nothing from the operands; it turns a held residue by the located base (§5). The fold's
  failure, located keys keying a written operation, does not recur, because no operation is
  written.
- **A key/value store passed as a Holonics key.** The separator's faces are operands of one
  contact `W`, not keys into a table of lines (§2); the capture holds a residue only while a future
  separates it (§4).
- **Text run on its codec's grain.** The lift reads any three ring faces, whatever modality
  produced them (a run of digits, of pixel intensities, of acoustic amplitudes, of joint angles);
  the itinerary is a ring's own turn.
- **A design thought in the programming language.** Rows, kernels, turns and residues, not arrays
  or windows; the capture's lifetime is a separation depth, not a buffer length.
- **Bits read as progress.** Nothing here is measured as progress; §5's witness is the decoder's
  exact form, not a tower's output.

# Antipattern: catered machinery. A task's solution routine never stands in for learning

**Date.** September 29. **Issues.** #73, #148, #63. **Grade.** [project-postulate] for the rule,
[source-inspected] for the instances.

**Occasion.** U6 item 3's arithmetic build released every result exactly: `so 347 × 5102 = `
released `1770394`, with its producer and carries. Brandon asked how, and the source answered:
- a hand-written state machine over a fixed glyph set (decimal, `0b`, `0x`; `+ * × · ^`; `=`,
  `==`) recognized exactly the layouts the test terrain generated;
- the result was computed by the exact arithmetic routines (carry cascade, digit convolution,
  powers) from the parsed operands, and its "release" drew from a one-hot face, so it could only
  emit the computed digits;
- nothing learned arithmetic. Only the reading of `^` (power or exclusive or) was located from data.

Brandon: "I would recommend killing the calculator implementation … that's how you cause confusion
and allow for contaminated and wrongly fitted implementations; rote computation is not a machine
learning solution, we have intense research on Holonics regarding tokenizers and encoding text and
recursively 'thinking' … I would archive whatever might've been positive from that and document
this as an antipattern, I don't want this kind of contaminated machinery to appear again."

## The rule

The machine is never handed a task's solution routine as a family, stage, port, receiver or
predictor. No calculator, hand-written grammar or parser, copier, sentence counter, sieve,
depth-limited context window, or classical compressor tuned to a codec stands in for learning.
Producers, structure and keys are located by the machine's own encoding, dynamics and deposition
from its passage. Tokenizing, encoding and recursive refinement ("thinking") are the field's own.
- **What remains lawful.** A terrain may generate its truth with exact routines: that is data
  with its answer key, never a receiver. The machine's own laws are exact (ratios, the carries of its
  clocks, the energy balance). A declared family may be a candidate navigator of the machine's own
  kind (a rotor ring, a grating, a contact lock) whose keys are located.
- **What is excluded.** A receiver that computes a task's answer by an authored routine, or
  recognizes a task's inputs by a grammar fitted to the test's layouts.
- **The sign.** A result that is perfect because it was authored is a failed build, not a
  success: it measures the author, not the machine.

## The instances found

1. **The arithmetic calculator** (U6 item 3, `c17ea7bd`): `receiver::population::arithmetic::
   {ExpressionPort, ExpressionEgg}`, the `Expressions` terrain and its harness. Retired.
2. **The arithmetic eggs** (`receiver::population::arithmetic`: `RecordClock`, `CarryEgg`,
   `Counter`, `Sieve`, and `Composed::products` over the `Products` and `PrimeWindow` terrains).
   They are the same form: a family that computes a product, a count or a sieve by an authored
   routine and codes its result at zero bits. Retired, and the composition, evolution and release
   laws they served as fixtures for are tested on families of the machine's own kind.
3. **The byte-tree text line** (F0, F4, U2, U6 items 1 and 2): a depth-limited context window,
   the admitted egg's copy stage (longest match into the request), the boundary egg's sentence
   counter, and the byte-by-byte text release. Stopped September 29
   ([record](2026-09-29_THE_TEXT_CHART_IS_THE_ONE_MACHINES_FIELD_TORI_HELICES_EGGS_AND_TUBES_ARE_ONE_FAMILY.md)).
   Its catered layers are retired once `hnn::encoding` and `hnn::prediction` land, since those
   loops are running on the same passage and must not lose their data plumbing mid-run.

## What is archived

Git history is the archive: the calculator at `1b374d46`, the arithmetic eggs before their
retirement commit. What was positive stays as mathematics, in Lean, where no receiver consumes
it as a routine:
- `HolonicsResearch/Mathematics/ArithmeticContract`: counting as a navigator's windings, the carry
  as section flux, the holds sheet's telescope, the producer jets;
- `jet_separates_across_keys`: two producers of one face part by the second-order jet;
- the finding that an operator's reading is located by **which consequences hold**: the one
  native piece of the build, the loop-closure form the encoding must realize in general.

## The guard

`CLAUDE.md` and `AGENTS.md` state the rule among the governing laws ("No catered machinery"), and
`docs/THE_MACHINE.md` lists it among the guards that make the rejected forms impossible.

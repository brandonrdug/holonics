# The review finds the codec cuts the numeral, the credit stops at the section, and the equals has one step

October 27. Refs #404, #406, #405. At Brandon's request, a review of the arithmetic line after
seven rotor towers. They changed what the level's pair contact holds and all landed in one band at
the equals, with one shape of error. This record names the four limits every one of them shared,
none of which a contact can repair, orders the fixes, gives each its pass condition, and fixes the
first fix's run before it runs. Grades: [measured] for reads with their receipts, [derived] for what
follows from the objects, [agent-inferred] for each choice.

Computational object: the helical pair interaction. The review touches the pair (a unit is a
founded pair of adjacent units, and the codec's chart decides which pairs may be proposed), faces
and placement (a numeral is read with the place each digit stands at, and the release writes its
first unit at the equals) and the tube (the section is the span the covector crosses). The helix,
cell holonomy and the tower thread stay as the strand towers have them.

## 1. What seven towers measured, and why the variants stop

[measured] Right at the equals, of 2,448 held-out calculations and of the 876 never met in
training (receipts: [the opened run](2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES_receipts/OPENED_RUN.md)
and the strands record's [STRANDS_RUN.md](2026-10-26_THE_OPERANDS_ARE_HELD_BY_LOCATED_STRANDS_AND_THE_RESULT_IS_READ_ON_THE_RING_THAT_CLOSES_receipts/STRANDS_RUN.md)):

| tower | law | all | never met |
|---|---|---|---|
| `PRT` | turned rotor | 240 | 24 |
| `PRS` | free rotor | 288 | 19 |
| `PRK` | located strands | 230 | 16 |
| `PRI` | strands, identity keys | 214 | 22 |
| `PRA` | located strands, contacts opened | 286 | 18 |
| `PRJ` | located strands, joined at zero | 233 | 19 |
| `PRE` | identity keys, contacts opened | 245 | 26 |
| 8-gram | | 1,559 | 34 |

Every tower's wrong values have one shape: about half fall within a factor of two of the result
(49 to 55%), 97 to 100% are values heard after some `=` in training, the leading digit is right no
more often than its foil (`PRA` 12% against 14%), the last digit is right well above its foil (39%
against 29%), and the share right falls with the result's length (`PRA`: 25%, 10%, 7%, 2% and 0 of
64 for one to five or more digits).

[agent-inferred] The variants changed what the contact holds. The limits below lie before the
contact (the units the passage is read in), around it (the span its covector reaches) and after it
(the steps the release has at the equals), and are the same for all seven. No further contact or
key variant is built against this read until they are repaired.

## 2. The four limits

**2.1 The codec cuts the numeral by frequency.** [measured] The committed units
(`d0973c39…782a`) are 1,062 merges founded by the order-one code-length price over the raw bytes
(1,318 units with the bytes). Nothing in the founding knows a digit or a mark: 113 merges hold a
digit, 69 hold two or more, and several join a mark to the digit beside it (`=3`, `2=`, `0>>`). A
numeral is cut where its pairs were frequent, not by place, and some units are pieces of results
heard often.

**2.2 The read asks for a continuation the founded passage never holds.** [measured] The read stops
the prompt right after a calculation's `=`. Where training's own parse joins that `=` to the
result's first digit, the founded passage never has a unit boundary there, and the tower is asked a
question it never met. Split by whether training's parse has a boundary right after the `=`: 422 of
the 2,448 calculations have none, and every tower writes 0 of them right (the leading digit right in
9 to 17). On the other 2,026: `PRA` 279, `PRE` 241, `PRT` 233, `PRK` 229. (The split was measured
on the PC by string matching, with a script outside the repository, so its counts differ slightly
from the rules'; the founding's `UNITS_EQUALS` line below measures the same cut in the example.)

**2.3 The credit stops at the section.** [measured; derived] Training reads eight streams in sections
of 128 units, and a section's covector is cut at its edge. The training text's 3,528,168 bytes read
as 1,342,760 units, 2.63 bytes a unit, so a section spans about 336 bytes, while a problem averages
524.6 bytes (6,726 problems); sections are cut wherever the stream reaches 128 units, not at
problems. Under a joined rotor the passage credit that would carry the covector across the edge is
refused as owed (`hnn::tower`: "a passage credit under a rotor: its moments through the step are
owed"), and on the byte tower it measured worse in bits
([record](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY.md)).
A result's covector reaches the question that set it up only where both fall in one section.

**2.4 The equals has one step.** [derived; measured] Each unit the release writes has one step
through two levels. The result's leading digit is written first and depends on the whole carry
chain; its last digit depends only on the operands' last digits (the residue mod 10 is local). The
reads match: the leading digit is at its foil, the last digit above it. The opened comparison's
share of the contacts' bilinear weight fell from 250 thousandths a ring at founding to 0 after
training on every ring (`TOWER_PAIR_COMPARISON`): under this codec, in one step, the next unit's
loss at the equals had no use for it.

[definition; agent-inferred] **The codec's chart** (built with this record; `hnn::units`, "The
codec's chart"). A founding may declare a chart of its byte classes:

```text
kinds      each byte class has a kind; (a, b) is proposed only when both are of one kind, so no
           founded unit crosses a class of another kind
counted    the counted classes (value order) never merge: a run of them is a word on its base's
           tower, each class read with its place, the power of the base it stands at
marks      the point ends the whole places (after it −1, −2, …); a group mark followed by exactly
           its width of counted classes continues a run no longer than it
classes    a counted class at place 0 is its byte's own class; every other founded place adds one
           class a value, decoding to the same byte, so decode(parse(x)) = x
founded    the places are those the passage holds; a place past them reads as the outermost
           founded place, which `Units::outside` counts
```

The text codec declares letters, the space, `'` and bytes from `0x80` as one kind, the line feed
as another, and every other byte as a kind alone; the ten digits are counted, `.` is the point and
`,` a group of three. So `12,400.50` reads as `1@4 , 2@3 4@2 0@1 0 . 5@−1 0@−2`, `=` and `>>` are
always units of their own, and every cut at an `=` falls where every reading of the passage has a
boundary. The place is counted from the numeral's own end, so the first unit written after an `=`
carries the result's leading digit and its length together (the joint `RINGS` reads as
`lead_length`). The equations at the consumer are the units tests: the place of every counted byte
on a text with groups, points and a trailing group mark; no founded unit crossing a kind; `=` a
boundary on both sides; `decode(parse(x)) = x`; the chart's text form restoring exactly; a forged
merge across a kind refused.

## 3. What is naive, and what is not

[agent-inferred] The tower has no attention, by law: the HNN keeps no key/value store, and a
selective recurrence holds the passage in its modes (two levels of 64 complex modes). That is not
the naive part; the strands located 15,480 of 15,613 result digits from the state the tower
already carries, so the operands are in the state. Three things are naive:
- the codec was founded with no chart, so a mark and a digit could fuse and a numeral had no
  places;
- the credit horizon is a batch length chosen for the hardware, not the passage's own span;
- the clock is one step a unit, so the release has no more time at the equals than at a space.

Attention would repair none of the three: a transformer reading these units would face the same
missing boundary and the same leading-digit-first order. Writing a sum's digits lowest place first
is known to help small transformers learn addition (Lee et al., "Teaching Arithmetic to Small
Transformers", 2023) [external, cited], which is the same carry order 2.4 names.

## 4. The fixes, in order, each with its pass condition

[agent-inferred] The order is the order of dependence: while the codec zeroes 17% of the read, no
credit or time change can be read on those calculations; while the credit stops inside the
problem, the time at the equals has no covector from the question to learn from.

**Fix 1: the codec's chart** (built). Two towers are founded on units founded with the chart:
`UA`, founded as `PRA` (located strands, contacts opened), and `US`, founded as `PRS` (the free
rotor). The acceptance: `UA` writes never-met calculations right at the equals for more than the
8-gram's 34 of 876. Decisions fixed before the run:
- 1a. If `UA` passes, the codec was the binding limit, and the next loop is the products (the
  index chart) and results past four digits.
- 1b. If `UA` fails and the comparison's share at its final state stays above one thousandth on
  every ring (`TOWER_PAIR_COMPARISON`), the codec gave the contact a target it keeps, and fix 2 is
  next.
- 1c. If the share still falls to 0, fix 3 comes before fix 2: the contact has a target and no
  time to use it.

Beside the acceptance: `UNITS_EQUALS cut` (0 is expected); right at the equals overall, met and
never met, and `lead_length`, against `PRA` and `PRS`; the held-out bits a byte (comparable across
codecs, since they are per byte). Fewer met calculations right than `PRA` is expected and is not
the measure: the digit foil `F`, whose digits were single units with no places, wrote 131 met
calculations to the committed units' 176 and 25 never-met to 14 (within the paired line,
[record](2026-10-26_THE_DIGIT_PIECES_ARE_NOT_THE_CAUSE_THE_PLAIN_TOWER_WRITES_BACK_176_OF_1572_HEARD_CALCULATIONS_SO_THE_EQUALS_IS_READ_WHERE_IT_WAS_HEARD.md)).

**Fix 2: the section is the problem.** A training section begins where a problem begins and spans
the problem, so a result's covector reaches its question exactly. This replaces a cut chosen by the
batch with the passage's own partition; it raises no limit. The passage credit stays unused: it
measured worse in bits, and under the rotor its moments are owed. Before launch, the reverse scan's
memory is projected from the longest problem's units and measured on a development pass. Pass:
never-met right above fix 1's count by the paired line (`b − c > 1.96·√(b + c)`) and above 34.

**Fix 3: time at the equals.** The release gets the steps the carry chain needs. Its form is fixed
from fixes 1 and 2's reads, before it is built: if the leading digit stays at its foil while the
last digit is above, the order is the limit, and a numeral is presented lowest place first at the
codec (the chart's places already name each digit's power, so the order is a presentation, decoded
back); otherwise the release takes silent steps at the equals before it writes. Pass: the leading
digit right above its foil on never-met calculations, and never-met right above 34.

## 5. Strategy beyond the equals

[agent-inferred] The four limits are not arithmetic's. A codec founded across marks, a credit cut
by the batch and one step a unit bind every line the tower reads: John's answer names a referent
set up in the question, usually more than one section back (2.3); a Holonics paragraph's
constraint on its language crosses the same edges; an acoustic or motor codec declares its own
counted classes and marks, or none. The chart lives in the boundary codec, the section in the
passage's own partition, and the time in the release's clock, so each fix is general and each is
measured here first because the equals gives an exact read.

What the variants showed stays: the located strands hold the operands, and the opened contact
conducts their comparison at founding. They need a coherent target and room to use it before
another variant of the contact can be read.

## 6. The recorded failures this review could repeat

- **Text run on its codec's grain as the exception.** The chart is declared by the boundary codec;
  `hnn::units` names no modality and founds any passage of byte classes, with or without a chart.
- **An authored routine standing in for learning.** The chart computes no value, sum, carry or
  comparison. It reads a numeral as a word on its base's tower, the structure the
  [association record](2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER.md)
  names, and keeps marks from fusing with what they mark.
- **A refusal answered with a larger limit.** Fix 2 changes the partition to the passage's own and
  projects its memory before launch; no deadline, budget or section length is raised past a
  measurement.
- **A located cause carried unrepaired into a new consumer.** The zeroed 17% was in every read since
  the units were founded; every count above carries it, and fix 1's reads are compared with that
  stated.
- **Bits read as progress.** The held-out bits are reported beside the read and decide nothing.
- **Seen material graded as unseen.** Met and never-met calculations are read apart.

## 7. Fix 1's run, fixed before it runs

On Brandon's PC, from the commit that carries this record: the units founded with the chart on the
training text (`found-units`, its old founding took 2.99 s; deadline 60 s), printing
`UNITS_FOUNDED` with the founded places and `UNITS_EQUALS`; `UA` and `US` founded on them as `PRA`
and `PRS` were, with only the units changed; development passes together, the projection as the
opened run made it with the section count scaled by the development passes' own count, then three
training passes together under fixed deadlines and guards; the written reads, the rules (`rings`,
`heard`, `pair` against `PRA`, `PRS` and each other, `gaps`) and the pair modes at founding and at
the final state. Every output stays on the PC; the receipt is copied here with the release text,
marks and unit pieces left out.

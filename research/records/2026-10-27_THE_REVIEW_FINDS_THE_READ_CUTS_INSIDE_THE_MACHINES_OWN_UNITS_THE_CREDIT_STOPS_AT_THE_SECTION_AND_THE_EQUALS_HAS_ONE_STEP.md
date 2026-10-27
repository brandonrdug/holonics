# The review finds the read cuts inside the machine's own units, the credit stops at the section, and the equals has one step

October 27. Refs #404, #406, #405. At Brandon's request, a review of the arithmetic line after
seven rotor towers. They changed what the level's pair contact holds and all landed in one band at
the equals, with one shape of error. This record names the three limits every one of them shared,
none of which a contact can repair, orders the fixes, gives each its pass condition, and fixes the
first fix's run before it runs. It keeps apart what the review must not mix: the units are the
machine's own learned reading of the text, on an axis of their own, and the read at the equals is a
check from outside. Grades: [measured] for reads with their receipts, [derived] for what follows
from the objects, [agent-inferred] for each choice.

Computational object: the helical pair interaction. The review touches faces and placement (where
the check cuts a prompt against where the machine's units end, and the release writing its first
unit at the equals) and the tube (the section is the span the covector crosses). The pair (a unit
is a founded pair of adjacent units), the helix, cell holonomy and the tower thread stay as the
strand towers have them.

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
contact (where the check cuts the passage the tower reads), around it (the span its covector
reaches) and after it (the steps the release has at the equals), and are the same for all seven.
No further contact or key variant is built against this read until they are repaired.

## 2. What the units are, and the three limits

**The units are the machine's own reading.** [measured] The committed units (`d0973c39…782a`) are
1,062 merges founded by the order-one code-length price over the raw bytes (1,318 units with the
bytes). Nothing in the founding knows a digit or a mark: 113 merges hold a digit, 69 hold two or
more, and several join a mark to the digit beside it (`=3`, `2=`, `0>>`). [agent-inferred] That is
the founding doing its work, not a defect: a pair joins where joining it codes the passage shorter,
and `=3` is joined because results open with 3 often enough to pay for the unit. The founding is a
learning of its own, recursive along its own axis (a founded unit is proposed again as half of a
later pair), and it is judged on that axis (§5), never by the arithmetic check.
[the digit pieces' record](2026-10-26_THE_DIGIT_PIECES_ARE_NOT_THE_CAUSE_THE_PLAIN_TOWER_WRITES_BACK_176_OF_1572_HEARD_CALCULATIONS_SO_THE_EQUALS_IS_READ_WHERE_IT_WAS_HEARD.md)
already found the digit pieces are not what keeps the never-met calculations low: the foil `F`,
whose digits were single units, wrote 25 never-met calculations to the committed units' 14 and 131
met ones to 176.

**2.1 The read cuts inside a unit.** [measured] The read stops the prompt right after a
calculation's `=`, a cut at a byte. Where the problem's own reading in the units joins that `=` to
the result's first digit, the passage the tower was trained on never has a unit boundary there, and
the tower is asked to continue from a unit (`=` alone) it never met before a result, while the unit
it did meet there (`=3`) is cut away by the prompt. Split by whether training's parse has a boundary
right after the `=`: 422 of the 2,448 calculations have none, and every tower writes 0 of them
right (the leading digit right in 9 to 17). On the other 2,026: `PRA` 279, `PRE` 241, `PRT` 233,
`PRK` 229. (The split was measured on the PC by string matching, with a script outside the
repository, so its counts differ slightly from the rules'; `CUTS.tsv` below makes the same split in
the example and the rules.) [agent-inferred] This is the check's limit, not the tower's or the
units': the question was asked in bytes of a machine that reads in units.

**2.2 The credit stops at the section.** [measured; derived] Training reads eight streams in sections
of 128 units, and a section's covector is cut at its edge. The training text's 3,528,168 bytes read
as 1,342,760 units, 2.63 bytes a unit, so a section spans about 336 bytes, while a problem averages
524.6 bytes (6,726 problems); sections are cut wherever the stream reaches 128 units, not at
problems. Under a joined rotor the passage credit that would carry the covector across the edge is
refused as owed (`hnn::tower`: "a passage credit under a rotor: its moments through the step are
owed"), and on the byte tower it measured worse in bits
([record](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY.md)).
A result's covector reaches the question that set it up only where both fall in one section.

**2.3 The equals has one step.** [derived; measured] Each unit the release writes has one step
through two levels. The result's leading digit is written first and depends on the whole carry
chain; its last digit depends only on the operands' last digits (the residue mod 10 is local). The
reads match: the leading digit is at its foil, the last digit above it. The opened comparison's
share of the contacts' bilinear weight fell from 250 thousandths a ring at founding to 0 after
training on every ring (`TOWER_PAIR_COMPARISON`): in one step, the next unit's loss at the equals
had no use for it.

[definition; agent-inferred] **The read meets the units** (`tower_train::written_release`, built
with this record). The check cuts at a byte; the machine reads in its units. Healed, a
calculation's prompt is read in the units without its last unit, and the release opens with that
unit's bytes: while they are unspent, the draw is the tower's face restricted to the units whose
bytes agree with them (a unit that is a prefix of the unspent bytes, or one running past them, as
`=3` runs past `=`), the tower's own conditional on the bytes it was shown; past them the release
draws from the whole face, and what follows the withheld bytes is graded. A tail for which no
agreeing unit holds mass at the face's grain is placed as the units parse it, and counted. The
units stay as founded. This is the reader's form of a known repair for prompts cut at a byte and
read by a learned tokenizer ("token healing") [external, known practice].

```text
p = u_1 … u_n            the prompt read in the units;  t = bytes(u_n), the withheld tail
the fork receives        u_1 … u_(n−1)
while |r| < |t|:         s = t[|r|..];  draw u ∝ m_u · [s starts with bytes(u), or bytes(u) starts with s]
then                     draw u ∝ m_u until `>>` or a line end past t, or MARK_CAP units (the tail's among them)
graded                   r[|t|..]
```

The equations at the consumer: with no tail the release is the unhealed one bit for bit (the free
release runs unhealed, so a healed read's `FREE.tsv` equals the unhealed read's), and the graded
mark is exactly the bytes after the prompt's own. `CUTS.tsv` records, for each calculation, whether
the whole problem read in the units ends a unit at its `=`, and the rules' `cuts` mode reads any
release apart on the two sides of that split.

## 3. What is naive, and what is not

[agent-inferred] The tower has no attention, by law: the HNN keeps no key/value store, and a
selective recurrence holds the passage in its modes (two levels of 64 complex modes). That is not
the naive part; the strands located 15,480 of 15,613 result digits from the state the tower
already carries, so the operands are in the state. The units are not the naive part either: they
are the machine's own encoding. Three things are naive:
- the check cut each prompt at a byte, not where the machine's reading has a boundary, so 17% of
  the read asked a question the tower never met;
- the credit horizon is a batch length chosen for the hardware, not the passage's own span;
- the clock is one step a unit, so the release has no more time at the equals than at a space.

Attention would repair none of the three: a transformer reading these units would be cut inside
them by the same check, and would face the same leading-digit-first order. Writing a sum's digits
lowest place first is known to help small transformers learn addition (Lee et al., "Teaching
Arithmetic to Small Transformers", 2023) [external, cited], which is the same carry order 2.3
names.

## 4. The fixes, in order, each with its pass condition

[agent-inferred] The order is the order of dependence: while the check zeroes 17% of the read, no
credit or time change can be read on those calculations; while the credit stops inside the
problem, the time at the equals has no covector from the question to learn from.

**Fix 1: the read meets the units** (built). Every tower is read again from its final state with
the healed read, on the units it was founded on; nothing is founded or trained. The acceptance is
the arithmetic line's: a tower writes never-met calculations right at the equals for more than the
8-gram's 34 of 876. Decisions fixed before the run:
- 1a. A healed read whose `FREE.tsv` differs from its unhealed read's is a defect in the healing;
  the run stops there.
- 1b. If a tower passes, the cut was the binding limit, and the next loop is the products and
  results past four digits.
- 1c. Otherwise, on the calculations whose `=` the units do not end at (`CUTS.tsv` 0), each
  tower's share right is read against its share on the others. If in every tower it stays below
  half, the zero was not only the cut, and that is the next loop's subject; otherwise fix 2 is next.

Beside the acceptance: right at the equals overall, met and never met, `lead_length`, and each
healed read paired calculation by calculation with its unhealed read. The healed counts replace the
unhealed ones in every later comparison.

**Fix 2: the section is the problem.** A training section begins where a problem begins and spans
the problem, so a result's covector reaches its question exactly. This replaces a cut chosen by the
batch with the passage's own partition; it raises no limit. The passage credit stays unused: it
measured worse in bits, and under the rotor its moments are owed. Before launch, the reverse scan's
memory is projected from the longest problem's units and measured on a development pass. Pass:
never-met right above fix 1's count by the paired line (`b − c > 1.96·√(b + c)`) and above 34.

**Fix 3: time at the equals.** The release gets the steps the carry chain needs. Its form is fixed
from fixes 1 and 2's reads, before it is built: the release takes more steps of its own clock
before it writes, never steps triggered by a named mark: a step keyed to the `=` byte would be a
routine authored for the task (the `=` is where the read checks, never a law of the learning); nor
does any rule reorder the numeral's digits for the tower, since the order a numeral is read in
belongs to the passage and its units. Pass: the leading digit right above its foil on never-met
calculations, and never-met right above 34.

## 5. Strategy beyond the equals

[agent-inferred] The three limits are not arithmetic's. A check cut inside the machine's units, a
credit cut by the batch and one step a unit bind every line the tower reads: John's answer names a
referent set up in the question, usually more than one section back (2.2); a Holonics paragraph's
constraint on its language crosses the same edges; an acoustic or motor codec's units are cut by a
check at a sample or a frame the same way. The healing lives in the reader, the section in the
passage's own partition, and the time in the release's clock, so each fix is general and each is
measured here first because the equals gives an exact read.

**The units' own axis.** The units are founded by their own learning, recursive along their own
axis, and judged on their own measure: the held-out code a byte they give the tower that reads them.
One fact about that axis is stated because the review met it: the founding's price is an order-one
receiver of its own, not the tower that reads the units (`hnn.founded-units`), so the units the
tower reads are not re-founded by its own reading. That question belongs to the units' axis and is
read on its measure; nothing on the arithmetic line steers the founding, so that the check's cut
falls on a boundary or for any other reason of the check's.

What the variants showed stays: the located strands hold the operands, and the opened contact
conducts their comparison at founding. They need a coherent target and room to use it before
another variant of the contact can be read.

## 6. The recorded failures this review could repeat

- **An authored routine standing in for learning.** The first version of this record built a chart
  into the units' founding: the text's byte classes sorted into kinds no unit could cross, digits
  that never merged and were read with their place, `=` always a unit alone. It was a hand-written
  tokenizer, chosen so that the check's cut would fall on a boundary, and it put the check's
  convenience into the machine's learning. It was retired the same day, before any run, and the
  repair moved to the check's side. The units stay founded by their own price.
- **Text run on its codec's grain as the exception.** The healing names no byte: it withholds the
  last unit of any prompt in any codec's units, and knows no digit, mark or text.
- **A refusal answered with a larger limit.** Fix 2 changes the partition to the passage's own and
  projects its memory before launch; no deadline, budget or section length is raised past a
  measurement.
- **A located cause carried unrepaired into a new consumer.** The zeroed 17% was in every read since
  the units were founded; every tower is re-read healed, and no unhealed count is carried into a
  later comparison.
- **Every key located is not nothing authored.** The rotor towers are founded from a menu of
  stretches of three numerals with single bytes between them, a shape chosen because calculations
  have it; the closing byte (`=`) and its keys are located from the text, but the stretch is
  authored. It computes no value, and it stands as a stated qualification on every rotor tower's
  read until the menu is located from unnamed bytes.
- **Bits read as progress.** The held-out bits are reported beside the read and decide nothing.
- **Seen material graded as unseen.** Met and never-met calculations are read apart.

## 7. Fix 1's run, fixed before it runs

On Brandon's PC, from the commit that carries this record: every tower already read at the equals
(`C`, `F` and the rotor record's `PP` and `PR`, the turns', strands' and opened runs' seven above) is
read again from its final state with `read-unit-tower-written` at the arguments of its earlier read
(the written keys, 400 bytes, 1, 64 and 8) and the units it was founded on; each read is checked
against decision 1a; then the rules (`rings`, `heard` and `gaps` over the healed reads, `cuts` over
the healed and the unhealed reads, and `pair` of each healed read with its unhealed one). No tower
is founded or trained. Every output stays on the PC; the receipt is copied here with the release
text, marks and unit pieces left out.

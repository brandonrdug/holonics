# The binding bank at the first level recalls the held-out bindings, and at the top level it recalls nothing

**Withdrawn, October 26.** The binding bank this record builds or measures is a key/query/value
store: a fixed grid of slots written by the delta rule, opened as an induction copier and first
accepted on a lookup benchmark (MQAR). An audit made at Brandon's request found it, and commit
`0934a25ff` retired it ([the
retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements below stand only as measurements of that machinery, never as progress of the
learner, and nothing here is a design to resume.

October 26. Refs #404, #405, #386. The build of spec 1 of
[the binding bank record](2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md)
and its first readings against that record's fixed acceptance (§3). Receipts:
[`…_receipts/`](2026-10-26_THE_BINDING_BANK_AT_THE_FIRST_LEVEL_RECALLS_THE_HELD_OUT_BINDINGS_AND_AT_THE_TOP_LEVEL_IT_RECALLS_NOTHING_receipts/RUN.md).

## 1. What was built

The bank is `hnn::tower::bank` (`BankDeclaration`, `BankState`), joined to a tower by
`Tower::join_bank`. Its law is the record's §2.2 unchanged. Its material joins the certified
deposit's families, the tower and learner text carry it, and its state at rest is not carried. Its
reverse scan is the record's §2.5 inside a section. The exterior commands are in
`examples/solenoidal_alpha/complete_language/tower_bank.rs`: found a tower on a class alphabet,
join a bank onto any learner, and train and read a learner on a class passage cut into sections,
each from rest and compared only where a mark file says. `tools/listener/mqar.py` writes the
record's MQAR terrain from its own generator.

Computational object: the helical pair interaction, with the strand clocked by content. The bank
touches two of the winding guide's six objects: the helix (its key turns are half-turn phases on a
box of harmonics) and faces and placement (a binding sits at a grid address and is read through the
kernel `K_M`). The pair contacts, cell holonomy, tube and tower thread stay as the tower has them.

## 2. Acceptance, item by item

| §3 item | reading | state |
|---|---|---|
| 1. Opening | with `O = 0` the banked tower codes every passage and reads every face bit-identically to its bankless twin (`a_banked_tower_opens_on_its_bankless_twin`) | passes |
| 2. Covector | the code's difference agrees with the covector for all ten families (`the_banked_covector_matches_the_code_difference`) | passes |
| 3. Card form | the bank runs on the host only (`C = 1`) | owed |
| 4. Recall | 15,999 of the 16,000 held-out answers named, 0.001 bits an answer; the bankless foil names 243 at 6.031 bits | passes (bar 95%) |
| 5. Prose | not yet read | owed |
| 6. The subject | not yet read | owed |

## 3. The recall reading

One pass over 4,096 training passages, 16 passages a certified deposit, each passage read from rest
and compared at its 16 answer cells (`LEVEL0_4K.txt`, `FOIL_4K.txt`, `TOP_4K.txt`):

| learner | held-out named | held-out bits an answer | training bits an answer, the pass |
|---|---|---|---|
| bank at level 0 | 15,999 / 16,000 | 0.001 | 0.419 |
| bank at the top level, the same opening | 234 / 16,000 | 6.032 | 6.154 |
| bankless foil | 243 / 16,000 | 6.031 | 6.059 |

Chance among the 64 values is 6 bits and 250 named. The level-0 bank's training windows (each read
before its deposit, so on passages it had not met) fall 2.865, 0.396, 0.064, 0.013, 0.008, 0.003,
0.002, 0.001 bits an answer over the first 256 deposits of the stopped 16,384-passage run
(`LEVEL0_16K_STOPPED.txt`). After them, every answer is read from its key's binding inside its own
passage. Key 0 alone is bound to 63 different
values across the held-out set, so this is recall of the passage, never a constitution naming
answers.

## 4. Two openings the readings moved

**The level.** The record placed the first bank at the top level. There the held-out answers stay at
chance through every deposit, with the key opened on the face block (234 named) as with the key
drawn over both blocks (247 named after 16,384 passages, `TOP_BOTH_BLOCKS_16K_STOPPED.txt`). At the
first level, where the face is the arrival's own encoding `E(u)`, the same bank names all but one.
The first declaration (`BankDeclaration::first`) is now the first level. [measured] Why the top level
fails [agent-inferred]: its face is the first level's mixture of the passage, so two arrivals of one
key class open on different key turns, the read recalls nothing, and `O`'s covector has nothing to
correlate with. Whether a bank at a higher level opens once a first-level bank binds is not read.

**The key opens on the face block.** The key and the query open on one founded draw over the face
block `x^ℓ`, the read block `r̂` at zero, so a key names the face that arrived before it and the query
the face arriving now, and the read at an arrival returns what followed that face's last arrival
from the first cell. This is the derivation in the module's notes; the level-0 reading uses it, and
level 0 with the key over both blocks was not read.

**The covector fixture.** With the key on the face block, the check's opening (gate bias 1, hold 4,
join drawn on `2^(−8)`) left the gate bias and the hold at 0.30 and 0.12 of the reading bar
(`FIXTURE_FAILED.txt`): the assertion that every family is read failed, while every family that was
read agreed with its difference. A sweep of the opening (`FIXTURE_SWEEP_*.txt`) chose the join on
`2^(−7)`, the hold at `h = 2` and the gate at `g = ½`, on the record's passage of recurring pairs: every
family reads at 3.18 times the bar or more, and the check passes unchanged.

## 5. Time

Projections, deadlines, measured wall times and peak resident sets are in `RUN.md`. The first
level-0 run was projected at 455 s from a 0.433 s deposit; a window ran 0.60 s a deposit, and it was
stopped on that evidence at 158 s, incomplete. The read was changed, not the bound: the next run
trained on the first 4,096 passages, which the stopped run had already shown suffice, at 0.83 of its
166 s projection.

## 6. The recorded failures these choices could repeat

- **An authored routine standing in for learning.** The bank is a general strand; nothing in it
  names keys, values, marks or the terrain. The marks tell the exterior where to compare and never
  enter the tower. Its recall is located by its own covector and deposition.
- **Seen material graded as unseen.** The held-out passages are 1,000,000–1,000,999, fixed by
  SHA-256 before any run; the generator refuses a training range that overlaps them.
- **Bits read as progress.** The bar is the count of answers named, fixed before the build; bits
  stand beside it.
- **An uncertified deposition step.** Every deposit is the tower's certified section: the section
  reread from its opening codes strictly fewer bits, with halvings counted.
- **Text run on its codec's grain as the exception.** The terrain here is a class alphabet, not
  bytes; the same commands read any class passage, and the prose item reads bytes.
- **A refusal answered with a larger limit.** The stopped run's bound stood; the read changed.

## 7. What is owed

- §3.3, the card form: the bank's chunk form (record §2.6) on the card, against the host at the
  declared `C`.
- §3.5, prose at or below bz2 given the same training text, with `O` zeroed after training raising
  the code.
- §3.6, the subject question about John.
- Lean, carried in #410: `bank_recall_exact` (a read at a grid key returns its value exactly),
  `bank_delta_overwrite` (a second write at one key replaces the first), and `bank_chunk_eq_recurrent`
  (the chunk form's series equals the recurrence's).

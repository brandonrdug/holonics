# The stores and copiers are retired, and the plain tower codes the same bits without them

**Date:** 2026-10-26. Refs #404 #405 #406 #410. Design thread. Status: built and accepted; the
deletion is commit `0934a25ff`, merged beside the pumped towers in the same branch. The receipts
are below.

## Why

At Brandon's request on October 26 the design asked whether database architecture had crept into
the machine. His direction is the law this record enforces: a key/value memory is addressing as
computer science does it, not learning; the machine addresses by geometry (its own phases,
windings and locks) and evolves by its own dynamics. CLAUDE.md's "No catered machinery" already
forbade it (no copier, no index of contexts, no store standing in for learning), and the lessons
record names the copier as the failure that repeated most. It repeated again.

The audit found four pieces of machinery of one species, each a store or a copier beside the
tower's own state:

| owner | what it was |
|---|---|
| `hnn::tower::bank` with `tower_bank.rs`, `tools/listener/bank_trace.py`, `tools/listener/mqar.py` | a fixed grid of 64 slots written by the delta rule, opened as a hand-wired induction copier and first accepted on a lookup benchmark (MQAR): a key/query/value memory |
| `hnn::tower::clock` | a reset clock that held the unit arriving after a chosen class and raised that unit's logit at the readout: a copy pointer |
| `hnn::passage` | the passage tree: decayed counts per exact context, and a node lock returning the class that followed the deepest match's last visit: an index of contexts and a longest-match copier |
| `unit_copy.rs`, `modes_train.rs`, `read-lines-located` | the letters copy (the node lock run forward beside the tower), the keyed-modes trainer and sampler that joined the passage tree's news and lock at the face, and the reads whose moments the tree's lookups placed |

How it crept in, from the records: the October 23 copy pieces (the copier, under "news"); the
October 25 bar against bz2, which a copier lowers; the October 26 bank specification, which
imported the key/query/value framing with a lookup benchmark as its acceptance; then the role key,
the clock and the referent key (the last withdrawn in PR #499 before it was built). The word
"key" carried it. CLAUDE.md's key is a navigator's initial configuration, located by loop
closure; it was cited for a database key, and the atlas filed the bank's rows under the object
"key".

## The acceptance, fixed before the deletion

1. The plain gated unit tower trains and reads to identical bits, state and written release
   before and after, on the same inputs.
2. The tower, keyed-modes and units tests pass.
3. `bash tools/gate.sh` passes.
4. No retired name remains in `crates/`, `tools/` or `docs/atlas/`.

All four hold. The receipts, from the worker's run in the container (base `36b17ebd8`, after
`0934a25ff`):

- Train and read logs are equal line for line once `elapsed_ms` and `pass_ms` are masked:
  `TOWER_PASS pass=0 train_bits_a_byte=3.701 dev_bits_a_byte=3.465 dev_regions Q=2.280 P=3.566
  N=3.099 M=3.467 deposits=29/29 train_code=150339651308 dev_code=33627456105 grain_bits=20`.
  The rested state's SHA-256 is
  `37901d6487aa5d7f557895e7f644983253a383a636f4f4759504e89b84121775` both times; the written
  release's FREE.tsv is `a28581c5832818e888b21f18c61269463cb93d382bed8af708d583e1e572002c` and
  MARKS.tsv `9a93a9b4aadd6d20d1c00b030015d5b301f0fa6d98147db0e594aea273350dcf` both times.
- `hnn::tower` 54 passed, `hnn::keyed_modes` 9, `hnn::units` 3; the Python suites under `tools/`
  pass on the changed tree.
- The gate: all 22 stages ok.
- The retired-name search over `crates tools docs/atlas` returns nothing, and no atlas owner
  points at a deleted declaration.

| run | deadline | measured |
|---|---|---|
| base release build | 1,200 s | 317 s |
| after release build | 600 s | 284 s |
| train / read | 60 s each | 4.57 s / 1.61 s |
| test build | 1,500 s | 152 s |
| tests (tower / keyed modes / units) | 900 s each | 17.7 s / 0.1 s / 0.2 s |
| gate | 1,100 s | 508 s |

Peak resident set was not measured (no `/usr/bin/time` in the container); no run neared a limit
and none was repeated.

## What changed beside the deletion

- 19 files, 6,157 lines removed, 142 added.
- `train-unit-tower` (and its pumped siblings) lose the `HOLD` argument; `read-tower-held` and
  `read-tower-held-cells` lose `unjoined`.
- `log2_face` moves to `hnn::keyed_modes` beside `ln2_face`, the inverse face of the exponential
  navigator.
- The keyed learner's save format is `keyed-modes-learner-v4`, with no older decoder: an old save
  is a superseded prototype.
- `TowerLearner::moments()` had no caller left and is deleted in the merge.
- The atlas loses the ten rows of the retired owners. `contact.pool-founding` stays: its law, the
  reduced-rank founding of a face from a pool's drop, does not depend on the clock, which was only
  its first instance; its owner is now the clock's file at `36b17ebd8`.

## What stays, and why

- The tower, the duplex and the keyed modes are learned state, not stores. The tower draws its
  exponential faces and dyadic turns from `hnn::keyed_modes`. Its `KeyedModes` and `KeyedLearner`
  keep only their tests as consumers; their law, each arriving class selecting every mode's move,
  is the pumped tower's move, so they are deleted when the pumped tower's run is read and that law
  is stated at the tower.
- Three owners are of the same species at the boundary (agent-inferred): the founded units
  (`hnn::units`, a code-length pre-pass that cuts text into pieces), the ring faces' pair-move
  tables found by a driver's search, and the receiving tree's contexts
  (`compression::landmark::context`). They stay for now because the current loop compares the
  pumped towers with the plain tower on the same units, so the grain must not move under the
  comparison; each is retired when the machine's own founding replaces it, and the
  [generator-is-the-modulator record](2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING.md)
  names what replaces addressing by table: a numeral addressed by its own digits on coprime rings.

## The records

The 21 records that build or measure the retired machinery carry a withdrawal note under their
title, and the October 24 record's section "The lock where a located key fires" carries one above
it. Their measurements stand as measurements of that machinery, never as progress of the learner,
and none is a design to resume. `CONSTRUCTION_STATE.md` states the retirement; its October 23
paragraphs stay as history.

## The rule this leaves

A design with keys, queries and values, slots, per-entity indexing, a copy opening at the output,
or a lookup benchmark as its acceptance is refused before it is built. Recall is the tower's own
state: a phase or winding address, a parametron's lock, a deflection of a later passage. When a
brief says "key", it means a navigator's configuration located by loop closure, and the brief says
so.

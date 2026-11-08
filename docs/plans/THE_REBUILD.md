# The rebuild

**Status: November 7.** This plan is the construction's one order: the steps with their issues and
done conditions, the campaign under way, and the rules every step keeps. The laws live in their
guides and owners ([the elementary objects](../ELEMENTARY_OBJECTS.md), [THE_MACHINE](../THE_MACHINE.md)),
[CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md) is the position, and dated records hold the
derivations and the measurements.

The plan was rewritten on November 7 as the current order, at Brandon's word that the construction
documents are the agents' to redo. What it replaced is history:
- the plan of September 28 to November 7 (the unified plan U0 to U8, the issue order of October 9,
  the October text-chart lanes, the gates F0 to F6 word for word, the protocol and the Decisions
  index) is at [`0a051ae5`](https://github.com/brandonrdug/holonics/blob/0a051ae5/docs/plans/THE_REBUILD.md);
- the [construction record](../../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md)
  keeps what that plan replaced: steps 0 to 8, the step-4 design and its five campaigns, and the
  forward plan F0 to F6 as it stood on September 27.

## 1. The line

The construction serves one line ([THE_MACHINE](../THE_MACHINE.md#the-line-the-rebuild-serves)):
compression is intelligence is navigation. Holonic Compression couples a fractal navigator's
resonating modes with terrain, landmark discovery locates the faces where navigator paths converge,
and the HNN executes both at scale.
- Every campaign names the navigators, terrain, kernel, cokernel and landmarks it touches.
- RH, Hodge, complex Euler and Navier–Stokes, and BSD are targets of the same objects. Their Lean
  is worked alongside every step, never behind the HNN and never as a separate category.
- Athena is the HNN's first intended product. Text, code, image, sound and motion are boundary
  charts of one machine: a design is checked against every chart, and whatever is particular to a
  medium lives only in its boundary codec.

## 2. The steps

The milestones are the steps; each issue body holds its dated status line and its "Done when" boxes.

| Step | Issues | Done when | Where it stands |
|---|---|---|---|
| 4–5. The HNN learning law and its card realization | #73, #76; the helical code #386 (critical); the contact and chain laws #408 | the HNN learns through its own deposition, a reached comparison changing located material, on the card with host parity for each law (#73, #76); the helical code's and the contact laws' boxes (#386, #408) | campaigns 1 and 2 built; the field learner of step 8 runs on the card at parity with its host reference; campaign 2's criterion and learned physical repair stay open (#73) |
| 6. Equation extraction | #146 | a foreign realization's operators and coefficients are read as native element relations, interconnection and navigators; inherited coefficients seed the engine's initial configuration (the overture) and are never served | unparked October 29; SmolLM2's layer 0 founds a participating level on the host, and four terms remain before a source layer is a native level |
| 7. Lean curation | #147; every owed statement is one box in #410 | #147's boxes | the first pass, the renames and U0's owner consolidation are done |
| 8. Athena alpha | #404 with #405, #406, #407, and the November 2 review's #601, #602, #603 | #404's boxes: real text learned online through the native route, kept by retained deposition, a cold restart, a question answered from the retained state with its sources, readable text shown whole | the field on a code passage, learning lap by lap on the card (§3) |
| Parked | #409 | the target laws #20, #22, #23, #32 and the contact terms #30, #31 | closed until their work starts |

## 3. The campaign under way: Athena alpha on a code passage

**The terrain.** Since November 5, at Brandon's request, the field learns Python code
([the passage record](../../research/records/2026-11-05_THE_FIELD_MOVES_TO_A_CODE_PASSAGE_WHOSE_CLOSURES_ARE_BRACKETS_STRINGS_AND_BLOCKS.md)):
`flytech/python-codes-25k`, converted at the exterior boundary into records `question US answer RS`,
every byte as the row holds it. 128 problems are held, chosen in a keyed order among the rows whose
instruction and output stand in no other row, so no held question or answer is met in training. One
problem is one field: the question's sites are known, the answer's sites are open, and the answer is
refined and released whole ([the one-field record](../../research/records/2026-11-01_THE_PROBLEM_IS_ONE_FIELD_EVERY_SITE_READS_EVERY_OTHER_AND_THE_ANSWER_IS_REFINED_NOT_SPOKEN.md)).

**The field's law.** The faces are the forces of one stored energy.
- Each tick descends one energy `Φ` of the region's state and letters: the receivers' lock
  partitions, the strand pair's contraction and the letters' rows read against the sites they reach.
- A letter's face is the total derivative `z_t(a) = −dG/de_t(a)` of `G(e) = Φ(x^K(e); e)`, read
  through the opening and the `K` declared ticks, so its Hessian is symmetric.
- Owners: `hnn::tower::field` and `hnn::tower::field::energy` (the host reference) and
  `holonics-cuda`'s `hnn::field` (the card), equal bit for bit on the energy parity suite. The
  derivations and every lap's receipt are in the running record, the
  [dispersing field record](../../research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP.md)
  from its §16.47.

**The learner** (`FieldLearner` in `crates/holonics/examples/solenoidal_alpha/complete_language/field_train.rs`).
- A section deposits the contrast of the truth against one kernel step from it:
  `(1/T) Σ min(1, A)[∂G/∂θ(truth) − ∂G/∂θ(e′)]`. The proposal `e′` draws a block of answer places
  from their faces, and `A = 2^((G − G′)/T) Π face′(truth)/face(a)` weighs the move, so by detailed
  balance the expected deposit vanishes at the true distribution.
- Each problem's residue class is cut into blocks of at most `k*` places, each its own kernel step,
  with `k*` read again each section.
- Each family steps at `2^(−ρ_f)`, its length read from its own transfer to the next section, and the
  letters' temperature `T` learns from the energies already read.

**The loop.** A lap walks the training passage's 1,543 sections on the RTX 4080 SUPER in seven to
eight minutes. Each lap's law is fixed before launch, the theory thread's guesses are written down
blind, and the lap ends in its receipt in the running record. An iteration between saved states stays
within one hour on the card (Brandon, November 6); a run that would pass it is a design change, not a
longer run.

**Where it stands, by measurement (lap 9).** The held answers' enumerated code (every letter's `G`
read, at 64 held places) fell from 6.639 bits a place at founding to 4.786, against 4.93 for the
letters' own frequencies: a paired change of −0.178 at lap 9 with standard error 0.135. The faces
propose worse as the energy sharpens (`KL(enumerated ‖ face)` from 0.25 to 0.52), so a writer that
releases on the faces misses the context the energy carries.

**The order within step 8.**
1. The learner takes the held code past the letters' frequencies by more than its error, and keeps
   it falling, lap by lap.
2. The writer releases from the energy itself (its own kernel), not from the faces' mean field, and
   its writes are shown whole as they come out.
3. The card realization moves the lock scores, words and rows onto the tensor cores as limb products:
   every term keeps its declared width and integer sums are associative, so the bits are unchanged.
4. #404's remaining boxes follow on that learner: retention across passages, a cold restart on the
   card, and a question answered from the retained state with its sources.

## 4. Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)) and which part of the
  line it serves.
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it:
  read, rewritten against the current objects, and tested by the law it implements. Nothing is
  restored wholesale or kept for compatibility.
  - The census at `13f8c734` locates history's owners
    ([`RUST_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/RUST_R0.tsv),
    [`LEAN_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/LEAN_R0.tsv)),
    and so does the manifest on `archive/leftovers-2026-09-24`.
  - Each port is recorded in its step's issue as history path, new owner, law and test.
- **Do not port** what the retention audit and the lessons retired: the per-occurrence tape and
  frozen-cut replay; `returns` journals and archives of completed updates; slot, session and episode
  wires; byte and nibble codecs; key/value stores, context indexes and copiers; foreign forward
  graphs taken whole; any Lean inside the HNN; floats inside a law.
- **Precision is the bit widths of graphs** (CLAUDE.md and AGENTS.md, the governing laws). No float
  is stored or consumed inside a law or the machine. Each term has a declared width, a carrier widens
  at a declared crossing, and a term is released only at a declared tolerance with its remainder
  carried.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA, and
  `holonics-cuda` depends on it and realizes its operations. Brandon's `codex/apple-silicon` becomes
  `holonics-apple`, implementing the execution port only after the host reference exists, with parity
  for each law.
- **Learning runs on the card** (CLAUDE.md, "GPU first"). A part enters a learner run with its card
  realization and its parity against the host; the host realization is the reference that checks the
  card's bits.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #410.
- **Tests are written for each law.**
  - A test proves its law on the smallest fixture that exhibits it and runs well under a second in a
    debug build; no test builds a campaign's field.
  - Measurements (code curves, timings, laps) are examples run once in release and reported with their
    command and result as receipts, never as gates.
  - A check that an optimization changes no value runs once on the real case as a receipt; the suite
    keeps only its small-fixture law.
  - Cost is a property of the representation: a local, block-sparse law is implemented and certified
    block by block, never by assembling a dense global object.
- **A development read decides; the held read confirms.** A hypothesis is measured first on
  development material, the held read runs once a law, and seen material is never graded as unseen.
  Campaigns on disjoint owners run together, each with its own receipt, and each new law lands at
  its consuming owner, retiring any duplicate in the same change.

## 5. Protocol

- **Pinned families.** Before a validation, its choosing and validation families are pinned by a
  declared keyed split, with the consumer, the charges, the baselines, the acceptance and a
  deadline.
- **The evaluation partition.** The September dataset's evaluation families stay closed. F5, Athena's
  first product outcome, alone reads them, once, after every product gate has passed on development
  material.
- **Budgets.** Each run is projected before it launches (CLAUDE.md, the waiting standard): its time
  from a development read on the card, a deadline fixed at the projection's upper end, at most 12 GB
  of the card's 16 GiB, and the host part's threads declared.

## 6. The September gates, as they came out

The gates F0 to F6 of the forward plan of September 27 stand word for word at
[`0a051ae5`](https://github.com/brandonrdug/holonics/blob/0a051ae5/docs/plans/THE_REBUILD.md#the-gates-inherited-verbatim).
They were set for the receiving population over the landmark tree, which the tower and the field
replaced as Athena's learner in October.

| Gate | What it asked | How it came out |
|---|---|---|
| F0 | the predictor on unseen families | diagnosed September 28: the population memorizes families and its standing is an index ([record](../../research/records/2026-09-28_THE_FORWARD_PLAN_STOPPED_AT_TRANSFER_THE_POPULATION_MEMORIZES_FAMILIES_AND_ITS_STANDING_IS_AN_INDEX.md)) |
| F2 | the field as a population family | on fresh families the code was strictly shorter, but a window cost 46 times the passage budget, so the field stayed dormant for text (September 28) |
| F3 | the resident population | superseded by learning on the card (#76) |
| F4 | release | its failure branch: the text-release carrier incomplete and the charged validation stream above the flat control |
| F5 | Athena-0, the first product outcome | development diagnostics only, their split spent; the evaluation partition stays closed (§5) |
| F6 | motion: the chase terrain, then the motor chart | its motion was chosen by a planner the author wrote, so learned motor navigation is not shown (audited October 3); the switch bullet passed and the capture bullet failed, 7 of 16 seeds |

The numbered Decisions 1 to 39 of September resolve through the
[Decisions index](https://github.com/brandonrdug/holonics/blob/0a051ae5/docs/plans/THE_REBUILD.md#the-decisions-index).

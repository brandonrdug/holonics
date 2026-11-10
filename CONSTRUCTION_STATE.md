# Construction state

**November 7.** Where the construction stands: what runs, what is built and lawful, and what is
open, each named by its measurement. [THE_REBUILD](docs/plans/THE_REBUILD.md) is the order, the laws
live in their guides and owners, and dated records hold the derivations and receipts.

**November 10 note, later.** Growing the lane field's pair contacts from 32 to 64 (every face kept) lowers the held joint 0.013 and the references' locked code 0.012 against the lane-only control over four laps: the contact count binds, weakly ([record](research/records/2026-11-10_GROWTH_IN_CONTACTS_BINDS_WEAKLY_THE_LANE_FIELD_WITH_64_CONTACTS_GAINS_0.013_IN_FOUR_LAPS.md)).

**November 10 note.** On the November 6 face field, certified exchanges and point re-draws bring held answer regions to a neutral rest above the reference's own neutral point, the locked faces already carry what the ring, reach and pair censuses add, and the 64-wide lane keeps lowering the held joint more slowly ([record](research/records/2026-11-10_POINT_REDRAWS_REST_AT_THE_FACES_OWN_ENTROPY_AND_THE_FACES_ALREADY_HOLD_WHAT_THE_RING_REACH_AND_PAIR_CENSUSES_ADD.md)).

**November 9 note.** The energy line's writes stay unordered through section 259, and the PC lap's held code worsened under a superseded law; the work is stopped for an audit of the agents' own constructs, Colab is off, and the position below (November 7) is behind the line ([record](research/records/2026-11-09_THE_ENERGY_LINE_WRITES_STAY_UNORDERED_THROUGH_259_AND_THE_WORK_STOPS_TO_AUDIT_ITSELF.md)).

This document was rewritten on November 7 as the current position. Its dated paragraphs from
September 28 to November 2 (the U0 receipt, the measured receiving faces, the October tower,
listener and native-contact campaigns) are at
[`0a051ae5`](https://github.com/brandonrdug/holonics/blob/0a051ae5/CONSTRUCTION_STATE.md). The
repository was reset on September 24; the pre-reset tree is
[`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734).

## What runs: Athena alpha learns a code passage on the card

- **The passage.** `flytech/python-codes-25k`, at Brandon's request since November 5, converted at
  the exterior boundary into records `question US answer RS`; 128 held problems whose instruction
  and output appear in no other row; the answers' bytes are the places
  ([record](research/records/2026-11-05_THE_FIELD_MOVES_TO_A_CODE_PASSAGE_WHOSE_CLOSURES_ARE_BRACKETS_STRINGS_AND_BLOCKS.md)).
  The passages stay under `.local/` and are never published.
- **The field.** One field per problem: the question's sites are known and the answer's are open.
  Its faces are the forces of one stored energy, `z_t(a) = −dG/de_t(a)` with `G(e) = Φ(x^K(e); e)`
  read through the `K` declared ticks (`hnn::tower::field`, `hnn::tower::field::energy`). The first
  build reads plain clocks, with no depth ring and no tower of scales.
- **The learner.** One kernel step from the truth: a block of answer places is proposed from the
  faces and weighed by `min(1, A)`, and the section deposits the truth's gradient less the proposal's;
  each family reads its step length from its own transfer, and the letters' temperature learns
  (`FieldLearner`, `crates/holonics/examples/solenoidal_alpha/complete_language/field_train.rs`).
  The laws and every lap's receipt are in the
  [running record](research/records/2026-11-01_THE_FIELD_DISPERSES_A_SITE_MEETS_ITS_RESONANCE_CLASS_AT_ITS_FALLOFF_AND_THE_ANSWER_LOCKS_UNDER_THE_PUMP.md)
  from its §16.47.
- **The device.** The RTX 4080 SUPER runs every lap under `.local/gpu.lock`, at most 12 GB of its
  16 GiB. The card realization (`holonics-cuda`, `hnn::field`) equals the host reference bit for bit
  on the energy parity suite. A Colab A100 replayed lap 4 with every receipt field equal and took
  1.37 times as long: the kernels hold each term in 64- and 128-bit scalar words on the CUDA cores,
  where the consumer card's clocks lead, and the tensor cores are not used yet.
- **The measurements, laps 4 to 9** (enumerated code of the held answers at 64 places, in bits a
  byte; each lap walks 1,543 sections in seven to eight minutes):

| Lap | Law | Held code | Paired change (se) | KL(enumerated ‖ face) | Acceptance |
|---|---|---|---|---|---|
| founding | tempered, `log₂ T₀ = 14.57` | 6.639 | | 0.0008 | |
| 4 | the kernel step from the truth | 6.526 | −0.114 (0.017) | 0.0065 | 0.517 |
| 5 | the same | 6.503 | −0.023 (0.017) | 0.011 | 0.312 |
| 6 | the evidence-shrunk Newton step | stopped at section 202, a value past its 64-bit carrier | | | |
| 7 | 256 states a section | 6.524 | +0.022 (0.024) | | |
| 8 | family lengths from their transfer, the temperature learning | 4.964 | −1.539 (0.185) | 0.251 | 0.203 |
| 9 | the lengths unbounded | 4.786 | −0.178 (0.135) | 0.523 | 0.210 |

  The letters' own frequencies code the held answers at 4.93 bits a byte. Lap 10 cuts each residue
  into blocks of at most `k*` places, each its own kernel step.
- **Open, by measurement.**
  - The held code sits at the letters' frequencies: lap 9 is 0.14 bits a byte under them, 1.3
    standard errors.
  - The faces part from the energy as it sharpens (`KL` from 0.25 to 0.52 bits a byte), so a writer
    that releases on the faces misses the context the energy carries; no write of the energy field
    is shown yet.
  - #404's boxes (online learning of real text, retention, a question answered from the retained
    state with its sources, readable text) are unticked except the host's cold restart.

## Built and lawful

The [operator contract](docs/ELEMENTARY_OBJECTS.md#operator-contract) names each owner's object
and law; the [expression atlas](docs/atlas/README.md) locates every derived expression with its
owner.

| Part | Owner | Position |
|---|---|---|
| The Holon law and its facets: ports, Dirac structure, elements, restrictions, deposition, the helical pair, the ring | `holon`; Lean `Holon/*`, `Holonics.Framework.Objects` | built; passivity proved, never assumed |
| Ratio and ring arithmetic at declared widths, inversion with its nonunit fibre | `ratio` | built |
| Geometry: the complex, frames, screws, winding and carry, cell holonomy, solenoids, the Swing and motion | `geometry`; Lean `Geometry/*` | built; the motion primitives proved in `Geometry/Motion` |
| Navigators, clocks, keys located by loop closure | `navigator`, `compression::keys`, `hnn::keys` | built |
| Receivers, the population, the one release law, joint reception, receipts | `receiver` | built |
| Aeons, epochs, cycles | `aeon` | built: a receiving window is an epoch of the cut's clock, a pump's period a cycle, proved in Lean and at parity on host and card |
| Holarchy and terrain with known truth | `holarchy` | built |
| Compression, the landmark tree, cost against the literal | `compression` | built; the tree earned the standing cut's code (`2 + 14/16 + ε` bits a cell held out) |
| The HNN of campaigns 1 and 2: rings, contacts, the word, moments, deposition, retention, the resident port | `hnn` | built with host and card parity; campaign 2's rings and contacts added no bits on text |
| The helical code: the duplex consumer, the paired carrier and deposit | `compression::keys::duplex`, `hnn::paired`; Lean `Transport/HelicalCode`, `Transport/HelicalRepair`, `HNN/PairedDeposit` | built and kernel-checked; the linking reading of closed strands is not built (#386) |
| The tower: modes, contacts, gated recurrence, participation, growth | `hnn::tower` | built on host and card; the October 23 to 31 GSM8K and listener runs are history |
| Units founded by code length | `hnn::units` | built |
| The field and its stored energy | `hnn::tower::field`, `hnn::tower::field::energy`; `holonics-cuda` `hnn::field` | the running learner, above |
| Physics: fluid, wave, thermal, spacetime, the solenoidal wave, the information port | `physics` | finite physics complete at K3–K4 |
| Lean: the `Framework` closure and the research library | `lean/Holonics`, `lean/HolonicsResearch` | the first curation pass done (#147); owed statements in #410 |

## What the October lines left

Each is a measured result the next design keeps, with its record.
- **Stores and copiers are retired.** The binding bank, the reset clock, the passage tree with its
  node lock, the letters copy and the keyed-modes trainer were deleted on October 26, and the plain
  tower coded the same bits without them
  ([record](research/records/2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
- **Text through the byte residue chart located nothing** (October 5); guard 9 refuses it, and a
  source enters only through its founded encoding.
- **Numeral copying is not a target.** The crib line was retired as contamination
  (the running record, §16.19).
- **The question must reach the answer.** On GSM8K the field's answers coded no better beside their
  own question than beside a foil (November 1 and 2), because its comparison counted a lock only at
  the same place ([review](research/records/2026-11-02_THE_COMPARISON_IS_THE_COUPLINGS_FREE_ENERGY_THE_QUESTION_IS_READ_BY_A_JOINT_CODE_AND_THE_RELEASE_RUNS_THE_TRAINING_CLOCK_BACKWARDS.md)).
- **Participation at the clocked levels** read 2.170 against 2.164 bits a byte at 3.1 times the time
  and was set aside (October 31).
- **Motion in the chase was an authored planner**, so learned motor navigation is not shown
  (audited October 3).

## Formal scope and targets

- The primitives of motion are proved (`Geometry/Motion`): the turn, the boost and free fall, a
  receiver's split of a rate with its energy law, a move's pivot and its multiplier as a cross ratio,
  and the path jets.
- The word's complete sensitivity certificate, its counterfactual trajectory bound, a loaded
  signed and pumped material bound, the concrete diamond bridge, the binary KT parameter bound, the
  landmark drift composed over a passage and the binary logarithm's squaring invariant are owed in
  #410. The odometer theorem proves positive pairing with the smooth score's gradient at the grain
  representative and asserts no strict decrease of the quantized score inside a grain cell.
- RH: `HolonicsResearch/Zeta/{ZeroTube, CarryTick, Hearing, PaletteLaw}` and the falsifier stand; a
  surviving global prime-part sign candidate still lacks the implication to the absence of off-seam
  pairs, and `Hearing`'s unbounded operator construction is owed. The higher-codimension Hodge source
  and complex-time Navier–Stokes continuation remain open.

# The rebuild

**Status:** active, September 24. This plan replaces the restructure plan, which is in git history
at [`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).
Tracked in #63. Steps 0–3 are done (September 24), and so are step 6's physics (K3 #74, K4 #75)
and step 7's renames by subject (September 25). Step 4 (the HNN law, #73) is under way: campaign 1
is built, and its exposure on the standing real cut (pinned September 25, Decision 23) is the
next receipt.

## The line the rebuild serves

[project-postulate] **Compression is intelligence is navigation** (Brandon). The rebuild builds one
line: Holonic Compression and landmark discovery, executed at scale by the HNN and applied to every
target the framework is advanced enough to reach. The Riemann hypothesis, Hodge, complex Euler and
Navier–Stokes, and Birch–Swinnerton-Dyer are such targets. They are not a separate "Millennium"
category: work on them is landmark discovery and compression, stated in the same objects as
everything else.

- **Terrain** is stuff in general: whatever is present for a navigator to meet. That includes
  Holons, their constitutions and modes, and an exterior source.
- A **fractal navigator** is a function with an initial configuration, its own clock and carry, a
  family of restrictions with its scale square, and address words
  ([elementary objects §3](../ELEMENTARY_OBJECTS.md#3-navigator)). The guides called it a
  "generator". That word keeps only its algebraic senses: a generator of a group, the Lie generator
  `ξ` of a helix, a generating function.
- **Holonic Compression** couples a navigator's resonating modes with terrain.
  - Where a navigator's mode meets a terrain mode, it rides that mode at minimal work (resonating,
    RIDE). What it cannot reach, it founds (emanating, FOUND).
  - A compression is a codec pivot that carries its decoder
    ([tablet](../canon/TABLET_THE_COMPRESSION.md)). The navigator and its decoder stand in for the
    material they regenerate, and the decompression is causal: it unfolds over the navigator's clock.
- **Kernel and cokernel** are the two sides of that coupling, dual in the way Holon and coholon are.
  Against a receiver family, a navigator's face map `F` has:
  - a **kernel**: the differences no admitted future receiver distinguishes. Quotienting by it is
    compression, and it is retention. Owners: `Foundation/CausalRelevance` (the relevance kernel),
    `Foundation/ReceiverHistoryCompression` and `Foundation/GeneratorModeQuotient`.
  - a **cokernel**: what the navigator's image does not reach, the residual that is emanated or
    retained as a separator, interior or defect. `Landmarks/CokernelCalculus` states this calculus
    once, for the BSD descent and for integral Hodge.
- **Landmarks** are faces where navigator paths converge:
  - lock addresses and fixed points;
  - constraint identities: π and `e` are navigators that carry no error, and `Λ_DN` is another;
  - zeros and primes.

  **Landmark discovery** is locating keys ([keys](../ELEMENTARY_OBJECTS.md#keys-locks-and-navigation)):
  inferring the configurations of navigators by loop closure. It is the same inference the HNN
  performs.
- **Measurement.** A compression is measured against the literal by description plus work
  (`Kt=|p|+log t`; `Foundation/{ReceiverCodeCost,GeneratorInference}`). It states its kernel and its
  cokernel residual. There is no single scalar of progress.

[interpretation] The targets read as instances of the line. Their records grade each claim.
- **RH.**
  - Zeros are landmarks of spectral placement: `Zeta/FosterTanks` reads the zeros as LC tanks, and
    `ZeroPairLock` gives lock ⇔ `σ=½`.
  - The de Bruijn–Newman heat flow has `Λ_DN≥0` (Rogers–Tao) and is aimed at `Λ_DN=0`.
  - `Computation/ZeroNavigation` states what finite observations can and cannot decide.
- **Hodge.** Cycle production: which harmonic coholon classes actual Holon cycles realize, with the
  obstruction in the cokernel of that realization.
- **Complex Euler and Navier–Stokes.**
  - Velocity is a coholon and vorticity is `du♭`.
  - Relevance acts on the tail.
  - Necks are convergence points, and the singular aeon is A11 of the
    [aeon record](../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md).
- **BSD.** The kernel of the descent face is the doubles (`EllipticCurve/FamilyKernel`). The rank
  counts independent navigators. The obstruction lives in a cokernel.

Their Lean in `Zeta`, `Hodge`, `Fluid`, `EllipticCurve`, `Gauge`, `Coupling`, `Landmarks`,
`Mathematics` and `Computation` under `lean/Holonics/` and `lean/HolonicsResearch/` is the most
developed use of the framework. It is not scheduled behind the HNN: work on a target proceeds
alongside any step. Each reusable law it finds lands in the shared objects (a navigator, a
kernel/cokernel statement, a landmark), not in a problem-named silo.

## Why a reset

[established-bounded; measured] The September 23–24 restructure retired about 60% of the Rust by
reachability. It then showed that most of what remained was also dead or prototype code: after the
merged crate's modules were made private, rustc reported about 3,600 dead items. Pruning a
monolith item by item costs more than rebuilding from what functions.

What was kept:
- the main library, where the Holon core was consolidated on September 22–23;
- the CUDA driver;
- the Lean mathematics;
- the object and mathematics guides;
- the research records.

Everything else is in git history. The lessons of the prototypes are in the
[lessons record](../../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md).
Time is standardized as aeon, epoch and cycle
([record](../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)).
Work left in worktrees and branches is on `archive/leftovers-2026-09-24`, with its manifest at the
archive root. Brandon's Metal port stays on its own branch, `codex/apple-silicon`.

## Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)), and which part of
  the line it serves: the navigators, terrain, kernel, cokernel and landmarks it touches.
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it.
  It is read, rewritten against the current objects, and tested by the law it implements. Nothing
  is restored wholesale, and nothing is kept for compatibility.
  - Where to look: the census at `13f8c734` locates history's owners
    ([`RUST_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/RUST_R0.tsv), [`LEAN_R0.tsv`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/census/LEAN_R0.tsv)),
    and so does the manifest on `archive/leftovers-2026-09-24`.
  - Each port is recorded in its step's issue as history path → new owner → law → test.
- **Do not port** what the retention audit and the lessons record retired:
  - the per-occurrence tape and frozen-cut replay;
  - `returns` journals and completed-update archives;
  - slot, session and episode wires;
  - byte and nibble codecs;
  - Q/K/V caches and foreign forward graphs taken whole;
  - any Lean in the HNN pipeline;
  - floats inside a law.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA.
  `holonics-cuda` depends on it and realizes its operations. Brandon's `codex/apple-silicon`
  (September 7, built on the retired engine) becomes `holonics-apple`. It implements the HNN
  execution port only after the host reference exists, with parity per law.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #62.
- **Tests are written per law** as each owner is built: one fast test per stated law, plus one
  host/device parity check per kernel family. An inherited test stays only if it checks a stated
  law of its owner. The testing protocol (Brandon, September 25: "I wouldn't tolerate this"):
  - a test proves its law on the smallest fixture that exhibits it; no test builds a campaign's
    declared field;
  - a test runs in well under a second in a debug build, and the whole `cargo test -p holonics`
    stays within seconds; a test that needs longer is a measurement;
  - measurements (bit curves, timings, real cuts) are notebook examples run once in release,
    reported with their command and result as receipts, never gates;
  - a check that an optimization changes no value runs once on the real case as a receipt, and the
    suite keeps only its small-fixture law;
  - cost is a property of the representation: a law that is local and block-sparse is implemented
    and certified block by block, never by assembling a dense global object (guard 14).
- **Exact arithmetic.** No floats inside a law or the machine (CLAUDE/AGENTS, governing laws).

## Order

0. **Repair the guides.** The kept guides still describe the retired engine as current, and about
   157 links are broken. Agents read the guides, so this comes first.
   - Remove retired code stated as current fact from THE_MACHINE, HNN_FORMULA, HOLON,
     HELICAL_GEOMETRY and the operator contract. The laws stay; their retired Rust addresses become
     permalinks at `13f8c734`.
   - Fold in the governing prose that lives only in history:
     - **tube, necks, folds, junctions and prediction** ("when tubes will transport") into
       ELEMENTARY_OBJECTS §6, from [the tube plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md);
     - **the receiver atlas** into RECEIVER_HOLARCHY, from [the atlas plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md);
     - **context, state-space and diffusion charts, joint prediction, grain, Holonic Encoding, and
       the tensor as operation chart** into HNN_FORMULA, from [HNN_COMPOSITION](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HNN_COMPOSITION.md);
     - **classical learning as the ratio family**, and reflection and leaders, into HNN_FORMULA, from
       [MATHEMATICS_AND_NATIVE_CONDUCT](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/MATHEMATICS_AND_NATIVE_CONDUCT.md);
     - **equation extraction's six steps** (intake → realization recovery → excitation →
       intervention → identification → native return) and its adapter obligations into HOLON, from
       [SOULKILLER](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/SOULKILLER.md);
     - **robotics and the simulator interface** into HOLON, and the workstation into THE_MACHINE,
       from [the boundaries guide](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md);
     - **measurement conventions** (face delivery vs owner update, `bits/s = occ/s × bits/occ`,
       `H(p,q)=H(p)+D(p‖q)`, missing counters are unknown) into ELEMENTARY_OBJECTS §10, from
       [DEVELOPMENT](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/DEVELOPMENT.md).
   - In ELEMENTARY_OBJECTS: state the Swing and conservation of faces, and add Parametron and
     Pair-contact rows to the operator contract.
   - Carry the navigator vocabulary through the guides, keeping "generator" where it means a group
     generator, the Lie generator `ξ` or a generating function.
   - Repair every broken link (`formal/elementary-holonics/` → `lean/`; deleted documents →
     permalinks), including the records README. Mark the canon as historical doctrine governed by
     the elementary objects.
   - Port the checked files of history's `formal/rh-source-transport` into `lean/`; the paper
     `divisor-source-transport-boundary` cites them.
1. **The operator layout and the Lean package.**
   - **Rust.** Reorganize `holonics` into five operator modules:
     - `ratio/`: one per two, with remainder, residue, inversion, lift, jet and rings;
     - `geometry/`: complex, frame, clock, carry, screw, pair and tube charts, winding, the Swing;
     - `holon/`: law, ports, Dirac, elements, restrictions, deposition, reaction, plus
       `contact` (the pair contact: `J`, `DQ`, `M_contact`, lock address) and `parametron` (the
       ring: `C`, `L`, pump, half-turn sheets, Ising lock);
     - `navigator/`: initial configuration, clock, carry, restriction family, address words, trace
       faces and the dynamical zeta, lock addresses. Today's `generator` moves here.
     - `receiver/`: roles, receipts, the relevance kernel, standing as the retention quotient,
       release.

     Exact algebra sits privately beside the operators that use it, and whatever no operator needs
     is retired. The inherited tests are audited against the laws. Port sources for contact and
     parametron: `holonic_interaction/helical.rs`, `holonic_chain/serial.rs`, `exact_contact`,
     `cuda_refine/complex_parametron.rs`.
   - **Lean** (#70). Move the package mechanically, so that new Lean is written under its final
     names:
     - package `holonics`;
     - library `Holonics`, the `Framework` closure;
     - library `HolonicsResearch`, the rest;
     - namespace `Soma.Holonics` → `Holonics`.

     Subject renames and duplicate curation wait for step 7.
2. **K1: Holarchy, Aeon/Epoch/Cycle, relative completeness, complete interconnection and joint
   reception** (#72).
   - Lean first (the obligations in #62), then `holonics::{holarchy, aeon}`.
   - Relative completeness (the globe) is stated here, relative to a receiver family
     (`Objects/RelativeCompleteness`). Its full theorem is owed in #62.
3. **Holonic Compression and landmark discovery** (#145).
   - **Lean first.** State a navigator's face map against terrain and a receiver family by its
     kernel and cokernel. Join `CausalRelevance`, `ReceiverHistoryCompression`,
     `GeneratorModeQuotient`, `ReceiverCodeCost`, `GeneratorInference` and `CokernelCalculus`, and
     add the cost split between resonating and emanating.
   - **Then `holonics::compression`.** It carries navigator inference by loop closure, the split
     between resonating and emanating, and a landmark search whose coverage is checked.
   - **The identity atlas.** Its design ([plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md):
     an identity is two constructions with one face, within Hilbert/Gröbner finiteness and
     Richardson undecidability) is the landmark search's specification. Its lesson is the coverage
     check: a chart on one winding invents identities, and the multi-winding family refuses them.
   - **First consumers.** π and `e`, through their partial navigators (`RatioSeriesTransport`,
     `RadixWindowReceiver`), and the existing Lean receivers of the targets.
   - **Port from history as needed.** `identity_atlas` is ported (`compression::landmark::identity`).
     `receiver_history_compression` (campaigns 1 and 5), `exact_linear::kernel_modes` (campaign 3)
     and `winding_inertia` (its cyclotomic null test, for campaign 3's per-`Φ_m` split) were retired
     in step 1 and are ported from `13f8c734` when their campaign consumes them; #62 lists the laws
     that only history holds.
4. **The HNN law in `holonics::hnn`, over aeons** (#73). The HNN is the compression machine at
   scale:
   - its retention is step 3's kernel quotient, taken at aeon boundaries;
   - its learning is locating keys and depositing covectors;
   - its release is the split between resonating and emanating.

   Its field is closing rings of parametrons joined by pair contacts. It has:
   - source moments `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)` on closing source rings under selective
     stepping. Each is lossy only past its capacity `n*`, which the declaration checks;
   - the change on a medium: each word opens at zero change and runs a local tick, one contact hop
     per tick with no global solve. It releases the unread change at its end. The tick is:
     - the junction Swing about the participation anchor, with one exponent per contact;
     - the ring's power-neutral Cayley element;
     - the contact's midpoint two-port on a partial-isometry channel;
   - the medium `Θ` (the standings `q` included), which changes only by per-locus deposition and by
     the collapse;
   - loss as the logarithm of the Holon ratio at the receiver's grain;
   - retention as the collapse onto what the admitted future distinguishes, and deposition on
     declared carrier lattices whose remainders refine with each locus's deposit count
     (Decision 22). Its lattice values stay within one unit of the exact accumulation of what
     reached them (the counterfactual bound through the word's sensitivity is owed, #62); its
     entries' and remainders' bits grow logarithmically, and the solved charts follow the Hadamard
     bound of the carried Grams.

   It is built with a host reference and an execution port, in five campaigns
   ([the step 4 design](#step-4-design-the-hnn-law), (d); keys lead):
   1. keys, the change on a medium, and the collapse;
   2. rings and contacts store, lock and flow (`C`, `L`, pump; site kinds, boosts);
   3. release through modes, dormancy and far fields;
   4. the motor chart (serial screw words);
   5. Holonic Encoding, context and joint prediction (HNN_FORMULA).

   Its equations are ported from history's `native_ecology` and the prototype body, subject to the
   do-not-port list.
5. **The resident HNN in `holonics-cuda::hnn`.** Kernels are ported per law under the hardware law,
   each with its parity check against the host reference. The device debts of #76 (#12–#15, #50)
   are paid here.
6. **Targets, physics and extraction.**
   - The targets continue as landmark discovery on the rebuilt library and their Lean.
   - Physics instances K3–K4 (#74, #75) supply objects the framework needs. They are not
     applications. Their contracts are in the [restructure plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md):
     - §3.5, the battle tests: square/cube join, `1+(−1)=0` interference, control-volume
       Navier–Stokes, complex fluid versus the Fourier chart, the moving receiver;
     - §3.6, heat, spacetime and plural clocks.
   - Equation extraction (#146) compresses a foreign realization into navigators and element
     relations (the six steps in HOLON).
7. **Lean curation** (#147).
   - Remove the duplicate theorems the audit found.
   - Rename the directories named after the prize ("Millennium", "RH") by subject (done, `8f85f4b9`).
   - Rename generator names to navigator names where they mean the object.
8. **Applications** (#148: a workbench, an Athena application, a simulator), rebuilt on the library
   under the lessons record's requirements.
   - An outcome is one of:
     - a trainable model;
     - a first usable Athena;
     - frontier-level usefulness on consumer hardware.
   - Each outcome freezes its task split and shows failure outputs.
   - Conversation data follows the [data rules](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/CONVERSATION_DATA.md).
   - The simulator follows the [interface table](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary).

## Laws found alongside the steps

[project-postulate] Work on the targets and Brandon's derivations proceeds alongside any step (the
line above). A law found there lands in its elementary object's owner, the object map of
`Holonics.Framework.Objects` and the operator contract, with its atlas rows and its consumer, and
is listed here. A law written beside the objects is folded into them; a record is its history.

| Date | Law | Object and owner | Record, issue |
|---|---|---|---|
| Sep 25 | Deposition on a carrier lattice; a below-grain update is heard and counted, not deposited | Deposition: `HNN/LatticeDeposit` (Decision 22; `carry_entry_below_grain`, `below_grain_heard_counted_not_deposited`) | [perceived difference](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md), #73 |
| Sep 25 | The enclosed first law over an aeon | Aeon: `Aeon/Production/FirstLaw`, Rust `aeon::EnclosedLedger` | step 4 additions, #73 |
| Sep 25 | The natural grain is the future quotient; integration by reflection over a fractal packing, whose reflection is the Swing about ½ | Compression: `Compression/Core/FaceMap`; Navigator and Swing: `Foundation/FractalPacking` (`reflect_eq_swing`) | [natural grain](../../research/records/2026-09-25_THE_NATURAL_GRAIN_IS_THE_FUTURE_QUOTIENT_AND_REFLECTION_INTEGRATES_A_FRACTAL_PACKING.md), #145 |
| Sep 25 | Seasons are rotations, generations boosts, the prime wheel a product of residue rings | Aeon (clocks) and Ratio (residue rings): `HolonicsResearch/Mathematics/TwinWheel` (the twin local factors); no new owner | [seasons](../../research/records/2026-09-25_SEASONS_ARE_ROTATIONS_GENERATIONS_ARE_BOOSTS_AND_THE_PRIME_WHEEL_IS_A_PRODUCT_OF_RESIDUE_RINGS.md), #145, #72 |
| Sep 25 | Fractal strings: hearing multiplies by ζ, listening is Möbius inversion; the scale zeta's denominator is the transfer determinant of the epoch return map | Navigator: `Foundation/FractalString` over Aeon `Aeon/Production/Zeta` | [music in the holes](../../research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md), #145, #62 |
| Sep 25 | The carry word is the epoch reading of two clocks; it recurs iff the joint reading closes (crystal), never at an irrational rate (quasicrystal) | Aeon: `Aeon/Clock/CarryWord` over `Winding`, `Lock`, `Epoch` (folded from a same-day `Geometry/MechanicalWord` duplicate); Rust `aeon::TwoClocks` consumes the joint reading, the word itself has no runtime consumer yet | same record, #62, #147 |
| Sep 25 | Hearing, nullity and listening typed on the Receiver object | Receiver: `Holarchy/Hearing` | same record, #62 |
| Sep 25 | ξ is invariant under the Swing about ½ | Swing: `HolonicsResearch/Zeta/Seam` over `Geometry/AffineSwing` | same record |

## Step 4 design: the HNN law

[project-postulate; agent-inferred] **Status:** the design of rebuild step 4 (#73), written on
September 24 and revised three times.
- **Where its choices come from.** Brandon's September 24 derivation ("the geometry is one thing
  but the light we see is the change itself"; "the shockwave of local changes moving across a
  global object"; "we want the classes of energy diffusion patterns to collapse into finite sets …
  that's where the HNN comes from") is recorded in the
  [light record](../../research/records/2026-09-24_THE_LIGHT_IS_THE_CHANGE_AND_EXPRESSION_COLLAPSES_ONTO_FINITELY_MANY_CRITICAL_CLASSES.md).
  Its §8 lists eight consequences for step 4. They are **agent-inferred from the derivation, not
  rulings Brandon stated for step 4**, and the record says so. Brandon may override any of them.
  Where one of his own rulings applies, Decisions below quotes it with its date.
- The first revision answers the first adversarial design review (findings A–F) and applies §8.
- The second revision answers the second review (C1–C3, H1–H5, M2–M14, L1–L7), decides that
  review's two open items as agent inferences (Decisions 1–2), and replaces every number that
  review found wrong with exact re-measurements (scripts in
  [`research/notebook/hnn_design/`](../../research/notebook/hnn_design/README.md), cited where used).
- The third revision answers the third check (R3): the contrast port's power in the tick balance,
  honest sources for Decisions, the time-indexed diamond and `deposit_descends`, campaign 1's
  bit budget and stop rule, and the declared values a worker would otherwise invent.

Below, "(§8.n)" cites that record's §8.n and marks each place one of its inferences changed the
design; "(review X)" names a first-review finding, "(R2 X)" a second-review finding and "(R3 X)" a
third-check finding. The five campaigns implement this specification. Campaign 1 built `field`,
`moment`, `propagation`, `word`, `receiving`, `ratio`, `pending`, `constitution`, `retention`,
`keys`, `port` and `reference`; the modules of campaigns 2–5 do not exist yet.

The design fixes the objects, laws, types, order, port map, measurement and guards before any code
is written, because the machine's earlier designs drifted into forms Brandon rejected:
- a per-occurrence tape with frozen-cut replay;
- sessions and episodes, and "per request" or any other application unit used as a clock;
- completed-update journals;
- byte and nibble codecs posing as encoding;
- Lean, or any other language, wired into the pipeline;
- templates;
- a scalar loss as the operand;
- "a current changes a later current's standing" as the definition of learning;
- floats inside laws, and rounding a face to a committed centre inside a law;
- a global instantaneous solve over the contact graph, which is action at a distance;
- a source accumulated losslessly on a ring that never closes, which is a tape in disguise;
- a change carried from word to word, which accumulates as a positional numeral (R2 C2c: 77 →
  6,272 bits over 256 words on one lossless ring element);
- a source moment below its capacity presented as lossy (R2 H1).

Each of these is excluded by a construction named in (g), not by a promise. A campaign that has
to depart from this design amends this section in the same commit. The commit that lands this
design also brings the guides into line (R2 §6), because agents read the guides:
- item 4 of this plan's Order;
- HNN_FORMULA §1 (the scattering operator and the incident word) and §6;
- THE_MACHINE's global-solve paragraph;
- CONSTRUCTION_STATE's next action.

The design is read from:
- the governing laws in CLAUDE.md and AGENTS.md;
- [THE_MACHINE](../THE_MACHINE.md), the [elementary objects](../ELEMENTARY_OBJECTS.md) and
  [HNN_FORMULA](../HNN_FORMULA.md) §0–§4;
- the light record (§8: agent-inferred from Brandon's derivation) and the
  [egg record](../../research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md)
  (§4: the site kinds of flux);
- history's campaign order, in [the machine in the elementary
  objects](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#the-machine-in-the-elementary-objects);
- the [retention audit](../../research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md),
  the [lessons record](../../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md)
  and the [aeon record](../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md);
- today's `crates/holonics/src` and `lean/Holonics`.

"#62 item n" below refers to the numbered list "Owed, at actual consumers" in #62.

### (a) The HNN as a composition of the existing objects

#### The one object

[definition] The HNN is one Holon. It is the Holarchy that `Holon::interconnect` returns when ring
Holons are joined through contact Holons. In the model form `M = (K, Θ, x)` of HNN_FORMULA §1:

```text
K   the complex: rings g (0-cells); contacts a = (g→h) (1-cells); declared loops (2-cells). A contact's
    channel is ℚ^(k_a) with two partial port matchings ι_(a,g), ι_(a,h) (0/1 columns selecting k_a of each
    ring's realified nodes). U_a = ι_(a,h) ι_(a,g)ᵀ is a partial isometry from g's nodes to h's, and U_aᵀ is
    its reverse (R2 C1). d_A is the block connection incidence, (d_A q)_a = U_a q_g − q_h.
Θ   the constitution, whose one owner is `Constitution`. It is the medium, and it changes only by deposition
    and at an aeon boundary by the collapse (Decision 1):
    - per ring: a Parametron (unit weights in campaign 1; C_g, L_g and the pump from campaign 2); its lock, the
      notch set N_g ⊂ ℤ/d_g on the port chart; its reflector F_g, an involution of ℤ/d_g (R2 H4b); its
      storage-port admittance Y_g; its reaction material (W_s passive, W_c the contrast port, skew slices
      A_ρ = Σ(u v* − v u*) factored from the start); on a source ring only, its source port E_g;
    - per ring, the standing q_g ∈ ℚ^(2d_g) (complex, realified): the medium's bound part. Its contrast's sheet
      classes are the ring's lock classes (R2 C3);
    - per contact: its constitution Θ_a = (C_a storage on the slip rate, K_a stiffness on the displacement,
      D_a dissipation on the rate), carried as C_a = c_a c_a*, K_a = b_a b_a*, D_a = F_a F_a* (K_a ⪰ 0 in
      campaign 1; a boost K_a ⋡ 0 from campaign 2, R2 H3); its reference admittance Y_a; its participation
      exponent β_a on its lattice, one per contact and read at both ends (R2 C1);
    - the receiving map R.
    Every learned map carries its normal statistics, per locus and factored (`Holon/MomentStorage`).
x   the current: the lift point λ ∈ ℤ^G of the rings' joint clock torus (`aeon::ClockLift`), the one owner of
    every ring's phase class and winding (review C9). Nothing else persists between words.
    The change lives only inside a word (`Word`), starting at zero at the word's open (R2 C2c, C3):
    - the waves a_(g←a) arriving at ring g from contact a, and s_g on ring g's own storage port;
    - the contact states z_a = (u_a displacement, w_a slip rate) ∈ ℚ^(2k_a).
```

[definition] **A ring is a closing rotor by default (§8.5).** Each ring `g` carries:
- one navigator `Ĝ_g`, whose transport is `navigator::Transport::Map`: the cyclic permutation
  `P_g` of its `d_g` nodes, of finite order `d_g`. Its key is its initial configuration, the
  initial ticks of its clock. Its phase lift is the lift point's coordinate `g`. This is the new
  variant `Transport::Map` (review C6): a Cayley image never has eigenvalue −1, so an even period,
  and the half-turn itself, cannot be a flow's Cayley step;
- one screw generator (`geometry::screw::ScrewGenerator`: axis and pitch) with `d_g` node
  placements at declared rational points of its circle, `Vec<RatVec3>`. Node `k` is the
  `geometry::screw::SituatedScrew` of that generator at placement `k` (R2 L1: one `SituatedScrew`
  holds one initial point, so a ring holds `d_g` of them over one generator). Node `k` at winding
  `n` sits at `x_g(k, n)`, node `k`'s placement advanced `n` pitches along the axis: a helix is
  circle plus carry (§8.6, review C5).

The period is combinatorial. A rotation of finite order in the plane is rational only at quarter
turns, so the nodes are declared rational points rather than equal angles, and several nodes may
share a placement (campaign 1 places node `k` at the quarter turn `⌊4k/d_g⌋`, below).

[definition] **Stepping is selective: an input fitting a lock (Decision 2; review B4, B7; R2 H4).**
- **The port chart.** Ring `g`'s ports are its nodes `ℤ/d_g`, so the plugboard's population is the
  ring's width (R2 H4c). A cell `x` meets ring `g` at `port_g(x) = code(x) mod d_g`: the residue
  face (`ratio`) of the cell's exterior code. It is a declared exterior chart, known before any
  key is located (R2 H4g). The ring widths are declared without the alphabet (guard 9).
- **The step.** On each source cell `x`, ring `g` advances `c_g(x) = [port_g(x) ∈ N_g]` ticks,
  plus one carry when its predecessor in the declared carry chain `0 → 1 → … → G−1` wraps (R2 H4i).
  `N_g` is a lock in the constitution. The key is the initial configuration: the ring clocks at
  the opening of an aeon, which for the first aeon is the cut's origin (re-keying at an aeon
  boundary, in campaign 1's data → menu map).
- **Why the key stays locatable.** Ring `g`'s step count before cell `k` of an aeon, counted from
  the aeon's opening, `steps_g(k)`, depends only on the cells, the declared locks and the
  configurations of rings before `g` (through their carries). It never depends on ring `g`'s own
  key or on any plugboard. So
  `compression::keys::ReflectorMachine::position(key_g, steps_g(k))` holds exactly, and the rotor
  gauge of ring `g`'s menu is `Machine.rotorGauge` (R2 §3.4).
- **Unlike Enigma.** Enigma's notch is a rotor position. Here the lock reads the input's port class,
  so a ring whose lock no input fits keeps its configuration: a dormant mode waiting for its
  antecedent. Which input advances which ring is the input-dependent (selective) transition, and it
  is the only way the source reaches the ring phases.

[definition] **Only source rings ingest (R2 M9).** The field declares a source-ring set `𝒮`, and
`E_g ≠ 0` only for `g ∈ 𝒮`. The front's first epoch at the receiving ring `R` is
`e_0 = min_(g∈𝒮) dist(g, R)` in contact hops. The last receiving epoch is `e_last = e_0 + A − 1`
(R3 R1). Every receipt reports the causal diamond's size: the rings `g` with
`dist(𝒮, g) + dist(g, R) ≤ e_last`, refined per locus in the retention section below.

[definition] **Campaign 1 admits no non-closing ring (§8.5; review A3; R2 §2).** `SourceMoment`
accepts closing rings only. A rotation transport has no ingest port, which a `compile_fail`
doctest proves. A rotation ring's moment would be a positional numeral in the Gaussian radix,
measured at about 4.6 bits per 1-bit cell. The first design carried a rotation ring's current to
its grain face at each aeon boundary, which is rounding a state (R2 §2). That rule is withdrawn.
Since the change no longer persists between words (below), a rotation element within a word needs
no such rule. A ring's own element `Cay_r` is such an element: a lossless non-closing rotation,
harmless because its waves are released at the word's end (R2 C2c).

[established-bounded; measured] **A closing ring's moment is lossless below a capacity (R2 H1).**
- **The claim is capacity, not construction.** The moment `M` has fixed slots:
  `Σ_(g∈𝒮) d_g|A|(1 + |Δ||A|)` counts. Its exact bits grow as `O(log n)` per slot, so at small `n`
  it can be injective, a lossless code of its cells.
- **The capacity condition, by counting (R3 H1).** The persisting source state after `n` cells is
  `(M_g, C_g(δ)` on `𝒮`, the window `win`, the lift point `λ)`. Its number of distinct values is
  at most
  ```text
  N(n) = |A|^(max Δ) · ∏_g (2n + d_g) · ∏_(g∈𝒮) [ C(n + d_g|A| − 1, d_g|A| − 1) · ∏_(δ∈Δ) C(n − δ + d_g|A|² − 1, d_g|A|² − 1) ]
  ```
  - `|A|^(max Δ)` counts the window's raw cells (one window, shared by the source rings);
  - `2n + d_g` bounds ring `g`'s lift: it ticks at most `2n` times in `n` cells (its own steps plus
    carries), and a re-keying moves only its phase class;
  - each binomial counts nonnegative integer counts on `S` slots summing to `n` (first-order,
    `S = d_g|A|`) or to `n − δ` (offset, `S = d_g|A|²`).

  `n*` is the least `n` with `N(n) < |A|^n`. Past it the source → state map is not injective on
  `A^n` (pigeonhole), so the moment is lossy by construction. `n log₂|A| − log₂N(n)` is convex and
  nonpositive at 0, so the inequality holds at every `n ≥ n*` once it holds at `n*`.
  `Field::declare` finds `n*` by bisection on exact integers (`N(n) < |A|^n`, no float, no sample)
  and records it in the receipt.
- **Measured** ([`capacity.py`](../../research/notebook/hnn_design/capacity.py), certified at
  `n* − 1` and `n*` by exact integers):
  - three rings of periods 3, 4, 5 over `|A| = 2` (24 slots), every ring a source ring: `n* = 137`;
  - campaign 1's declared field (source ring of period 5, bytes, `Δ = {1}`; 328,960 slots):
    `n* = 6,148` cells;
  - one byte ring of period 7 with `Δ = {1}`: `n* = 8,577`;
  - eight source rings of period 16 over bytes with one offset (8,421,376 slots):
    `n* = 3,641,698 ≈ 3.6 × 10⁶` cells.

  The moment's exact dense code (each slot self-delimited) is a reading, not the capacity. It is
  longer than `log₂N(n)`, so it crosses later: 138 bits at `n = 144` on the control; about
  1.17 × 10⁵ cells for the period-7 ring; and for the eight rings, with uniform counts, below the
  source for good only from 4,243,457 ≈ 4.24 × 10⁶ cells (and briefly from 3.19 × 10⁶ to
  3.67 × 10⁶, since its bit lengths step). The third check's "≈ 4.3 × 10⁶" read this dense code,
  and the second revision's "4.5 × 10⁶" was wrong.
- **The admitted regime is lossy by construction.** `Field::declare` refuses a declared population
  shorter than `n*`. Every receipt reports `log₂N(n)` per source bit against 1, and the moment's
  exact bits per source bit as a reading.
- **Below `n*`.** A moment is reported as below capacity. It holds no more than its own cells, and
  no cell outside them.

#### The law of one passage: a change on a medium (§8.1, §8.2)

[definition] Everything the HNN does is this chain. Between two lines nothing is retained except
what the line names.

```text
ingest   for each source cell k (exterior chart vector x_k), each ring g in carry order:
           τ_g ← τ_g + c_g(x_k) + carry_g                                        selective step (all rings; the lift point)
         and on each source ring g ∈ 𝒮:
           M_g[τ_g mod d_g] += x_k                                                phase-binned counts
           C_g(δ)[τ_g mod d_g] += x_k ⊗ win_g[δ] ,  δ ∈ Δ                           offset counts on the exterior chart
           win_g ← shift(win_g, x_k)                                                  the window: the last max Δ cells, overwritten
         m̃_g = Σ_c P_g^(−c) I_g (E_g M_g[c] + Σ_δ E_g^(δ) C_g(δ)[c])             the source moment, never stored
open     the medium (Θ, λ) at this cut; every wave and contact state is zero; s_g(0) = P_g^(τ_g) m̃_g on g ∈ 𝒮
tick     one contact hop per tick, t = 0, 1, …, e_max − 1 (the last stops after its junction), every operand fixed at the cut:
  junction  at each ring r, from its arrived waves a_(r←a) and its storage wave s_r:
              G_a  = κ_a Y_a ,  κ_a = 2^(s_a) ,  s_a = −β_a Q_a / 2 = n_a + φ_a/L        one exponent per contact (§8.4; R2 C1)
              Q_a  = |x_g(λ_g) − x_h(λ_h)|²  for a = (g→h)                             the pair quadrance of the two rings' screws
              v_r  = (Y_r s_r + Σ_a G_a a_(r←a)) / (Y_r + Σ_a G_a)                     participation is the Swing's anchor
              o_(r→a) = 2 v_r − a_(r←a)                                                the junction Swing
              (I − ½K_r) s_r′ = (I + ½K_r) b_r + W_c,r c_r ,  b_r = 2 v_r − s_r ,  c_r = v_r − s_r     the ring's element:
                    K_r = W_s,r + Σ_ρ σ_ρ,r A_ρ,r ,  so s_r′ = Cay_r b_r + (I − ½K_r)⁻¹ W_c,r c_r        the contrast port drives
                    inside the midpoint (Holon/Cayley.drive_balance; R3 C1)
  transit   on each contact a = (g→h), from o_(g→a) and o_(h→a) (the contact's midpoint two-port, below):
              α_g = ι_(a,g)ᵀ o_(g→a) ,  α_h = ι_(a,h)ᵀ o_(h→a)                          what enters the channel
              M_a ω_a = 2C_a w_a + h(α_g − α_h) − h K_a u_a ,
                    M_a = 2C_a + (2h/G_a) I + h D_a + (h²/2) K_a                        one k_a-sized local solve
              w_a ← 2ω_a − w_a ,  u_a ← u_a + h ω_a
              a_(g←a) ← o_(g→a) + ι_(a,g)(−(2/G_a) ω_a) ,  a_(h←a) ← o_(h→a) + ι_(a,h)((2/G_a) ω_a)
                    off the channel each wave reflects straight back to its own ring
receive  at the receiving ring's epochs e_j = e_0 + j, j < A, each read by tick e_j's junction; the last is
         e_last = e_0 + A − 1, so the word evaluates e_max = e_0 + A junction steps (R3 R1):
           f_j = R[P_R^(τ_R) v_R(e_j)] ,  read at the receiver's grain L_R as the face p̂_j with its fibre ε_R
release  at the word's end every wave and contact state is released: the unread change leaves as the
         word's emitted exchange, with its power in the receipt; nothing is carried to the next word
compare  |T⟩ is read through the same E and Ĝ ;  R_j = Ĝ_(T←H) at phase j ;  ℓ_j = log R_j , the winding its branch
return   R⁻¹dR at the face → the ticks in reverse, over the word's own per-tick waves → the open → the moment
         → E, R, Θ_a, the reaction material, q; the key covector as a reading
deposit  only at loci inside the causal diamond of the source rings and the receiver (retention, below), each
         update Δ exact at the lattice-valued operands (Decision 22):
           ΔH_U = Σ_t w f_t f_t* ,  ΔW_U = γ_U Σ_t w g_t (H_U'⁻¹ f_t)* ,  H_U' the carried successor Gram   per linear locus
                 (E_g, R, W_c), summed over the ticks t at which U's output is read within the word (R3 R3);
                 B_U = W_U H_U is not carried: the prox step needs only W_U, H_U' and the covector (normal_prox_step)
           Δh_x = Σ_t w|f_t|² (h_x from 1) ,  Δx = η_x G_x / h_x'                 per factor family x: c_a, b_a, F_a, the
                 slices' u, v, W_s's factor, E_g^(δ)'s factors, q_r; G_x its covector; no clamp: C_a, K_a, D_a, −W_s stay PSD as squares
           every entry of locus ℓ on its declared lattice 2^(−L_ℓ)ℤ, at the locus's m-th deposit (Decision 22):
                 Δ + r_prev = y_f + e at the nearest point of 2^(−L_ℓ−k_m)ℤ,  k_m = 2⌊log₂ m⌋ + 1;
                 y_f = q·2^(−L_ℓ) + r at the nearest lattice point, ties upward;
                 q·2^(−L_ℓ) applied,  r ∈ [−2^(−L_ℓ−1), 2^(−L_ℓ−1)) carried,  e released and reported in the receipt
           q_r moves only here (R2 C3)
close    at an aeon boundary: the collapse onto what the admitted future distinguishes (below); it releases
         only exact complements, so no remainder of a retained locus
```

[definition] The declarations the chain reads (R2 M8, M14, L2):
- **Tick length and admittances.** `h` is the hop's duration in the contacts' units: `h = 1` in
  campaign 1. `Y_g` is ring `g`'s storage-port admittance, `2/h` for the parametron's unit
  storage. `Y_a` is contact `a`'s reference admittance, a declared positive rational: the matched
  value `2c²/h` when `C_a = c²I`. Any positive `Y_a` keeps the tick lossless, and the matched
  value makes the storage reflection-free.
- **Sheet classes (R3 C3 gaps).** The standing contrast of ring `r` is
  `Δ_r = Σ_(a∋r) U_(r←a) q_(a's other end) − q_r ∈ ℚ^(2d_r)`, with `U_(r←a) = U_a` when `a = (g→r)`
  and `U_aᵀ` when `a = (r→h)`: `q` lives on rings. Ring `r` has `2d_r` slices, one per realified
  coordinate, and `σ_ρ,r = sign(Δ_r[ρ]) ∈ {−1, +1}` is the half-turn sheet reading of coordinate
  `ρ`, with the declared tie rule `sign(0) = +1` (the half-open sheet). It is a lock class, not a
  magnitude, read from the constitution's `q`, so it is fixed within a word. `q_g` starts at 0, so
  every class starts at `+1`, and a deposit that carries `Δ_r[ρ]` below zero flips it.
- **Steps and weights.** They are local declarations with named sources, never one global gate
  (first review C10):
  - `w = 1` per compare return: each observed target counts once;
  - `γ_U` is linear locus `U`'s proxy step and `η_x` factor family `x`'s step. Each is a declared
    rational, part of `Field::describe`, not learned in campaign 1 and reported with its value.
  - Campaign 1 declares `γ_U = 1`: the normal law's pure solve. Under the exact law its bits stay
    slow only for a map that is not an operand of its own covector (`R`: 155 → 196 bits over 8 →
    256 deposits). They grow linearly in deposits for `E` (612 → 14,852 over 8 → 128), and for
    every map that forms its own covector (retention, below). On the carrier lattice (Decision 22)
    the word reads only lattice values, and the updates' denominators stay in the carried
    remainders until the aeon collapse releases them.
  - A factor step is preconditioned by its family's scalar statistic `h_x = 1 + Σ_t w|f_t|²`, over
    the family's own features at the ticks inside its diamond window. [agent-inferred: the moment's
    counts, and so every feature, grow with `n`; an unpreconditioned step would grow with them,
    while the normal law is already scale-covariant.] Campaign 1 declares `η_x = 1/2`.
- **The target Holon for a byte (R3 D3).** `R` maps the receiving ring's `2d_R` realified
  coordinates to complex logits over the `|A|` exterior classes, realified as `2|A|` rationals:
  `Re f` is read at the grain as the face, and `φ^H = Im f / 2` is each class's phase in turns
  (`Objects/RatioPhase.phaseGap`). The target at receiving phase `j` is the one-hot face `q_j` of the
  byte `t_j` in the same exterior chart that `E` reads, so its magnitude part is `p̃_j − q_j` (the
  odometer chart, "Exact charts"). Its phase is the receiving ring's clock read through the same
  `Ĝ_R`, **in the cut's frame**: `φ^T_(t_j) = (τ_R(j) − d_R w)/d_R` turns, where `τ_R(j)` is `λ_R`
  advanced by selective stepping over `t_0 … t_j` (with carries, as `ingest` would, without
  ingesting) and `w = ⌊λ_R/d_R⌋` is the cut's winding. `w` is the branch of the log
  (`Im ℓ = w + Δ`), never a magnitude descended on: the produced side reads only a phase class
  through `P_R^(τ_R)` and can represent no stream winding, and measuring from the stream's start made
  the gap grow without bound (review C1: `τ_R/d_R` reached 521 turns over 40,000 cells, and the phase
  covector about 34 against magnitude entries of at most 1). In the cut's frame `φ^T_j ∈ [0, 1 +
  2(j+1)/d_R)`. Only the target's class carries phase weight (`q_c = 0` elsewhere), so the phase part
  is `−q_(t_j) Δ_(t_j)` with the windowed gap `Δ = φ^T − φ^H` (`alignCost`, Lean
  `HNN/Ratio.alignCost_turns`).
- **Notation.** `o` is a wave leaving a junction, `a` a wave arriving at one, and `z_a = (u_a, w_a)`
  a contact's state. `k_a` is a contact's channel width. `c_a`, `b_a` and `F_a` are the square
  factors of `C_a`, `K_a` and `D_a`. `φ_a ∈ ℤ/L` is the phase class of a contact's exponent. `ε_R` is a receiver's fibre, and `ε_k` a deposit's energy-growth bound
  (`CommittedEnergyBound`). Rings are `g, h, r`, and contacts are `a`.
- **The window and the pair port.** `win_g` is a shift register of the last `max Δ` exterior cells,
  overwritten cyclically: a bounded window of raw cells, counted in the moment's bits, with an
  overwrite law distinct from the accumulate law (R2 M7).
  - `E_g^(δ)` is the learned pair port on the exterior pair chart, carried factored. It is how the
    offset counts enter the open.
  - Campaign 1 declares `Δ = {1}`. Campaign 3 derives `Δ` from the receivers.
  - The kinded directed ports `c_p` are not in campaign 1: `C_g(δ)` already carries the ordered
    pairs. Their Lean law moves in campaign 1 (retirements below), and they enter with
    campaign 5's declared actions.

[definition] How to read the chain:
- **The light is the change (§8.1, §8.2).** The standing `(Θ, λ)` is the medium: the bound part
  that goes dark and conducts. `q` is part of `Θ`. The medium fixes every operand of a tick:
  - `Q` and so `κ` come from the rings' phases at the cut;
  - `Y` comes from the declared admittances;
  - `K_r` comes from the sheet classes of the standing contrast.

  The medium changes only by deposition and, at an aeon boundary, by the collapse (Decision 1). A
  word neither absorbs the change into `q` nor carries it forward: it starts at zero change and
  releases what is unread at its end. Within a word those operands are fixed, so each tick is an
  exact linear map of the change: the medium's Green's function. The medium decides, not the
  source (light record §2). What moves and what is read is the propagated difference.
- **Ring phases are held within a word (R2 M6).**
  - The lift point `λ` advances only at ingest, and is re-configured only by re-keying at an aeon
    boundary (campaign 1's data → menu map). A word reads it at the cut and does not change it.
  - The word's ticks are hops of the word's own clock, a `navigator::Clock`, and the response
    position `j` is the epoch `e_j`.
  - So `Q`, `κ`, `P_R^(τ_R)` and the sheet classes are one class configuration per word, and the
    word is `T_c^(e_max)`: linear and time-invariant within the word.
  - Phases advancing inside a word enter in campaign 2. There each change of a port's reference
    admittance between ticks is applied as the mismatched two-port junction with reflection
    `Γ = (G_old − G_new)/(G_old + G_new)`, `T + Γ² = 1` (atlas `wave.junction-reflection`), which
    keeps the power exact.
- **The nonlinearity lives in finitely many key and lock classes (Decision 2).** The machine is
  nonlinear only through what the medium reads by class:
  - the rings' phase classes, set by selective stepping from the located keys;
  - the lock classes: the notches and the sheet classes of the standing contrasts;
  - the receiver's grain.

  Each is a finite class set, and within one class configuration the word is linear in the moment
  `m̃`. The machine is a switched linear map over a family of exact operators `{T_c}`.
  - **Finite where.** `Q_a` reads the rings' windings as well as their phases. The family is
    therefore finite within an aeon, where the carry chain bounds the windings (ring `g` winds fewer
    than `∏_(h>g) d_h` times per aeon). Across aeons it is finite only when the screws' pitch is
    zero, which campaign 1 declares (its declared values); with a pitch it grows with the relative
    windings (R3 R4).
  - That is why `compression::FaceMap` applies exactly at the aeon boundary (review C3), and why bit
    length grows additively in ticks.
  - [agent-inferred] The capability consequence, stated once: given the classes, the response is
    linear in the moment, and participation is not learned in campaign 1. Every nonlinearity is a
    key or a lock (Decision 2). Brandon may override this.
  - [agent-inferred; measured] Reading `K_r` from the evolving state compounds bit length about
    `(n+1)`-fold per tick: 46 → 804,289 bits in 7 ticks at 4 real dimensions. Reading it from the
    sheet class grows additively: 44, 85, 127, 209, 374, 705 bits at ticks 1, 2, 4, 8, 16, 32. On
    the revised six-ring tick ([`word_bits.py`](../../research/notebook/hnn_design/word_bits.py))
    one word peaks at 77, 482, 1,461, 3,512 and 7,623 bits at 2, 4, 8, 16 and 32 ticks: additive,
    about 240 bits per tick, set by the operands' denominators.
- **The causal cone (§8.1, review A1).**
  - A change at ring `g` after `t` ticks is supported, exactly, in the ball of radius `t` contact
    hops about `g`.
  - Its speed is one contact per tick of the junctions' clock.
  - A receiver at hop distance `r` first reads the change at its `r`-th epoch. Two receivers locate a
    source by their epoch difference (light record §7).
  - [measured] An impulse at ring 1 of a six-ring cycle reaches rings {0, 2}, then {0, 1, 2, 3, 5},
    then all six.
  - No global solve exists, and so "deposit only where the covector reached" is meaningful. The
    covector also moves one contact per reverse tick. The reached loci are the causal diamond
    between the source rings and the receiving ring, and every other locus keeps its statistic
    exactly.
- **The connection heat equation is the continuum limit only (§8.1).**
  - On a refined contact lattice the junction Swing with transit is a finite-speed (telegraph)
    law.
  - Its overdamped limit, dissipation dominating storage, is the parabolic connection heat
    equation `∂_t q = −d_A* ρ² d_A q`. Its backward-Euler step is the earlier design's global
    `(I + d_A* ρ² d_A)` solve, with its immediate tails (atlas `heat.telegraph-relaxation`).
  - That limit is a reading, never the machine's step.
- **The word's clock is its own hop clock (review A4, A5; R2 M6).**
  - In campaign 1 every junction ticks once per hop, a declared synchronous specialization.
    Multi-rate rings, several ring ticks per hop at the Kac ratio, enter in campaign 2 with an
    `aeon::EpochTower`.
  - The word's length is not chosen. It runs from the open to the receiving ring's last receiving
    epoch `e_last = e_0 + A − 1`: `e_max = e_0 + A` junction steps, the front's hop distance plus
    the aperture.
  - The word acts once per receiving window, on the accumulated moment, never between source cells
    (retention audit).
  - Each ring's tick count is in the receipt.
- **Participation is the Swing's anchor, with one exponent per contact (R2 C1).** The junction
  potential `v_r` is the `G`-weighted mean of the ring's arrivals, its own storage port included.
  - Its weights `G_a / (Y_r + Σ_a G_a)` are ring `r`'s normalized participation, the ring's face of
    its neighbours. They stay ring-relative through the normalization.
  - `G_a = κ_a Y_a` is the contact's port conductance at both ends. The first design put the
    exponent on the ring (`β_r`), so a wave's weight changed in transit and the global power was
    not conserved: measured 38.1 → 51.0 → 43.5
    (R2 [`swing_power.py`](../../research/notebook/hnn_design/swing_power.py), re-run). With one
    exponent per contact it is exactly 28.147 at every tick.
  - `o = 2v − a` is the point Swing about that anchor (objects §3): the reflection `2P_D − I` onto
    the junction's common-potential subspace, with `P_D` the `W`-orthogonal projector,
    `W = diag(Y_r, G_a)`.
  - It is an involution and a `W`-isometry. It is the wave-digital parallel adaptor. Its two-port
    case is atlas `wave.two-port-junction` (`a e² + b h′² = a i² + b h²`), and its reflection face
    is `wave.junction-reflection` (`Γ = (R − M)/(R + M)`, `T + Γ² = 1`).
- **The tick's global power balance (R2 C1; R3 C1).** With
  `P = (h/4)[Σ_r Y_r|s_r|² + Σ_(r,a) G_a|a_(r←a)|²] + Σ_a E_a`, where
  `E_a = ½w_a*C_a w_a + ½u_a*K_a u_a`:
  - the junction contributes zero;
  - the element's midpoint solve gives, with `x̄_r = ½(b_r + s_r′)` (`Holon/Cayley.drive_balance`),
    `½|s_r′|² − ½|b_r|² = ⟨x̄_r, W_s,r x̄_r⟩ + ⟨x̄_r, W_c,r c_r⟩`; the skew slices contribute zero;
  - the untransmitted part of each wave reflects with its norm;
  - the contact's midpoint step gives `E_a′ − E_a + h ω_a*D_a ω_a = (hG_a/4)(|α|² − |α_out|²)`.

  So, exactly,
  ```text
  P(t+1) = P(t) − h Σ_a ω_a*D_a ω_a + (h/2) Σ_r Y_r ⟨x̄_r, W_s,r x̄_r⟩ + Π_c ,   Π_c = (h/2) Σ_r Y_r ⟨x̄_r, W_c,r c_r⟩
  ```
  - The first two terms are `≤ 0` (`D_a ⪰ 0`, `W_s` passive).
  - `Π_c` is the power the learned contrast ports supply, and it has no sign. For fixed `c_r`,
    `x̄_r = (I − ½K_r)⁻¹(b_r + ½W_c,r c_r)` ranges over the whole space as `b_r` does (the Swing
    makes `b_r` and `c_r` independent), so `⟨x̄_r, W_c,r c_r⟩` takes both signs unless
    `W_c,r c_r = 0`. The element is passive for every input exactly when `W_c,r = 0`.
  - So the contrast port is an active element relation with its power (objects: the constitution
    includes active and learned relations). Passivity of the word is claimed only where every
    `W_c = 0` and every `K_a ⪰ 0`. Elsewhere `Π_c` is stated per tick in the receipt, and what it
    supplies is part of the change, released at the word's end. A word with fixed operands is one
    linear map, so its growth stays additive in bits.
  - [established-bounded; measured] [`power.py`](../../research/notebook/hnn_design/power.py)
    checks this on six rings of widths 4, 2, 4, 6, 2, 4 (so `U_a` is a proper partial isometry),
    the six-cycle plus a chord, with contacts that have storage and stiffness:
    - lossless: `P` constant exactly over 8 ticks;
    - dissipative: `P(t) − P(t+1)` equals the dissipation exactly at every tick;
    - `W_c ≠ 0` with lossless contacts: `P(t+1) − P(t) = Π_c` exactly at every tick;
    - dissipation, passive `W_s` and `W_c ≠ 0` together: the balance above holds exactly at every
      tick, the `W_s` term is `≤ 0`, and `Π_c` takes both signs over 8 starting states;
    - with `W_c`'s entries 8 times larger the balance is still exact, and `P` grows 245-fold in 8
      ticks: an active word.
- **The score is the pair quadrance of the two rings' screws (§8.6, review C5).**
  - `holon::contact::PairContact::of(ScrewPair)` supplies `Q`, `J = [v_g | −v_h]`, `DQ = 2J*Δ` and
    `D²Q`, at the two rings' phases. Ring `g`'s point at phase `τ` is
    `x_g(τ) = x_g(τ mod d_g, ⌊τ/d_g⌋)`: the node at its phase, advanced by its winding.
  - A locked pair, with a Farey address and bounded relative winding, keeps participating.
  - An unlocked pair drifts apart along its axes: its carry `n_a` grows, and its weight is shifted
    out by `2^(n_a)`.
  - The current-space `|u − q|²` is the zero-advance, unit-radius collapse
    (`HelicalPairInteraction.bilinear_score_eq_polarized_quadrance`). It is kept as a specialization
    test.
- **The contact carries its own constitution (§8.6; R2 M8).** Its transit is the midpoint (Cayley)
  step of its own series two-port on the channel.
  - **The law.** State `z_a = (u_a, w_a)` (displacement, slip rate); `u̇ = w`;
    `C_a ẇ = e_g − e_h − K_a u − D_a w`; the port flows are `w` into the contact at `g` and `−w`
    at `h`.
  - **In waves** at reference admittance `G_a` at both ends, it is the chain's
    `M_a ω_a = …` solve.
  - **Its limits.** With `C_a = K_a = D_a = 0` it is pure transmission: the wave from `g` arrives
    at `h` through `U_a` and the wave from `h` at `g` through `U_aᵀ`. Its reflection back to `g` is
    the channel's `−(2/G_a)ω_a` term, plus the untransmitted part off the channel.
  - **Well defined.** `M_a ≻ 0` whenever `C_a, D_a, K_a ⪰ 0` and `G_a > 0`, so campaign 1's
    squared carriers make every forward transit well defined with no refusal (R2 H3).
  - **Boosts.** A boost `K_a ⋡ 0` (campaign 2) can make `M_a` singular. Declaration and deposit then
    refuse the operand, returning its singular direction. The energy `E_a` is indefinite, and its
    balance is stated with the indefinite storage.
  - Its one-tick transfer has a trace and a determinant, so it has a site kind
    (`navigator::trace::SiteFactor::kind`; egg record §4; light record §5):
    - rotation where `K_a > 0`: the joint returns; an elliptic Möbius flow, a vortex pair;
    - null at `K_a = 0`: the fold and the neck; a parabolic doublet;
    - boost where `K_a < 0`, from campaign 2: the joint breaks and the flux escapes; a hyperbolic
      source–sink pair. Its expanding part grows at most `ρ^(e_max)` within one word and is
      released at the word's end with the rest of the change, so no expanding mode is ever
      carried (R2 H3);
    - reflection at negative determinant: the Swing.
  - The computational stress lives in the contacts. One scalar conductance per contact is retired
    (review B6).
- **Reception is composed (§8.2, review C4).** A tick does not fit one `JointLaw::interact`.
  1. The ring's element step and the contact transit are midpoint steps of linear port-Hamiltonian
     laws at the frozen operands, and the tick realizes the midpoint scheme directly
     (`hnn::propagation::{element_step, transit}`). Two tests in `hnn/tests/propagation.rs` equate
     each with `holon::law::ReferenceHolon`'s midpoint advance (Lean `Holon/Law.advance_law`) at the
     same operands:
     - `the_element_step_is_the_reference_holons_midpoint_advance`: the element step is the advance
       of `ẋ = (Ω − R)x + W_c c` with `Q = I`, `h = 1`, `Ω = Σ_ρ σ_ρ A_ρ` and `R = −W_s`. It reaches
       the same storage, with dissipation `−⟨x̄, W_s x̄⟩` and port power `⟨x̄, W_c c⟩`;
     - `a_stored_transit_is_the_reference_holons_midpoint_advance`: whenever `C_a ≻ 0`, the transit
       is the advance on `(u, p = C_a w)` with storage `(K_a, C_a⁻¹)`, resistance `D_a + (2/G_a)I` and
       the channel waves as sources. It reaches the same displacement and rate, its port flow is
       `ω_a`, and its dissipation is `h ω_a*D_a ω_a + (2h/G_a)|ω_a|²`.

     [agent-inferred] The step stays hand-written, for two reasons. A singular `C_a` (campaign 1
     admits `c_a = 0`, pure transmission) makes the transit a descriptor midpoint step with mass
     `C_a`, which the owner's unit-mass step `q⁺ − q = h((J − R)Q q̄ + B u)` does not state. And a
     word's operands are fixed at its cut, so the tick charts each solved map (`Cay_r`,
     `(I − ½K_r)⁻¹W_c`, `M_a⁻¹`) once per cut and the return reads their transposes, where calling
     the owner per tick would re-solve its whole Dirac system at every step. The tick's balances are
     its own `TickBalance`s, carried in the receipt (item 4).
  2. The junction Swing has eigenvalue −1, so it is no midpoint step of any skew flow. It is the
     point Swing about the anchor, composed between the two. Its isometry is its own law
     (`junctionSwing_isometry`).
  3. The receiving read at epoch `e_j` is `ReceiverFace::read` with `C_S = R P_R^(τ_R) Π_R` on the
     anchor `v_R`. It is the zero-storage `JointLaw::reading` in campaigns 1–4, and a participating
     receiver with its own storage, through `JointLaw::interact`, in campaign 5.
  4. The tick's balance is the sum of the element and transit balances, plus the Swing's zero, over
     the global power `P` above (`word_tick_balance`), read as `hnn::propagation::TickBalance`
     (`P` before and after, the dissipation, the `W_s` term and `Π_c`). There is no chart-square
     test against `Field::holon()`.
- **The return holds no tape, and claims no inverse it does not have (review C11; R2 H2).**
  - **What is proved.** `Holon/Cayley.cayley_bijective` proves only that `I − ½K` is bijective for
    passive `K` (`⟨v, Kv⟩ ≤ 0`). That makes the element step well defined. It does not make the step
    `(I − ½K)⁻¹(I + ½K)` invertible, which fails when `I + ½K` is singular.
  - **What else can fail.** The transit's reverse needs `2C_a + hD_a − (2h/G_a)I − (h²/2)K_a`
    invertible. All these operands are learned.
  - **So the return does not invert.** The `Word` keeps its own per-tick waves, or checkpoints every
    `⌈√e_max⌉` ticks and recomputes forward from them, and the adjoints compose in reverse order
    over them (`HolonicAdjointNormalization.dualMap_comp_reverse_order`).
  - **This is lawful.** The memory is bounded by the word's length, `O(e_max · state)` or
    `O(√e_max · state)`, and it lives only in the `Word`, which its return consumes (guard 2). It is
    not an occurrence tape: one word is one evaluation on one moment.
- **The pending read (review C2; R2 C3).** A `PendingRatio` holds:
  - the producing anchor, the lift point `λ` at the cut;
  - the encoder moment `M_g`, never `m̃`: a copy of the counts at the cut, counted in the state
    bits, since a `MomentId` would read a moment that later ingests extend (R3 §4);
  - its `ReceivingPhases`;
  - the commit it was produced at.

  Every word opens at zero change, so the anchor needs no waves. `compare` recomputes
  `m̃ = ⟨M_g, E_now⟩` and runs the word at the contemporary constitution, `q` included.
  - `refine` publishes only faces; there is no `commit` flag. So no source is counted twice, and
    `E` is never mixed across two cuts.
  - With no intervening deposit, a delayed read equals the immediate one exactly. After a deposit,
    it returns the residual against the emitted face.
  - The producing anchor is a clock reading, not material. The retention audit sanctions it as a
    producing operand, and it is no frozen cut of earlier material.
- **The standing moves only by deposition (Decision 1; R2 C3).**
  - **How the word reads `q`.** Only through the sheet classes `σ_ρ,r = sign(Δ_r)_ρ`. The word is
    locally constant in `q`, so its derivative there is zero almost everywhere.
  - **The declared chart.** The standing's covector is the lock's derivative at its locked value:
    - the slice covector `g_σρ = Σ_t Re⟨u_t, A_ρ x̄_t⟩`, the derivative with respect to `σ_ρ` read
      as the lock coefficient at `±1`;
    - carried to `q` by the transpose of the contrast map `q ↦ Δ`;
    - [agent-inferred] the same declared straight-through chart as the face covector (the exact
      charts below, R2 M2).
  - **The step.** `q_r ← q_r + η_q G_(q_r)/h_(q_r)`, the preconditioned factor step of the
    declarations, with `h_(q_r) = 1 + Σ_t |x̄_t|²` over ring `r`'s element midpoints, inside the
    causal diamond only.
  - **Class changes.** A sheet class changes only when a deposit carries `Δ_ρ` across zero: a fold
    (light record §5).
  - **Nothing else writes `q`.** No word absorbs its change into `q`.

#### Retention: the collapse onto what the admitted future distinguishes (§8.3)

[definition] **What persists, and where each thing is released (Decision 1; R2 C2, C3).** Between
words only the medium `(Θ, λ)`, the open moments `M` and the pending ratios persist. Retention acts
twice:
- **At every word's end, the change is released.** The unread waves and contact states leave as
  the word's emitted exchange, with their power in the receipt. This is §8.3's "the stable
  remainder is released, not rounded", applied to the change. Nothing is rounded, and nothing of
  the change is carried. It is what bounds the change's bits: one word's growth, additive in its
  `e_max` ticks.
- **At an aeon boundary, the constitution is reduced** to what the admitted future still
  distinguishes (objects §8: the constitution suffices but is not minimal).

[definition] **The collapse at an aeon boundary.** Campaign 1 admits learning aeons only: every
aeon admits deposits (R3 R4).
1. **The admitted future,** declared at the boundary as the admitted `ReceivingPhases` (from
   campaign 3 also the cycle receivers of dormant rings), is:
   - read at their epochs after every admitted word, the last at most `e_last`, at every lift point
     and class configuration of the next aeon;
   - on every change the source ports can inject;
   - under every deposit the next aeon admits.
   - **Non-increasing (R3 R3).** The collapse is sufficient for every later aeon only if every later
     admitted family is contained in this one, since a released locus cannot return. `close_aeon`
     therefore refuses an admitted family not contained in the previous boundary's, naming the
     receivers it would add. The family may shrink.
2. **What may be released is exactly what no admitted future receiver distinguishes (R2 C2f):** the
   constitution used only on changes that no admitted reading sees within the word. Every admitted
   reading is therefore identical before and after, exactly. That is the collapse's test, and it
   holds by construction.
   - The recursions of item 3 run on the loci's sparsity, which no deposit changes. The release is
     therefore invariant under every admitted deposit, and a released locus cannot be resurrected
     by a later one (`release_structural`).
   - The value kernel of the current constitution, beyond the structural release, is reported as a
     reading and not released. A frozen aeon would release it, but its descended blocks no longer
     have the junction, Cayley or two-port form, so nothing says how its next word ticks. It moves
     to campaign 3, which must first specify that tick (R3 R4).
3. **The time-indexed causal diamond (R3 R1, R2).**
   - **Blocks and edges.** A block is ring `g`'s `2d_g` realified storage plus the waves it
     receives (every `a_(r←a)` belongs to ring `r`'s block), or contact `a`'s own `2k_a` state. One
     tick maps block `x` to block `y` along the edges `g → g`, `g → h`, and `g, h ↔ a` for each
     contact `a = (g, h)`.
   - **The two recursions**, one neighbour exchange per round, `e_last` rounds:
     - reach: `r_g = 0` on `𝒮`, and `r_h ← min(r_h, r_g + 1)`, so `r_g = dist(𝒮, g)`;
     - observe: `o_g = 0` at the admitted receiving rings, and `o_g ← min(o_g, o_h + 1)`, so
       `o_g = dist(g, R)`.
   - **The rule.** An edge `x → y` is used on a change that some admitted reading sees exactly when
     `r_x + 1 + o_y ≤ e_last`. So, per locus:

     | Locus | Retained exactly when |
     |---|---|
     | ring `g`'s element (`W_s`, slices, `W_c`; edge `g → g`) | `r_g + 1 + o_g ≤ e_last` |
     | ring `g`'s junction (`Y_g`; edges `g → g`, `g → h`) | `r_g + o_g ≤ e_last`, and always at `R` |
     | contact `a = (g, h)`'s channel (`c_a`, `b_a`, `F_a`, `ι`) | `min(r_g, r_h) + 1 + min(o_g, o_h) ≤ e_last` |
     | contact `a`'s conductance `G_a` (`Y_a`, `β_a`, the pair geometry) | its channel or either end's junction is retained |
     | source ports `E_g`, `E_g^(δ)`, `I_g` on `g ∈ 𝒮` | `o_g ≤ e_last` |
     | the standing `q_g` | the element of `g` or of a neighbour is retained (`q_g` enters their contrasts) |
     | the receiving map `R` | always |

   - **This is exactly the diamond.** A block reached at `t = r_x` is retained exactly when it is not
     in `FaceMap.horizonBlind(e_last − t)`, on the loci's sparsity. The second revision ran the
     blind recursion to its fixed point and paired it with a cumulative reach. That separable form
     keeps whatever is reached at some time and read at some later time, even when the two do not
     fit in `e_last`: it is lawful, but finer.
   - **What replaces a released locus.** A released element becomes the zero map, and a released
     ring the matched termination (zero return) of its retained neighbours' channels. No
     replacement is ever read.
   - **Structural rank (case b)** is the same recursion run on coordinates instead of blocks, where a
     declared port matching or source-port image leaves directions uncoupled. Every campaign 1
     element is dense on its ring and every matching covers the smaller ring, so campaign 1's
     structural release is whole loci.
   - **A source ring past the diamond** (`o_g > e_last`) also drops its `M_g` and `C_g(δ)` and stops
     counting, while its clock keeps stepping in `λ`. `n*` is recomputed on the remaining source
     rings and reported.

   [established-bounded; measured] [`release.py`](../../research/notebook/hnn_design/release.py)
   runs the two recursions on a path of six rings, with source ring 0 and receiving ring 2
   (`e_0 = 2`, `A = 2`, `e_last = 3`, `e_max = 4`):
   - Retained: the elements and junctions of rings 0–2, and the channels (0,1), (1,2) and (2,3).
     Channel (2,3) is kept because its reflection back to ring 2 is read at epoch 3.
   - Released: 72 of 156 constitution entries (each element's `n_g²`, each channel's `3k_a²`). The
     separable form releases 44.
   - Replacing every released item with arbitrary values leaves every admitted reading identical,
     exactly, over 20 injections.
   - Replacing any one retained item alone changes some reading, 12 of 12, so the rule is tight.
   - The rim case, `A = 1` (`e_last = 2`): every element is released (`r + 1 + o = 3`), the junctions
     of rings 0–2 are kept, and channel (2,3) is released while its conductance is kept, because
     junction 2's weights read it. That releases 132 of 156 entries, with identical readings and 8 of
     8 retained items tight.
4. **When the release is nonempty.** It is nonempty exactly when the admitted family does not reach
   and read the whole field in time:
   - **past the diamond:** founded rings (campaign 3) or declared capacity beyond it, or a shrinking
     admitted family, since a retired receiver's diamond goes with it;
   - **on its rim,** where an element is released while its junction is kept;
   - **the empty case:** a field inside one diamond, where the collapse is the identity quotient.
     The boundary then carries the moments and pending ratios, re-keys, reports the first-law split
     and reduces nothing. Campaign 1's declared field is such a field (its declared values), so on
     the real cut the state bits with and without the collapse are equal, and the collapse is
     exercised by its synthetic tests.
5. **What is not released (R2 C2b, C2d).** A decaying (stable) mode that an admitted receiver reads
   at a nonzero value within an admitted word is distinguished, so it stays.
   - **The first design's rule.** It released "the stable part certified extinct at tolerance"
     through `receiver::standing::extinction`. But a driven stable part is `O(1)`, not extinct: the
     certificate refused it at 32 of 32 boundaries, reaching 1,831 bits, the no-collapse curve.
   - **Its certificate.** `ContractionCertificate` accepts `λ = 1` and certifies a coordinate chart,
     not a spectral subspace.
   - **Neither is used by the collapse.** Center-manifold slaving (light record §6) is the
     long-time-receiver limit of this rule. With finite admitted words it is a reading.
6. **Per ring, so the collapsed field keeps its contact graph (R2 M3, M4).**
   - **Specification only.** `compression::FaceMap::new(NavigatorFamily{T_c}, receivers)` states the
     retention. Its `NAVIGATOR_CEILING = 32` and `EXTENT_CEILING = 256` refuse any real field, so it
     is not the realization.
   - **The realization** is item 3's two recursions: local, one neighbour exchange per round,
     `e_last` rounds.
   - **The result.** `V = ⊕V_g` deletes whole loci: a 0/1 projection, block-diagonal, inside the
     global quotient. That is lawful (`standingLaw_exists_iff_future_factors`), and possibly finer
     than the global quotient. [agent-inferred: a global quotient would make the descended
     operators dense and break locality (§8.1).]
7. **What descends.**
   - Every retained operator keeps its law (junction, Cayley element, two-port) and its exact
     values; the released ones are gone. Every receiver factors, `ρ = ρ̄ V`. No denominator is
     introduced.
   - `E_g` and the moment `M_g` are unchanged on the retained source rings, and `M_g` stays integer
     counts (R2 M5). Only campaign 3's moment quotient `V_m` acts on `M`.
   - A retained locus keeps its own normal statistics unchanged.
   - A relation that does not descend returns its separating direction and stays unreduced (item 4
     of the retention audit).
8. **A deposit gives the same result with or without the collapse (R3 R3; `deposit_descends`).** A
   retained locus's deposit reads a feature and a covector at each tick of its diamond window: the
   ticks at which its output is read within the word.
   - Suppose such a feature or covector depended on a released edge `u → w`. There would be a path
     from a source ring through `u → w` to the locus, and on to the receiver by `e_last`. That
     gives `r_u + 1 + o_w ≤ e_last`, so `u → w` is retained, a contradiction.
   - A released locus receives no covector, so its deposit is zero.
   - So `collapse ∘ deposit = deposit ∘ collapse` on the admitted family. This is why the chain's
     normal statistics sum only over the diamond window: a feature at a tick whose output no reading
     sees could have passed through released loci.
   - On the carrier lattice the carried deposit leaves an empty window's locus, value and remainder,
     unchanged (the upward tie rule keeps a remainder alone in its cell), so the descent holds
     verbatim (`HNN/LatticeDeposit.lattice_deposit_descends`), and with the release of the
     remainders at the boundary (`aeon_boundary_descends`).
9. **It reaches the pending ratios (review C3, D4).** The resident owns every open `SourceMoment`
   and `PendingRatio`.
   - `close_aeon` keeps each one's anchor `λ` and its `M`. `R` is never released, so later
     compares run on the descended constitution through the same `R`.
   - A pending ratio whose receiving phases lie outside the admitted family is refused with its
     separating direction.
   - The receipt names what was released.

[established-bounded; measured] **Bits: what is bounded, and what is not (R2 C2).** These are exact
`Fraction` measurements: the first review's scripts, the second review's and the revisions', in
[`research/notebook/hnn_design/`](../../research/notebook/hnn_design/README.md).

| Carrier | Measured | Status |
|---|---|---|
| Source moment on a non-closing Cayley ring (3/5, 4/5), one 1-bit cell per tick | 7, 34, 146, 592 bits at `n` = 2, 8, 32, 128 | not admitted: no moment on a non-closing ring |
| Source moment on a closing period-5 ring with selective stepping | its largest count: 1, 2, 3, 5, 7, 9 bits at `n` = 2, 8, 32, 128, 1,024, 4,096 | counts, `O(log n)` per slot; lossy only past `n*` (the capacity above) |
| Reaction within a word, operands read from the evolving state | 46 → 804,289 bits in 7 ticks | not the law |
| Reaction within a word, operands read from the sheet class | 44 → 705 bits in 32 ticks | the law: additive within a word |
| The revised six-ring word ([`word_bits.py`](../../research/notebook/hnn_design/word_bits.py)) | 77, 482, 1,461, 3,512, 7,623 bits at 2, 4, 8, 16, 32 ticks | additive within a word |
| The same change carried from word to word (the first design's published `s′, b′`) | 11,728, 24,057, 48,707, 98,004 bits after 8, 16, 32, 64 words of 6 ticks; one lossless ring element: 77 → 6,272 bits over 256 words (R2) | not the law (R2 C2c) |
| The same change released at each word's end | at most 963 bits in any word of 6 ticks, over 32 words | the law: bounded by one word |
| The first design's case (5): a period-5 ring and a dissipative contact, one injection per epoch, collapsed every 8 epochs | no collapse: 47, 221, 912, 1,831 bits at epochs 8, 32, 128, 256. The spectral (Bezout) projector that design stated: 72, 74, 77, 78, max 121 ([`collapse_bezout.py`](../../research/notebook/hnn_design/collapse_bezout.py), independent of R2's Sylvester solve). Its certified release: refused at 32 of 32 boundaries | withdrawn: its "3, 5, 7, 7, max 52" zeroed the wrong coordinates (R2 C2a) |
| Deposited receiving map `R` (not an operand of its own feature), `γ = 1` | 155, 176, 180, 196 bits after 8, 32, 128, 256 deposits ([`deposit_bits.py`](../../research/notebook/hnn_design/deposit_bits.py)) | slow: a function of `(H, B)` only, whose denominators the fixed word shares |
| The same, `γ = 1/2` | 1,001, 5,172, 22,477, 46,784 bits | linear in deposits: the previous map enters its own target |
| Deposited source port `E` (an operand of the word that forms its covector), `γ = 1` | 612, 3,237, 14,852 bits after 8, 32, 128 deposits | linear in deposits |

**The revised collapse's own projector.** In a learning aeon, the only kind campaign 1 admits, `V`
deletes loci: a 0/1 projection. The retained entries keep their exact values, and no denominator
is introduced. In [`release.py`](../../research/notebook/hnn_design/release.py), 72 of 156 entries
are released and the other 84 are unchanged. A frozen aeon's value-level `V` moves to campaign 3
with its descended tick.

What these show:
- **Bounded:**
  - the change, per word: it is released at the word's end. Its growth within a word is additive in
    ticks, at a rate set by the operands' bits, which grow with deposits. So it is bounded per word
    given the constitution, not absolutely (R3 §5);
  - the lift point;
  - the moment, whose counts grow `O(log n)` per slot.
- **The deposited constitution, on its declared carrier lattices (Decision 22).** Under the
  exact law it compounded: on the chain control of the HNN tests, 1,126 → 10,883 → 623,415 bits
  over two deposits at the declared steps (249 s for the second), and 7,053 → 311,864 → 2,224,183
  with the factor steps off, because `E`, `R` and `W_c` form each other's covectors through the
  word's inverses. On the lattice the word reads only lattice values:
  - the lattice entries are bounded by their magnitudes (`lattice_bits_bounded`), which grow as the
    Grams accumulate, so their bits grow logarithmically in deposits;
  - a remainder kept exact accumulates every update's denominator (`remainder_den_dvd`): about 800
    bits per entry per deposit on campaign 1's field (250 Mbit after 21 deposits, 15,000 carried
    entries). No aeon bounds that: the aeon is the joint clock's carry-out, whose mean on uniform
    bytes is `5·7·11·13·256/(52 + 5·37 + 35·24) = 1,281,280/1,077` cells, one deposit per `A = 2`
    cells, and a stream with no byte `≡ 0 (mod 5, 7, 11)` never closes one;
  - so the remainder is carried at a precision that refines with the locus's deposit count `m`,
    `k_m = 2⌊log₂ m⌋ + 1`, and the tail below it is released and reported at each deposit. Its bits
    are at most `L_ℓ + 2k_m + 1 = L_ℓ + 4⌊log₂ m⌋ + 3` (`remainder_rat_bits_bounded`); the released total stays below half a unit over every aeon since the locus's founding
    (Kraft), so every lattice value stays within one unit of the exact sum of what reached it, and
    the carried Gram within `1/(2L_R)` of the exact one in operator norm.
  - [established-bounded; measured] Receipts of
    [`hnn_lattice_growth`](../../research/notebook/hnn_design/README.md), each a command of that
    README run once in release:
    `cargo run --release -p holonics --example hnn_lattice_growth -- <mode>`. Campaign 1's field
    reads the pinned cut, `docs/plans/THE_REBUILD.md` at `fed5488c` (171,754 bytes).
    - `growth chain 128 declared`: on the chain control the constitution levels at about 30 kbit
      (29,899 bits at deposit 128), the widest remainder takes 51 bits, a deposit takes 28 ms on
      average, and the 22 aeon boundaries release nothing.
    - `growth campaign 40 declared`: on campaign 1's declared field the constitution grows from
      0.19 to 1.37 Mbit over 40 deposits against `B_Θ = 2^33`. The widest remainder takes 45 bits,
      and the solved charts take 0.56 Mbit and grow as the Grams fill in. A refine takes 0.49 s, a
      compare 4.7 s and a deposit 1.8 s on average, so the full `n*` exposure (6,148 cells, 3,074
      windows) projects to 21,773 s, about 6 h. These are the costs of the integral chart: products
      summed over integers with each entry reduced once, a fraction-free inverse, integer tick sums
      in the compose, and only the nonzero offset counts read.
    - `equality chain 32 declared`, `equality chain 32 normal` and `equality campaign 8 declared`:
      the integral chart changes no value. At every deposit each update is recomputed termwise over
      `Rat` and the carry's accounting is checked on every carried entry: 19,008 entries are equal in
      each chain run, and 760,648 over 8 deposits on campaign 1's field.
- [open] **What stays owed (#62, "Step 4 (#73) owed").**
  - **The word-level certificate.** `remainder_below_grain` bounds one read of one locus with
    unit-scale operands. The receiver reads the whole word, which composes loci over its ticks: on
    the chain, the carried remainders move the admitted logits by up to 0.72 of a grain at the first
    six boundaries (`growth chain 128 declared`, reading `Θ` against `Θ + r`). The
    certificate is `Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`, with `K_ℓ` the word's sensitivity from locus `ℓ` to
    the logits: passivity gives `‖dCay‖ ≤ ‖dK‖` for an element whose symmetric part is `⪯ 0`, and the
    contrast port `W_c`, which is active, needs its own bound. `Objects/CommitRebase` carries the
    counterfactual chain bound once `K` exists.
  - **The solved charts.** `H⁻¹` is carried exactly; its bits follow the Hadamard bound of the
    carried Gram as it fills in, and are reported per deposit.
  - Every campaign reports the constitution's bits per deposit by carrier (entries, remainders,
    solved charts) beside the state bits per source bit, and campaign 1 keeps its budget and stop
    rule, which refuses and reports, never rounds.

#### Far fields carry moments (§8.7)

[definition] A source's emission reaches a receiver through the medium's propagator, and it is
carried by the moments that receiver distinguishes (light record §2: a receiver with a finite grain
distinguishes finitely many multipole orders).
- **The moment's quotient is campaign 3's (R2 M5).** In campaign 1, `M_g` stays integer counts and
  only `I_g` descends. From campaign 3, at an aeon boundary the `SourceMoment` is reduced by the
  retention `V_m` of the moment terrain against the admitted receivers composed with the word,
  `{ρ_R ∘ T_c}`: `M_g ↦ V_m M_g` and `m̃ ↦ V_m m̃`. `V_m` descends the counts only where it maps
  counts to counts. Otherwise it returns its separator and `M_g` stays.
- The declared offsets `Δ` are those whose second moments `C_g(δ)` survive that quotient. An offset no
  receiver reads is dropped at the boundary. From campaign 3, offsets are derived from the receivers,
  not chosen. Campaign 1 declares `Δ = {1}`.
- **The window is a shift register (review A7; R2 M7).** The last `max Δ` cells are kept in `win_g`,
  overwritten cyclically at every ingest: a bounded window of raw exterior cells. Its bits are
  counted in the moment's. It is not a closing ring, whose law accumulates. The first design's
  "delay-line ring" needed this overwrite law, and it is named here. The window enters the open only
  through `C_g(δ)` and the pair port `E_g^(δ)` (the chain above), and no tick reads it.
- **Offsets on the exterior chart (review C8).** `x_k ⊗ x_(k−δ)`, with `|A|²` counts per phase and
  offset, is independent of the learned `E` and `E^(δ)`, so it stays tape-free when either changes.

#### Release through modes (§8.8)

[definition] The HNN releases by resonance wherever a mode fits, and founds only what no mode
reaches.
- **The split.** At the receiving ring, the release drive is split by `compression::resonance_split`
  against the ring's `Parametron`. The resonating part rides the existing modes (RIDE, zero
  effort), and only the emanating part founds (FOUND).
  - The modes are the Parametron's, not the reaction element's: with unit weights on a closing
    ring, `K_g = 2I − P_g − P_g⁻¹` is a polynomial in `P_g` (R2 C2c keeps the two apart).
  - `ω²` is irrational outside `d ∈ {1, 2, 3, 4, 6}`. The split is therefore taken per rational
    mode component: the kernels of `Φ_m(P_g)`, `m | d_g`.
  - `resonance_split` gains that form: a rational projector in place of one rational eigenvalue
    (review F8).
- **FOUND is a Holarchy join.** It is `Holon::interconnect` of a new ring from the cokernel
  residual (`FaceMap::at_horizon(..).cokernel()`), within the field's declared founding capacity.
  Guard 9 constrains only the codec (review F7).
- **Release happens at width zero at the receiver's grain.** It goes through
  `receiver::release::release` with its `DecisionLaw`, and is refused when the width exceeds the
  tolerance. The width is the receiving faces' largest fibre `ε`, which lies below the grain, and the
  tolerance is the receiving phases' own grain `1/L_R`, never a free argument (R2 §2).
- **Scope.** This is campaign 3; campaigns 1–2 report the split as a reading. On campaign 1's
  closing rings the capacity `C_g = Bᵀ W_C B` of the cycle is singular: its kernel is the ring's
  harmonic (dormant) mode. The reading is therefore reported absent, never pseudo-inverted. Campaign
  3's split reports the drive's harmonic part as dormant and splits the rest on the complement of
  `ker C_g`.

#### The objects in the machine

| Object | In the HNN | Existing owner | Campaign |
|---|---|---|---|
| Complex | rings, contacts, loops; block `d_A` | `geometry::complex::{CellComplex, ConnectionIncidence}`, extended to block transports with its Lean `connectionIncidence` (review F4) | 1 |
| Holon / coholon | the field, a Holarchy's whole; receivers are coholons at the receiving ports | `holon::Holon`, `holarchy::Holarchy::whole` | 1 |
| Constitution | Θ, owned once by `Constitution`; `Field::holon()` is a read-only chart built from it (review F2) | `holon::{element, reaction, deposition}` | 1–2 |
| Navigator | one per ring: `Transport::Map`, key, clock, lift; its screw placement; a source word is its address | `navigator::{Navigator, Clock, PhaseLift, Transport}`, `geometry::screw::SituatedScrew` | 1 |
| Swing | the junction Swing about the participation anchor (one exponent per contact); the element's Cayley step | `geometry::swing` (generalized to `ℚ^d` anchors), `Holon/Cayley`; Lean `Geometry/AffineSwing` | 1 |
| Pair contact | the rings' screw pair (`Q`, `J`, `DQ`, `D²Q`); its channel (partial isometry `U_a`, reverse `U_aᵀ`); its constitution `(C_a, K_a, D_a)` and midpoint two-port; its site kind; its lock address | `holon::contact::{PairContact, ContactMaterial, pair_lock}`, `navigator::trace::SiteFactor`, `navigator::address::LockAddress` | 1 (geometry, constitution), 2 (resonance, fold, break, lock) |
| Parametron | each ring, with unit weights from campaign 1 (review F3); `C_g`, `L_g`, `ω²`, pump, sheets from campaign 2 | `holon::parametron` | 1, 2 |
| Keys | ring keys located by loop closure over the menu the data forms, by propagation over its edges; selective stepping against declared locks | `compression::keys::{Menu, Loop, Candidate, Gauge, ReflectorMachine}` and the new menu edges with propagation, `holon::contact::menu` | 1 |
| Tube / tower | source and response are longitudinal spans; multi-rate rings form an epoch tower | `holon::restriction::{tube, tower}`, `aeon::EpochTower` | 2, 5 |
| Relatively complete region | a dormant ring is interior motion in the exterior family's fibre | Lean `Objects/RelativeCompleteness` | 3 |
| Deposition | the only change of Θ, inside the causal diamond | `holon::deposition`; Lean `Objects/Deposition`, `Holon/Deposition` | 1 |
| Ratio | `ℓ = log Ĝ_(T←H)`; `R⁻¹dR`; the carried power `2^(n + k/L)` | `ratio::{Presentation, surprisal, exponentiated}`; Lean `Objects/{Ratio,RatioPhase,RatioBlock}` | 1 |
| Receiver and receipt | the receiving read at the receiving ring's epochs; per-ring receipts in their own clocks | `receiver::{reception, receipt, standing, release}` | 1, 3 |
| Holarchy | rings and contacts `interconnect`ed; `view` per receiver; FOUND joins a ring | `holarchy::{Holarchy, Gluing, view}` | 1, 3 |
| Holonic Compression | retention is the collapse; release is RIDE/FOUND; cost `Kt` | `compression::{FaceMap, Retention, resonance_split, CompressionCost}` | 1, 3 |
| Aeon, epoch, cycle | the lift point carries every aeon; the collapse at aeon boundaries; epochs count section flux | `aeon::{ClockLift, Reading, Epochs, EpochTower, TwoClocks, Cycle, EnclosedLedger}` | 1, 2 |

#### The types `holonics::hnn` adds

[definition] Each type is an elementary object or a named composition of them. The HNN row of the
operator contract names the field law, source moments, adjoint, deposition return and execution
port. No other noun enters.

| Type | File | What it is | Composes |
|---|---|---|---|
| `Ring` | `hnn/field.rs` | A closing rotor ring: its `Parametron`, its navigator (`Transport::Map`, key, clock, lift), its screw generator with `d_g` node placements, its lock `N_g` and reflector `F_g` on the port chart `ℤ/d_g`, its storage admittance `Y_g`, its standing `q_g`, and its reaction material; on a source ring, its source ports `E_g`, `E_g^(δ)` and injection `I_g`. Campaign 1 has no non-closing form. | `holon::parametron::Parametron`, `navigator::Navigator`, `geometry::screw::{ScrewGenerator, SituatedScrew}`, `holon::restriction::PortMap` |
| `Contact` | `hnn/field.rs` | A pair contact `a = (g→h)`: its channel width `k_a` and partial matchings `ι_(a,g)`, `ι_(a,h)` (so `U_a` and `U_aᵀ`), its block of `d_A`, its constitution `(c_a, b_a, F_a)`, its reference admittance `Y_a`, its participation exponent `β_a` and its pair geometry read from the two rings' screws. It has no scalar conductance. | `holon::contact::{PairContact, ContactMaterial}`, `geometry::screw::ScrewPair`, `holon::parametron::Parametron::lc` |
| `Field` | `hnn/field.rs` | The HNN law: the complex, the rings and contacts, the `Constitution`, the admitted receivers, the founding and pending capacities. `Field::holon()` returns a read-only `Holarchy` chart built from the `Constitution`, `Field::parametric()` the `ClockLift`, and `Field::describe()` the field's exact self-delimiting code. | `geometry::complex::CellComplex`, `holarchy::{Holarchy, Gluing}`, `aeon::ClockLift` |
| `Constitution` | `hnn/constitution.rs` | Θ, the standings `q` included, with a commit counter, the declared steps `γ_U` and `η_x`, and its bit budget `B_Θ`. Its fields are private, and only `deposit` and the collapse change it. | `holon::element::{ActiveRelation, ResistiveRelation, Pump}`, `holon::deposition::{project_passive, CommittedEnergyBound}` |
| `NormalLaw` | `hnn/constitution.rs` | One locus's deposition owner, `W H = B`, with factored statistics of the locus's own width. There is no global Gram (review A6). `W` and `H` are carried on the locus's lattice with their remainders, and `B = W H` is not carried (Decision 22). | `ratio::linear`; Lean `Holon/MomentStorage` |
| `Current` | `hnn/field.rs` | The lift point `λ`: the rings' continuing motion, the only current that persists between words. It has no wave field (R2 C3). | `aeon::ClockLift` |
| `SourceMoment` | `hnn/moment.rs` | On closing source rings only: the phase-binned counts `M_g`, the offset counts `C_g(δ)` on the exterior chart, the window `win_g` and its opening lift point; its capacity crossover `n*`. `m̃` is computed, never stored. | `navigator::Navigator`, `ratio::linear` |
| `Word<'c>` | `hnn/word.rs` | One evaluation of the ticks at one cut's fixed operands, opening at zero change. It borrows `&'c Field` and owns the change: the waves, the contact states and their per-tick values or checkpoints, which its return reads in reverse. Its end releases the change. | `hnn::propagation` |
| (functions) | `hnn/propagation.rs` | The junction Swing, the ring element step and the contact transit. | `geometry::swing`; the midpoint scheme of `holon::law::ReferenceHolon`, realized directly and equated with it in two tests (reception item 1) |
| `ReceivingPhases` | `hnn/receiving.rs` | The receiving ring, its epochs `e_j`, aperture `A`, grain `L_R` and the shared map `R`. It refuses `A` beyond the rank of the receiving ring's observability over the word, which it reports (review C7). | `receiver::reception::ReceiverFace` |
| `HolonRatio` | `hnn/ratio.rs` | `R_j = Ĝ_(T←H)` at each receiving phase, as undivided pairs, with `ℓ`, its branch and the receiver's fibre. | `ratio::Presentation`, `ratio::surprisal::SymbolicSurprisal`, `ratio::exponentiated::{RatioFamily, CarriedPower}` |
| `RatioCovector` | `hnn/ratio.rs` | `R⁻¹dR` at the face: the magnitude part `p̂ − q` and the phase part `−q_c Δ_c`, in units of `ln 2` carried as a declared factor. Only a `HolonRatio` constructs it. | — |
| `PendingRatio` | `hnn/pending.rs` | The producing anchor `λ`, the encoder moment `M`, the `ReceivingPhases` and the commit it was produced at. It is owned by the resident and addressed by `PendingId`. | the types above |
| `Pullback` | `hnn/port.rs` | Covectors on `M`; per contact `(λ_Δ, λ_Q, λ_DQ)` and its constitution; per ring its reaction material, its standing `q` (through the declared lock chart) and `E_g`, `E_g^(δ)`; `R`. The key covector is a reading only. | `holon::contact::PairContact::feature_pullback`, `holon::law::HolonLaw::pullback` |
| `Deposit` | `hnn/port.rs` | The staged material return, keyed by locus, inside the causal diamond, addressed by `StagedId`. | `holon::deposition` |
| `AeonBoundary` | `hnn/retention.rs` | What the collapse returns: `V = ⊕V_g`, the descended constitution, the released loci and directions with their dimension and bits (structural, and the value kernel as a reading), the first-law split, each receiver's aeon reading, and the pending ratios carried or refused. | `compression::{FaceMap, Retention}` (specification and the dual face map), `aeon::{exchange, deposition}` |
| (functions) | `hnn/keys.rs` | The data → menu map, key location per ring in carry order, and the gauge fixing. | `compression::keys::{Menu, Loop, Candidate, Gauge, ReflectorMachine}`, the new menu edges and propagation |
| (functions) | `hnn/release.rs` | Release through modes and founding (campaign 3). | `compression::resonance_split`, `receiver::release`, `holarchy` |
| `MomentId`, `PendingId`, `StagedId` | `hnn/port.rs` | Handles into the resident, so that the moment, pending ratios and staged deposits stay on the card in step 5 (review D1). Each has a declared consumer and `discard` (R2 M11). | — |
| `ExecutionPort` | `hnn/port.rs` | The trait the CUDA and Apple backends implement in step 5. | — |
| `Reference` | `hnn/reference.rs` | The exact host implementation of `ExecutionPort`. | everything above |
| `MotorChart` (campaign 4) | `hnn/motor.rs` | A serial screw word as a source and receiver chart of the same field. | `holon::contact::{SerialChain, LinkContact, LinkContactJacobian}` |
| `Encoding` (campaign 5) | `hnn/encoding.rs` | `(E, U_a per admitted action, D)`, with its two squares. | `holon::restriction::descent::{square_descent, factor_descent}`, `compression::FaceMap` |
| `Context` (campaign 5) | `hnn/context.rs` | The causal cut restricted to the admitted receivers. | Lean `Foundation/AddressedBoundary.boundary_join`, `Transport/WorldTube.ClockedSpan` |
| `JointPrediction` (campaign 5) | `hnn/prediction.rs` | `Γ_m` over `m` receiving stations of one joint refinement. | `ReceivingPhases`, `receiver::release::{release, DecisionLaw}` |

Some types are not added (review F):
- There is no `Key` type (F5). A key candidate is a
  `compression::keys::Candidate<Vec<navigator::Clock>>`: one clock per ring, with the port images.
- There is no `hnn::Reception` (F1). Every port method returns
  `receiver::reception::InteractionReturn`, made generic in its owner over the payloads of (c), so
  that the base module never depends on `hnn` (R2 M10). Each component is a declared absence where
  a method does not produce it.

The additions outside `hnn`, each in its owner and with its Lean:
1. `navigator::Transport::Map`: a finite-order exact port map (review C6).
2. Block transports in `geometry::complex::ConnectionIncidence` and Lean `connectionIncidence` (review
   F4).
3. `geometry::swing` generalized to `ℚ^d` anchors.
4. `ratio::exponentiated::CarriedPower`: `2^(n + k/L)` as a carry `n` and a phase `k ∈ ℤ/L` in
   `ℚ(θ)`, `θ^L = 2` (§8.4).
5. `compression::resonance_split` over a rational mode component (campaign 3).
6. `receiver::reception::InteractionReturn<Fw, Pb, Dp>`, generic over its forward, pullback and
   deposit payloads. Each is a `Component<T> = Absent(reason) | Present(T)`. Its existing callers
   take the absent payloads, and `hnn` supplies handles, never `Current` by value (R2 M10).
7. `compression::keys` menu edges and propagation, the Bombe's diagonal board (R2 H4d); see the
   data → menu map in (d).
   - **The edge.** A one-stage open path of a menu: two ports and a stage per key, whose stage is an
     involution, so it can be traversed both ways. A `Loop` is a closed path of edges.
   - **`propagate(keys)`.** For each key and each image of one seed port per connected component, it
     sets `S(v) = W_k S(u)` along the edges, and refuses on a conflict or a repeated image.
   - **Its law.** It returns exactly the candidates whose images satisfy every edge, which are the
     fibre of the component's fundamental-cycle menu with injective images.
   - **Its work** is `keys × d × edges`, where enumerating `PortImages::injections` costs
     `keys × d!/(d − m)!`, past `IMAGE_FAMILY_CEILING`.
   - [established-bounded; measured]
     [`propagation.py`](../../research/notebook/hnn_design/propagation.py), `d = 7`: propagation
     equals brute force over all 5,040 plugboards on every menu tried, at 322–3,822 steps against
     35,280.
8. `receiver::release::DecisionRule`: the data form of the declared decision laws, implementing
   `DecisionLaw`, so that step 5 can take the decision as data (R2 M11).

[established-bounded; source-inspected] **Built in campaign 1** (September 25), each with its Lean:
- 1 as `Transport::Map` (`order`, `compose`); a `Ring` carries a `Navigator` rotor, and
  `ReflectorMachine` is built only for keys (Lean `Holon/Generator.{map_pow_mod_order,
  map_turn_lossless, map_compose_order_pos, map_compose_order_dvd, mapRotor_order}`).
- 2 as block transports in `ConnectionIncidence`, held by `Field::connection` and read at the
  contact's from-end, `(d_A q)_a = U_aᵀ q_h − q_g`, matching `∂₁` (Lean `Holon/Complex.{blockIncidence,
  blockWalkRead_incidence, block_cell_curvature, block_flat_closed}`). Campaign 1's declared loop is
  flat, so `d_A¹ d_A⁰ = 0`. Its consumer is `Field::contrast`, the contrast map
  `(M x)_r = Σ_(a: s a = r) T_a x_(t a) + Σ_(a: t a = r) T_aᵀ x_(s a) − x_r`, `T_a = U_aᵀ`, which
  reads ring `r`'s row blocks of `d_A` forward and its column blocks transposed. `M` is symmetric
  (off-diagonal blocks `T_a` and `T_aᵀ`, diagonal `−I`), so the one map gives the standing contrast
  `Δ = M q` and carries the class covectors back to `q`. `Contact::transport` and
  `Contact::reverse` are deleted; the transit reads its channel through `Contact::selection`.
- 3 as `geometry::swing` over `ℚ^d` anchors, which `propagation::junction_swing` calls.
- 4 as `ratio::exponentiated::CarriedPower` (Lean `Objects/Ratio/CarriedPower`).
- 6 as `InteractionReturn<Fw, Pb, Dp, Ph = (), Rc = Receipt>`, with the phases and the receipt as two
  further defaulted payloads; every port method takes `Ph = Vec<ReceivingPhases>` and
  `Rc = hnn::port::PortReceipt` ((c)), and `hnn::port::PortReturn` is deleted.
- 8 as `DecisionRule`, which `ExecutionPort::release` takes.
- `Field::holon(&constitution)`: the rings joined by the contacts, the rings' port map `−d_Aᵀ`.
- The mount certifies `Field::holon` (the Holarchy glues, keeping its parametric orientation) and
  refuses a singular `C_a`; `view` and `count` are declared absent while the gluing is ports-only,
  with no regions.
- `AeonBoundary` is built on `aeon::Aeon<ClockLift>` between the aeon's two lift points: its
  readings from `aeon::reading`, its epochs from the aeon epoch owner (section flux), and the
  carry-out as an `aeon::Cycle` when the last ring opened on its section (otherwise a declared
  absence). `Field::describe` includes the constitution's declared `γ_U`, `η_x`, `B_Θ` and pending
  capacity (review D3).

`exponentiate_face`, a committed centre, is not added (§8.4).

#### Exact charts (§8.4, §8.5)

[definition] The reference is exact. Nothing in it rounds or commits (review A2, C1). The one
rebase is the deposit's (Decision 22): each update is carried onto its locus's lattice with its
remainder, whose precision refines with the locus's deposit count. The part below that precision is
released and reported at each deposit, and its total stays below half a unit over every aeon since the locus's founding.
- **Complex currents** are realified as `[re₀, im₀, re₁, im₁, …]` over ℚ with the complex structure
  `J`, as `holon::reaction::realify` does.
- **Phase: rings close by default.** A closing ring's transport is a port permutation. Its entries
  are 0/1, it closes at `d_g` (`geometry::winding::Odometer`, `holon::parametron::ring_crossings`),
  and it has no bit growth. Its complex modes, the roots of unity, are a chart that is read and never
  evaluated. Its rational mode components are the cyclotomic factors. Campaign 1 admits no
  non-closing ring, as above.
  - The ring's reaction element `Cay_r` is a different operator. It is a non-closing rotation, and
    it acts only within a word (R2 C2c).
- **Exact inside, grain only at the face (§8.4).**
  - The base-2 chart carries `κ = 2^s` with modulus and remainder, `s = n + r`. The integer `n` is a
    carry, an exact shift by `2^n`. The remainder `r = k/L` is a phase in the finite set `ℤ/L` that
    the receiver's grain distinguishes, and `2^(k/L) = θ^k` with `θ^L = 2`.
  - The phase odometer's carry is multiplication by 2. `ℚ(θ)` is a field, because `x^L − 2` is
    Eisenstein at 2, so normalization is exact division there (`CarriedPower`).
- **Participation scores lie on the lattice by construction.**
  - The screws' placements and pitches have declared denominators, so every quadrance lies in
    `(1/q_Q)ℤ`.
  - `β_a` lies on the lattice `(2q_Q/L)ℤ`, one per contact (R2 C1), which makes it a key: declared
    in campaign 1 (Decision 2), its location owed with continuous keys (#62, step-3 list item 3).
  - So `s_a ∈ (1/L)ℤ` and the fibre is empty.
  - Campaign 1 declares `L = 1`, which makes the weights rational. A finer `L` carries currents in
    `ℚ(θ)`, with `L` rational coordinates each, and its cost is reported.
- **The receiving face.** The logits `f` are exact rationals.
  - The receiver reads each exponent at its grain `L_R` as `f = n + k/L_R + ε` with
    `ε ∈ [0, 1/L_R)`.
  - The face `p̂` is built exactly in `ℚ(θ_R)` from `(n, k)`.
  - `ε` (written `ε_R`) is the receiver's unresolved fibre (`receiver::reception::UnresolvedFibre`).
    It is returned and never rounded, and nothing consumes it as a value.
  - **`L_R` is derived from the receiver (R2 M2).** Reading every exponent down by less than `1/L_R`
    moves each cell's code length `−log₂ p̂(t)` by less than `1/L_R` bits. So a receiver that
    declares a code tolerance of `ε_bits` per cell has `L_R = ⌈1/ε_bits⌉`.
    - Campaign 1's text receiver declares `ε_bits = 1/16`, so `L_R = 16`. Its faces live in
      `ℚ(θ_R)`, `θ_R^16 = 2`, at 16 rational coordinates per value, a cost reported with every run.
  - **The covector is read in the odometer chart (R2 M2; review C3).** The face is constant on each
    grain cell, so its derivative in `f` is zero almost everywhere, and a covector in `ℚ(θ_R)` has no
    ring map into the rational constitution (`X^L − 2` is irreducible).
    - The learning face is therefore the **odometer chart** of the carried power,
      `2^(n + k/L_R) ↦ 2^n(1 + k/L_R)`: rational, exact at every carry, continuous across it
      (`2^n · 2 = 2^(n+1) · 1`) and monotone. The covector is `R⁻¹dR` in that chart: the magnitude
      part `p̃ − q` with `p̃_c ∝ 2^(n_c)(L_R + k_c)`, and the phase part.
    - [agent-inferred] It is a declared chart, not the face's derivative, and it is a **strict
      descent direction for the scored face**: the scored code length `−log₂ p̂(t)` has logit
      gradient `p̂ − q`, and `⟨p̂ − q, p̃ − q⟩ = Σ_(c≠t) p̂_c p̃_c + (1 − p̂_t)(1 − p̃_t) > 0` for at
      least two classes (Lean `HNN/Ratio.odometer_covector_descends`). At an integer cell it is the
      face (`odometer_eq_face_at_integer_cells`), and its weight dominates the face's,
      `2^(n + k/L) ≤ 2^n(1 + k/L)` (`face_weight_le_odometer`), by at most the factor
      `max_x (1 + x)/2^x ≈ 1.0615` (a reading). At `L_R = 1` the two agree.
    - The face `p̂` that is read, scored and reported stays exact in `ℚ(θ_R)`.
    - The word-adjoint test covers the word up to the logits `f`, not through the grain.
  - Base 2 is a declared chart. Temperature is a root on the ratio family for real `β`, but a rational
    `β` does not reach base `e` (review B1).
- **Log and phase.** Magnitude log-ratios are `SymbolicSurprisal` forms and are never evaluated.
  - The imaginary part of a receiving potential is carried in turns.
  - A phase gap is `Δ_c = δ_c + n_c`, with `δ_c` rational and `n_c` the winding, so the phase
    descent cost `½ Σ_c q_c Δ_c²` is exact.
  - The covector on `s` carries `ln 2` as its unit, a declared factor.
- **Solves are local only.**
  - A junction divides by its own positive admittance sum.
  - The element's `I − ½K` is invertible for skew-plus-passive `K` (`Holon/Cayley.cayley_bijective`).
  - The transit solves its own `k_a`-sized `M_a ω_a = …`, with `M_a ≻ 0` for campaign 1's squared
    carriers.
  - No global solve exists.

### (b) The laws stated in Lean first

[definition] Where the laws go:
- Each law lands in Lean before its Rust owner, within its campaign.
- They go in a new `lean/Holonics/HNN/`, gathered by an `HNN` entry of `Holonics.Framework`, so the
  default target checks them.
- `Holonics` cannot import `HolonicsResearch`. A research owner that an HNN law needs is moved into
  `Holonics` with its callers; it is not copied.
- An open item names its #62 item.

| # | Law | Existing owners it composes | New module and theorems | Rust consumer | Campaign; #62 |
|---|---|---|---|---|---|
| 1 | The ring's element: the power-neutral Cayley step at the sheet-class operands | `Holon/Cayley.{cayley_isometry, midpoint_reaction_balance, drive_balance, driveCovector, cayley_bijective, inner_devK}`, `Holon/Reaction.{skewReaction_workless, bilinear_reaction_workless_iff_zero, skewPart_orthogonal}` | `HNN/Word.lean`: `reaction_stage_isometry` (with `W_s = 0` and `W_c = 0`, `\|y′\| = \|y\|`); `reaction_stage_balance` (`(I − ½K)s′ = (I + ½K)b + W_c c` gives `½\|s′\|² − ½\|b\|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩`, composing `drive_balance`); `contrastPort_active` (for `W_c c ≠ 0` some `b` makes that power positive, so the stage is passive for every input exactly when `W_c = 0`); `reaction_stage_adjoint` (`u = (I − ½K)^(−*) g`: the drive covector `2u − g`, the contrast covector `W_c* u`, the slice covectors `Re⟨u, A_ρ x̄⟩`); `word_tick_balance` (over the global power `P = (h/4)[Σ_r Y_r\|s_r\|² + Σ_(r,a) G_a\|a_(r←a)\|²] + Σ_a E_a`, one tick changes `P` by exactly `−h Σ_a ω_a*D_a ω_a + (h/2)Σ_r Y_r⟨x̄_r, W_s,r x̄_r⟩ + Π_c`, `Π_c = (h/2)Σ_r Y_r⟨x̄_r, W_c,r c_r⟩`: the Swing contributes zero, the element and the transit their balances; R2 C1, R3 C1) | `hnn::propagation` | 1; 5 |
| 2 | Local propagation: the junction Swing, the transit and the causal cone (§8.1) | `Geometry/AffineSwing`; `Computation/HolonicAdjointNormalization.{sourceDerivedProjection_idempotent, sourceDerivedScatter_involutive, dualMap_comp_reverse_order}`; `Holonics/Computation/HolonicConstitutiveCirculation.weighted_square_energy` (the two-port junction, atlas `wave.two-port-junction`); `Computation/HolonicWorldReturnDeposit` (junction reflection, `T + Γ² = 1`, route deposits); `Physics/ScatteringWaveHeat` (attenuation heat); `Transport/JunctionLaw` | `HNN/Propagation.lean`: `anchor_is_participation` (the anchor's weights are the normalized participation, self port included); `junctionSwing_involutive`; `junctionSwing_isometry` (the `W`-weighted power, `W = diag(Y_r, G_a)`, one `G_a` per contact read at both ends); `partialIsometry_transit` (`U_a = ι_hι_gᵀ` is a partial isometry with reverse `U_aᵀ`, and the untransmitted part reflects with its norm); `transit_balance` (the contact's midpoint two-port: `E_a′ − E_a + h ω_a*D_aω_a = (hG_a/4)(\|α\|² − \|α_out\|²)`); `tick_well_defined` (`cayley_bijective` for passive `K_r`, and `M_a ≻ 0` for `C_a, D_a, K_a ⪰ 0`, `G_a > 0`; no invertibility is claimed, R2 H2); `tick_causal_cone` (support after `t` ticks lies in the ball of radius `t`); `reached_loci_diamond` (the return's covector lies in the causal diamond); `release_past_diamond` (with `r` and `o` the reach and observe distances and `e_last = e_0 + A − 1`, an operator on an edge `x → y` with `r_x + 1 + o_y > e_last` changes no admitted reading; R3 R1). The continuum (telegraph, then heat) limit is a reading, owed in #62. **Scope (review L1):** `tick_causal_cone`, `covector_causal_cone`, `trajectory_pairing`, `word_variation_exact`, `reached_loci_diamond` and `release_past_diamond` are proved on an abstract time-invariant sparse linear `BlockOp`; the concrete tick has `HNN/Word.{fieldTick_balance, fieldTick_local, word_tick_cone, elementSolve_spec, transitSolve_spec}`, and the bridge (`fieldTick` linear in the change at fixed operands, a `BlockOp` on rings and contacts with `blockAdj` sparsity) is owed | `hnn::{propagation, word}` | 1; 5, and "Step 4 (#73) owed: the diamond on the concrete tick" |
| 3 | Moment accumulation on closing rings with selective stepping, and its tape-free adjoint | `Transport/SourceMoment.{moment_closed_form, position_adjoint_is_tape_free, offset_moment_separates_pair, streamDescent}`; `Objects/SourceHolon.{moment_closed_form, jointMoment_append_one, momentStanding, native_futureAgreement_iff}`; `Objects/SourcePorts.{moment_eq_symbol_sum, port_eq_symbol_sum, moment_transpose, anchor_covector}` | `HNN/Moment.lean`: `encoderMoment_contract` (`m̃_g = ⟨M_g, E_g⟩` for every linear `E_g`); `encoder_covector_tape_free`; `selectiveClock_stream_descent` (with input-dependent clocks, the fixed-size state is a `ReceiverHistoryCompression` for the append action); `closingRing_moment_is_phaseBinned` (`M_g = Σ_c P^(−c) ⊗ h_c`, `h_c ∈ ℕ^\|A\|`); `exteriorOffset_independent_of_E`; `selective_position` (`steps_g(k)`, counted from the aeon's opening, depends only on the aeon's cells, the declared locks and the earlier rings' configurations, so the rotor position is `key_g + steps_g(k)`; R3 K1); `moment_capacity` (the persisting source state takes at most `N(n)` values, the stated product of binomials; where `N(n) < \|A\|^n` the source → state map is not injective on `A^n`, and that holds for every `n ≥ n*` by convexity; R2 H1, R3 H1); the moved `DirectedContact`, `pooledContrast`, `pooledContrastPullback`, `pooledContrast_zero_of_absent_kind` and `pooledContrast_pairing_adjoint` (kinds and multiplicity kept; review B5, F6) | `hnn::moment` | 1; 4 |
| 4 | The normal constitution and deposition, per locus | `Physics/AccumulatedNormalResponse.{normalProxyTarget_residual_eq_scaled_covector, rankOne_update_residual_identity, unitPrior_data_separation}`; `Objects/Deposition.{normal_law_local, normal_law_keeps_posSemidef, constitutionStanding}`; `Holon/Deposition.{commit_balance, projectPassiveCongruence_passive, certified_committed_energy_bound}`; `Holon/MomentStorage` | `HNN/Normal.lean`: `normalStatistic_standing` (the objective factors through `(H, B, C_data)`: a `StandingLaw` that keeps the statistic, never the sample list); `normal_prox_step` (`W_next = W + γ_U g f* H_next⁻¹`); `deposit_local`; `reaction_deposit_storage_unchanged`; `factorCarrier_psd` (`C = cc*`, `K = bb*` and `D = FF*` stay PSD under every factor update, with no clamp); `standing_deposit` (`q` changes only by deposit, through the declared lock chart; a sheet class changes only where a deposit carries `Δ_ρ` across zero; R2 C3) | `hnn::constitution` | 1; 5 |
| 4b | Deposition on a declared carrier lattice, with the remainder carried at a precision that refines with the locus's count and the tail released and reported (Decision 22) | `Geometry/PhaseCarry.carry_cocycle`; `HNN/Retention.deposit_descends`; the Ratio's `div_rem`; `Objects/CommitRebase` (the counterfactual bound, owed with `K`) | `HNN/LatticeDeposit.lean`: `div_rem_spec`, `rem_bounds`, `quot_eq_zero_of_bounds` (nearest point, ties upward); `carry_accounting`, `lattice_deposit_accounting` (applied + carried + released = the exact sum); `gamma_kraft_lt_one` (`Σ_(m≤M) 2^(−(2⌊log₂ m⌋+1)) < 1`); `release_bounded`, `release_bounded_since_founding`, `within_one_unit_since_founding`; `remainder_numerator_bounded`, `remainder_rat_bits_bounded` (`O(L + 2 log₂ m)` bits); `carried_gram_posDef`, `carried_gram_posDef_rule`; `carry_zero`, `carry_entry_zero`, `carry_entry_below_grain` (heard and counted, not deposited), `listening_grain_refines`, `lattice_deposit_descends`; `lattice_bits_bounded`, `lattice_entry_bits`, `lattice_rat_bits_bounded`, `remainder_below_grain` | `hnn::constitution`: `Lattice::{div_rem, div_rem_coordinate}` (the carry's fine split at `2^(−L−k_m)ℤ` and its coarse split at `2^(−L)ℤ`), `BudgetedCarry` (the carried deposit of every entry), `gamma_length` | 1; "Step 4 (#73) owed": the word-level certificate, and the counterfactual bound through `Objects/CommitRebase` |
| 5 | The Holon-ratio loss at the receiver's face, and the carried power (§8.4) | `Objects/Ratio.{logRatio_mem_logFibre, liftedCrossEntropy_excess_eq_logRatio, lossCovector_eq_expected_logDerivative, winding_separates_liftedCrossEntropy}`; `Objects/RatioPhase.{excessCovector_re, excessCovector_im, alignCost_gradient_sign, phaseGap_winding}`; `Physics/InformationDifference.liftedCrossEntropy_commonPhase` | `HNN/Ratio.lean`: `receivingPhase_ratio` (a common rechart leaves `ℓ_j` unchanged); `receivingPhase_pullback`; `alignCost_turns` (the windowed gap: with `τ = d_R w + ρ`, the absolute gap is the cut's winding `w`, the branch, plus the windowed gap, on which the cost and its gradient `−½ q_c Δ_c` are exact; review C1); `odometer_covector_descends` (`⟨p̂ − q, p̃ − q⟩ > 0`: the odometer chart's covector is a strict descent direction for the scored face; review C3), `odometer_eq_face_at_integer_cells`, `face_weight_le_odometer`; `carriedPower_exact` (`2^(n + k/L) = 2^n θ^k`, `θ^L = 2`; the phase carry is multiplication by 2; `ℚ(θ)` is a field); `face_constant_on_fibre` (the face depends only on `(n, k)`; `ε` is the receiver's fibre). `Objects/CommitRebase` is not used | `hnn::ratio` | 1; 5 |
| 6 | Retention as the collapse onto what the admitted future distinguishes (§8.3) | `Foundation/Standing.standingLaw_exists_iff_future_factors`; `Compression/Core/FaceMap.{kernelQuotient_is_coarsest_retention, ker_faceMap_invariant, kernelHistoryCompression}`; `Objects/Retention.minimalRetain_factors_through_every_standing`; `Aeon/Clock/Winding.reading_navigatorClock` | `HNN/Retention.lean`: `word_opens_at_zero` (between words only `(Θ, λ, M)` and the pending ratios persist); `fieldStanding` (a `StandingLaw` with carrier `(Θ, λ, M, pending)`, generators `ingest`, `locate_keys` at an aeon boundary and `refine` then `compare` then `deposit`, observations the admitted faces after every admitted word over the class family `{T_c}`, and `retain` the collapse; R3 R3); `diamond_recursion` (the reach and observe recursions compute `r_g = dist(𝒮, g)` and `o_g = dist(g, R)` in `e_last` rounds, and a block reached at `r_x` lies outside `horizonBlind(e_last − r_x)` exactly when `r_x + o_x ≤ e_last`; R3 R2); `release_indistinguishable` (every locus the diamond rule releases changes no admitted reading); `release_structural` (the release computed on the loci's sparsity is invariant under every admitted deposit); **`deposit_descends`** (a deposit gives the same result with or without the collapse: `collapse ∘ deposit = deposit ∘ collapse` on the admitted family, because the features and covectors a retained locus reads in its diamond window depend on no released locus, and a released locus receives no covector; composes `tick_causal_cone` and `reached_loci_diamond`; R3 R3); `admitted_nonincreasing` (the collapse is sufficient for every later aeon exactly when each later admitted family is contained in this one); `local_retention_blocks` (the block-diagonal 0/1 projection is lawful and keeps the contact graph); `constitution_descends` (deleting released loci keeps every retained operator's law and values, and every receiver factors); `contemporary_read` (with the producing anchor held, a delayed read equals the immediate one when no deposit intervened, and otherwise returns the residual); `lift_reading`. **Scope (review L1):** `release_indistinguishable`, `deposit_descends`, `release_structural`, `admitted_nonincreasing`, `contemporary_read`, `fieldStanding` and `word_opens_at_zero` are proved on the abstract `BlockOp` of item 2 (`word_opens_at_zero` is its linearity; the Rust guarantee is structural, `Current` has no wave field); `diamond_recursion` and `lift_reading` hold as stated; the concrete-tick bridge is owed | `hnn::{retention, pending}` | 1; 6, and "Step 4 (#73) owed": bounded bit growth of the deposited constitution (open), and the diamond on the concrete tick |
| 7 | Keys by loop closure, and selective stepping (Brandon, September 22) | `Compression/Core/Keys.{fibre_eq_bombe, fibre_cons, fibre_gauge_invariant, fibre_eq_orbit}`, `Keys.Machine.{stage_succ, rotorGauge}`; `Transport/HelicalPairInteraction.menu_loop_closure` | `HNN/Keys.lean`: `contact_menu_closes` (a cycle of observed deterministic contacts closes under the true key); `field_loop_fibre` (the consistent ring keys are the Bombe fibre of the field's menu, up to the rotor gauge); `selective_step_dormant` (a ring whose lock no input fits keeps its configuration, so its mode is invariant until a fitting input arrives); `propagation_eq_edge_fibre` (the propagated survivors are exactly the candidates satisfying every menu edge: the fibre of the component's fundamental-cycle menu with injective images); `gauge_fix_unique` (each rotor-gauge orbit has exactly one member with `S_g(p_0) = 0`) | `hnn::keys` | 1; 3, 8 (continuous keys: item 3 of the step-3 list) |
| 8 | Ring and contact storage, lock and flow | `Objects/Parametron.{modeEnergy_conserved, ringCrossings_eq, perceptron_is_a_face}`; `Physics/{PhaseCarrier, CoupledIncidence}`; `Holon/Conformance.pairContact_resistive`; `Geometry/PairResonance`; `Aeon/Clock/Lock.lock_at_address`; `Compression/Landmark/SiteKind` | `HNN/Ring.lean`: `ring_tick_conserves_mode_energy`; `field_energy_balance`; `contact_siteKind` (a lossless contact's tick transfer is a rotation exactly when `K_a > 0`, null at `K_a = 0` (the fold) and a boost when `K_a < 0`); `contact_lock_address` | `hnn::field` | 2; pump/Floquet locking open |
| 9 | Release through modes, and founding (§8.8) | `Compression/Core/Resonance.{split_exists_unique, split_orthogonal, emanating_drive_needs_effort}`; `Foundation/ReceiverRelease`; `Objects/RelativeCompleteness` | `HNN/Release.lean`: `release_through_components` (the split over a closing ring's rational components `Φ_m(P)` is `C`-orthogonal and exact); `found_reaches_cokernel` (a ring founded from the cokernel residual reaches that face); `dormant_ring_retained` (a cycle receiver keeps a harmonic ring mode silent to the exterior family) | `hnn::release` | 3; 6 |
| 10 | The motor chart | `Transport/SerialScrewChain` | the chain Jacobian in `Transport/SerialScrewChain`; `HNN/Motor.lean`: `motor_pullback` (`⟨w, Jθ̇⟩ = ⟨Jᵀw, θ̇⟩`) | `hnn::motor` | 4; 2 |
| 11 | Joint prediction as a boundary section | `Computation/JointReceiverWitness`; `Foundation/Holon.{ofEvolution, ofEvolution_receive_eq_encoded}`; `HolonicsResearch/Transport/ArtifactRelease.{step, stepMulti, restriction_never_widens}`, moved into `Holonics/Transport` | `HNN/Prediction.lean`: `jointSection`; `station_faces`; `joint_not_marginals`; `release_width_zero` | `hnn::prediction` | 5; 4 |
| 12 | Holonic Encoding: `E_next T = U E`, `D E = ρ` | `Physics/ReflectedBoundaryMemory.{boundary_reduction_iff, boundary_reduction_with_forcing}`; `Foundation/JointReceiverDescent.joint_generator_descends_iff`; `Holon/Restriction.{descent_total, scale_square_pow}` | `HNN/Encoding.lean`: `injection_square`; `encoding_reduced_recurrence`; `encoding_separator` | `hnn::encoding` | 5; 4 |

[project-postulate; agent-inferred] **Retired with campaign 1, in this order.**
1. The directed-contrast law of `Transport/GeneratorSourceEpisode.lean` moves into `HNN/Moment.lean`
   first (review B5, F6): `DirectedContact`, `pooledContrast`, `pooledContrastPullback`,
   `pooledContrast_zero_of_absent_kind` and `pooledContrast_pairing_adjoint`. Its atlas row
   `navigator.pooled-contrast-adjoint` is repointed.
2. Then the file's ordered tape is retired: `occurrenceForward`, `occurrenceDifferential`,
   `occurrencePullback`, `OrderedLinearStep`, `orderedVariation`, `orderedState`, `reverseReturn`,
   `gradientPairing` and `orderedVariation_reverse_pairing`. The generic reverse telescope is
   `dualMap_comp_reverse_order`.
3. `Transport/ContactAmplitudeState.lean` is retired: a fold over an update list, and its
   `realizedOperator` duplicates `ContactFactorScale.amplitude`. The standing binding is
   `fieldStanding`.

Both files leave `Framework.Dynamics`, and their remaining atlas rows are repinned to `13f8c734`
permalinks in the same commit.

### (c) `holonics::hnn`: layout, host reference and execution port

```text
crates/holonics/src/hnn/
  mod.rs           header with the Lean table; HnnError; re-exports
  field.rs         Ring, Contact, Field, Current; declaration checks (n*, one exponent per contact); holon() (read-only chart); parametric(); describe()
  constitution.rs  Constitution, NormalLaw (per locus, factored)
  moment.rs        SourceMoment on closing source rings: selective stepping, phase-binned counts, the window and offset counts
  propagation.rs   the junction Swing, the ring element step, the contact two-port; the global power; the causal cone
  word.rs          Word<'c>: opens at zero change; the ticks at fixed operands; forward; pull_back(self) over its own waves or checkpoints; the release at its end
  receiving.rs     ReceivingPhases; the read at the receiving epochs
  ratio.rs         HolonRatio, RatioCovector, readings
  pending.rs       PendingRatio
  retention.rs     AeonBoundary; the collapse onto what the admitted future distinguishes
  keys.rs          the data → menu map; key location per ring by propagation; gauge fixing (campaign 1)
  release.rs       release through modes; founding (campaign 3)
  port.rs          ExecutionPort, Pullback, Deposit, MomentId, PendingId, StagedId, Handle
  reference.rs     Reference: ExecutionPort, exact
  motor.rs         MotorChart (campaign 4)
  encoding.rs      Encoding (campaign 5)
  context.rs       Context (campaign 5)
  prediction.rs    JointPrediction (campaign 5)
  tests/           one fast test per stated law
```

`lib.rs` gains `pub mod hnn;`, and its header lists ten modules (with `physics`, K3–K4). `holonics` keeps its
four dependencies.

[definition] **The host reference.** `Reference` implements `ExecutionPort`, and its `Resident`
holds the `Field`, the `Current`, the `Constitution`, the open moments, the open pending ratios, the
staged deposits and the first law's arrived operand, `Arrived`.
- **`Arrived`** is the last compared pending ratio (its anchor `λ`, its moment copy `M` and its
  `ReceivingPhases`) with its `A` target cells: the one operand the aeon's `EnclosedLedger` reads
  next. A deposit re-reads it at the successor (the deposition step); a collapse that releases a
  locus its diamond reads re-reads it at the collapsed constitution (an exchange step); the next
  compare replaces it. There is at most one, it is counted in `Resident::state_bits`, and no other
  method reads it. [agent-inferred: it is kept in the resident rather than in the staged deposit,
  because the collapse's re-read needs it after the staged deposit is consumed or discarded.]
- Every value is in ℚ, in `ℚ(θ)` at a face of grain `L > 1`, or is a `SymbolicSurprisal` form.
- No value is committed or rounded, and no float exists anywhere in `holonics`.
- A person reads an enclosure (`ExactInterval`) that the application renders.

Each method returns the same typed relation as the resident `holonics-cuda::hnn`. Parity in step 5
is per law and per kernel family:
- the reference's exact value lies in the dyadic ball the device returns;
- at a grain face both return the same cell `(n, k)`, and the device's ball for the fibre contains
  the reference's `ε` (review D3).

```rust
pub trait ExecutionPort {
    /// The field, its lift point, the constitution, the open moments, the open pending ratios and
    /// the staged deposits: on the card for a device (review D1).
    type Resident;
    /// The backend's own capacity census: its pending capacity, the declared constitution budget
    /// and its arithmetic (a device reports its own, never another's constants).
    fn census(&self) -> Census;
    /// Mounts the field at the lift point with the declared initial constitution (a transfer).
    fn mount(&self, field: &Field, current: &Current) -> Result<Self::Resident, HnnError>;
    /// The field, the lift point, and every open handle with its exact bits (a transfer; R2 M11).
    fn read(&self, resident: &Self::Resident)
            -> Result<(Field, Current, Vec<(Handle, u64)>), HnnError>;
    /// Opens (`None`) or extends a moment; stops at a carry-out of the joint clock (R2 M12).
    fn ingest(&self, resident: &mut Self::Resident, moment: Option<&MomentId>,
              cells: &[Vec<(usize, Rat)>])
              -> Result<(MomentId,
                         InteractionReturn<Ingested, (), (), Vec<ReceivingPhases>, PortReceipt>),
                        HnnError>;
    /// Locates the ring keys, per ring in carry order, from the crib that closed the aeon (at most
    /// its last cells, already ingested and read), at one offset. Admitted only between
    /// `close_aeon` and the next ingest; re-keys the rings whose fibre is one orbit, each key
    /// carried over the crib to the boundary, and leaves the open moment untouched (R3 K1;
    /// review D1).
    fn locate_keys(&self, resident: &mut Self::Resident, crib: &[Vec<(usize, Rat)>],
                   offset: usize)
                   -> Result<InteractionReturn<KeyLocation, (), Vec<Option<Clock>>,
                                               Vec<ReceivingPhases>, PortReceipt>,
                             HnnError>;
    /// Borrows the moment and publishes only faces; there is no commit flag (R2 C3). Refused
    /// beyond the pending capacity.
    fn refine(&self, resident: &mut Self::Resident, moment: &MomentId, phases: &ReceivingPhases)
              -> Result<(PendingId,
                         InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>),
                        HnnError>;
    /// Consumes the pending ratio once the compare succeeds; a refusal leaves it open.
    fn compare(&self, resident: &mut Self::Resident, pending: PendingId,
               target: &[Vec<(usize, Rat)>])
               -> Result<(StagedId,
                          InteractionReturn<HolonRatio, Pullback, Deposit,
                                            Vec<ReceivingPhases>, PortReceipt>),
                         HnnError>;
    /// Consumes the staged deposit once its successor and the first law's re-read are computed;
    /// any other refusal leaves it staged and the resident unchanged. Refused with
    /// `HnnError::ConstitutionBudget` when the successor's exact bits exceed the declared budget,
    /// which consumes the deposit and stops deposition (`HnnError::DepositsStopped` after it);
    /// nothing is rounded (R3 §5).
    fn deposit(&self, resident: &mut Self::Resident, staged: StagedId)
               -> Result<InteractionReturn<(), (), DepositReading, Vec<ReceivingPhases>,
                                           PortReceipt>,
                         HnnError>;
    /// Borrows the pending ratio; the width is read from its receiving phases' fibres and the
    /// tolerance is their grain, never an argument; the decision is a declared rule, as data.
    fn release(&self, resident: &mut Self::Resident, pending: &PendingId, decision: &DecisionRule)
               -> Result<InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
                         HnnError>;
    /// Refused unless the joint clock has carried out since the last boundary, and unless
    /// `admitted` is contained in the previous boundary's family (R3 D1, R3).
    fn close_aeon(&self, resident: &mut Self::Resident, admitted: &[ReceivingPhases])
                  -> Result<InteractionReturn<AeonBoundary, Vec<(PendingId, Transpose)>, (),
                                              Vec<ReceivingPhases>, PortReceipt>,
                            HnnError>;
    /// Drops an open moment, pending ratio or staged deposit.
    fn discard(&self, resident: &mut Self::Resident, handle: Handle)
               -> Result<InteractionReturn<(), (), (), Vec<ReceivingPhases>, PortReceipt>,
                         HnnError>;
}
```

The arguments:
- A cell is its sparse exterior chart vector `x_k`. The codec that produced it is exterior.
- `ingest` advances the lift point `λ` in the resident, the one owner of the ring clocks (review
  C9).
- **The aeon trigger belongs to the clock (R2 M12).** When the carry chain's last ring carries out,
  which is the joint clock's declared cycle closure, `ingest` stops and reports it. The resident
  then refuses further cells until `close_aeon` runs, and refuses a `close_aeon` at any other time.
  No caller counter decides it: the winding decides where the Holarchy's temporal boundaries fall
  (aeon record).
- **`close_aeon`'s admitted family is `&[ReceivingPhases]` (R3 D1).** Each carries its receiving
  ring, `e_0`, aperture `A` and so `e_last`, grain `L_R` and map `R`: what the diamond needs.
  `receiver::standing::ReceiverReading` is a dense matrix refused past `EXTENT_CEILING = 256`, with
  no ring, epoch or grain, so it is not the type. Campaign 3 adds the cycle receivers. Every aeon
  in campaign 1 is a learning aeon, so there is no frozen flag (R3 R4).
- `DecisionRule` is the data form of `receiver::release::DecisionLaw` (addition 8). `Handle` is
  `Moment(MomentId) | Pending(PendingId) | Staged(StagedId)`, and `Faces` is the faces `p̂_j` in
  `CarriedPower` with their fibres and the exact logits behind them.
- The payloads: `Census` is `(pending_capacity, budget, arithmetic)`; `Ingested` the cells taken and
  whether the joint clock carried out; `KeyLocation` the per-ring `RingKeys`; `DepositReading` the
  applied deposit's reading (`hnn::constitution`); `Transpose` is `Retained(loci)`, the retained
  loci a carried pending ratio's diamond reads (`Vᵀ` on it), or `Separator(loci)`.
- **Consumption (R2 M11).** `refine` and `release` borrow. `compare` and `deposit` consume their
  handle only when they succeed: a refusal leaves it open and the resident as it was, except the
  budget stop, which consumes the refused deposit and admits no further deposit. `discard`
  consumes. `close_aeon` carries every open handle or refuses it, a pending ratio with its separator
  and a staged deposit with the released loci it would reach, and discards a refused one.
- Campaign 5 adds a `&Context` to `refine`, with no alias left behind.

`mount` and `read` are transfers, not passages. They return the resident, and the field, lift point
and open handles with their bits, with no `InteractionReturn`; on a device a ready upload includes
device completion.

`InteractionReturn<Fw = (), Pb = (), Dp = (), Ph = (), Rc = Receipt>` is generic in its owner
(review F1; R2 M10; addition 6).
- `forward: Component<Fw>`, `pullback: Component<Pb>` and `deposit: Component<Dp>` are each
  `Absent(reason) | Present(T)`. The base module never depends on `hnn`, and `hnn` returns faces,
  ratios and handles, never a `Current` by value. The state stays in the resident.
- `order: Component<SourceOrder>`: one `aeon::Reading` per ring and the count of cells.
- `phases: Component<Ph>`: the receiving phases the passage was bound to. Every port method takes
  `Ph = Vec<ReceivingPhases>`.
- `receipt: Rc`. The joint law keeps `Rc = Receipt`; every port method takes
  `Rc = PortReceipt` (`hnn::port`), which has five fields:
  - `rings`: a `Receipt` of per-ring regions in their own clocks, each ring's tick count as a count
    whose unit is the ring's step;
  - `balances`: each full tick's `TickBalance` (`P` before and after, the dissipation, the `W_s`
    term and `Π_c`), filled by `refine`;
  - `work`: the method's `ExactWork`;
  - `unresolved`: the receivers' fibres, per face, filled by `refine`, `compare` and `release`;
  - `detail`: a `ReceiptDetail` with one arm per method (`Ingest`, `Keys`, `Refine`, `Compare`,
    `Deposit`, `Release`, `Boundary`, `Discard`) carrying the table's receipt column.

  There is no `released` or `balance` field on the return. What a method releases is read where it
  is produced: the change released at a word's end as `ReceiptDetail::Refine`'s `released_power` and
  `peak_bits`; a deposit's released residuals as `DepositReading::{released, released_bits}`; the
  loci and remainders a collapse releases in the boundary's `Collapse`.

A component that a method does not produce is a declared absence with its reason. It is never a
default value.

The boundary gains two fields beyond the design's list, each a report of what a collapse refuses or
releases (Decision 22; `hnn::retention`):
- `AeonBoundary::refused_staged: Vec<(StagedId, Vec<Locus>)>`: each staged deposit that reaches a
  released locus, with the released loci it would reach. It is discarded, and every other staged
  deposit is carried.
- `Collapse::released_remainders: Vec<(Locus, Carrier, usize, Rat)>`: the carried remainders that
  left with the released loci, each exact with its locus, carrier array and entry ("leaves whole,
  with its remainder, reported"). The receiving map is never released, so its remainders stay.

| Method | Forward field | Complete geometry and feature pullback | Material return | Source order | Receiving phase | Receipt |
|---|---|---|---|---|---|---|
| `ingest` | `M`, `C_g(δ)` and `win_g` updated in place; `λ` advanced by selective stepping; a stop at a carry-out | absent: ingestion produces no covector. The moment's adjoint is its contraction (position `k` returns `g ∘ P^(τ(n))P^(−τ(k)) ∘ I` without stored state), which `compare`'s pullback uses (R2 L7) | absent: ingestion deposits nothing | the lift after the cells; `n` | absent: nothing is read | `n` cell accesses; the moment's exact bits, and its bits per source bit against `n*`; the carry-out, when reached |
| `locate_keys` | per ring in carry order, on the crib that closed the aeon: the fibre of consistent key candidates with their rotor-gauge orbits. A ring's key is published, gauge-fixed, only when its fibre is one orbit; otherwise its current configuration stays | absent: key location is discrete, and the key covector is a reading | the published ring clocks: the phase classes of `λ` at the aeon's opening, windings kept | the crib's edges with their positions from the aeon's opening | absent | per ring: the fibre's size, its orbits, the minimal failing loop, the candidates checked and the propagation work |
| `refine` | the faces `p̂_j` with fibres; nothing else is published (R2 C3) | absent (forward only): the `Word` is dropped | absent | the moment's lift | the binding read | per-ring tick counts; the tick power balances; the diamond's loci reached; the change released at the word's end, its power and its peak bits inside the word; the source-to-receiver path attenuation at the cut; the fibres; work |
| `compare` | the contemporary faces and the `HolonRatio` per phase, from the anchor `λ` and `⟨M, E_now⟩` at the contemporary constitution | complete: `M` through to `E`, `E^(δ)`; per contact `(λ_Δ, λ_Q, λ_DQ)` and its constitution; per ring the reaction material and `q` (the declared lock chart); `R`; the key covector as a reading | a `Deposit` staged inside the causal diamond | the pending ratio's and the target's | the pending binding | the ratio's faces (KL part, phase excess, winding); the residual against the emitted face; the loci reached |
| `deposit` | the successor constitution, in one atomic publication, or a `ConstitutionBudget` refusal that leaves the predecessor published | absent: a deposit consumes covectors | the applied `DepositReading`: the energy-growth bound `ε_k` and its running product, the commit, the successor's bits against the budget, the loci reached, the released residuals with their bits, and the entries stepped | unchanged | absent | the deposition work; the energy-bound product; the commit counter; the constitution's exact bits against its budget |
| `release` | the released face at width zero, or a refusal with its width | absent | the founded ring's material, when FOUND | the pending ratio's | the pending binding | the RIDE/FOUND split, its work form, and the width against the grain |
| `close_aeon` | the `AeonBoundary`: its `Collapse` (`V = ⊕V_g` as the retained and released loci, the `released_remainders`, the entries and bits), the descended constitution published in the resident, the pending ratios carried or refused (`carried`, `refused`) and the staged deposits refused (`refused_staged`) | `Vec<(PendingId, Transpose)>`: per pending ratio the transpose of `V` on it, or its separator | absent: the released loci are the boundary's collapse, read in the forward | each ring's aeon reading (windings, open phase) and the aeon's cells; the epochs, as section flux, are the boundary's `epochs` | the admitted family | `ReceiptDetail::Boundary`: the boundary is the forward, carrying the first-law split (`first_law`, `literal`), the released entries (structural, with the value kernel as a declared absence), and the constitution's and state's bits before and after |
| `discard` | the handle removed | absent | absent | unchanged | absent | the bits freed |

[definition] **Realization on the card (step 5, hardware law).** Step 5 realizes a method only
after its reference exists. No method has a global solve (review A6).
- **`ingest`** is an exact prefix scan of the integer steps `c_g(x_k)` with carries, then a
  histogram reduction into `M_g[phase]`. Both are associative, and the reduction commutes.
- **`locate_keys`.** Per ring, the keys and seed images are independent rows, each propagating along
  the menu's edges. The join is the fibre, a filter.
- **`refine`.**
  - Within a tick, every junction reads only its own arrivals and writes its own outgoing waves.
    Then every contact transits disjointly.
  - The ticks are the light's propagation: one hop is a causal dependency, not a serialization.
- **`compare`** runs the ticks in reverse over the `Word`'s own waves or checkpoints, with the same
  partition. Scatter-adds to shared endpoints reduce by addition.
- **`deposit`.** Disjoint loci commute, and the constitution is published once.
- **`close_aeon`.** The per-ring reach and observe recursions run in parallel rounds, one exchange
  with the neighbours per round, `e_last` rounds. Each ring applies its own `V_g`.

Each method reports its actual realization: one block per row, one thread per row loop, or parallel
work within a row.

### (d) The five campaigns, in order (reordered: keys lead)

Every campaign:
- lands its Lean laws first;
- cites #73 in its commits;
- updates the HNN row of the operator contract, its atlas rows and CONSTRUCTION_STATE;
- records one verification receipt in #73.

[definition] **The standing real cut (review E1).** One pinned development cut of the conversation
data (`.local/`, private, reported by scope and counts only), with held-out targets, is measured in
every campaign from campaign 1 on, against the same baselines (f). A campaign succeeds only by
beating the online order-0 held-out bits on it. Otherwise it records the failure with its located
cause (source, relation, encoding or decoder) before the next campaign begins. The synthetic
regression controls are controls, never milestones:
- the `ab`/`ba` six-cycle, recorded at 0/6 and 0.085 bits;
- the three-word edit.

#### Campaign 1. Keys, the change on a medium, and the collapse

- **Laws:**
  - Lean items 1–7, and the two retirements above.
  - In Rust:
    - closing rotor rings with screws, locks, reflectors and selective stepping on the port chart;
    - the phase-binned source moment on the source rings, the window and the pair port, with its
      capacity `n*`;
    - **key location leading learning:** the data → menu map below, propagation over the menu's
      edges, the fibre per ring in carry order, and gauge-fixed publication when a fibre is one
      orbit;
    - the local tick (junction Swing with one exponent per contact, ring element, contact
      two-port);
    - the word opening at zero change and releasing it at its end;
    - the receiving read at the receiver's grain;
    - the Holon ratio and covector;
    - the pending read from the anchor `λ`;
    - per-locus normal deposition, the preconditioned factor steps and the standing's deposit,
      inside the causal diamond, each carried on its locus's declared lattice with its remainder
      (Decision 22), under the constitution's bit budget and stop rule;
    - the collapse at the joint clock's carry-out, a learning aeon only, reaching the constitution
      and the pending ratios, then re-keying from the crib that closed it (review D1);
    - per-ring receipts in their own clocks.
- **Declared values (R2 M14; R3 D2).** Each is a key of the field, part of `Field::describe`. The
  primary declares each in #73 before any exposure, by the rule given, and never tunes one on
  held-out bits. [agent-inferred: each rule is the primary's choice with its reason; Brandon may
  override any.]

  | Value | Declared | Rule |
  |---|---|---|
  | Exterior chart | UTF-8 bytes, `\|A\| = 256` | the literal is `8n` bits, and the baselines use the same alphabet |
  | Rings | `G = 4` closing rings of periods 5, 7, 11, 13, carry chain in that order | prime periods (§8.5); at least 5, so each port chart splits the bytes into at least 5 classes; few and small, so `n*` stays far below the cut |
  | Contact graph | the 4-cycle 0–1–2–3–0, its one 2-cell the declared loop | the smallest graph with a loop in which every ring has two neighbours |
  | Channels | `ι_(a,g)`, `ι_(a,h)` match node `i` of both ends for `i < min(d_g, d_h)`, so `k_a = 2 min(d_g, d_h)` | full coupling on the common nodes; each `U_a` is a proper partial isometry |
  | `𝒮`, `R`, `A` | `𝒮 = {0}`, `R = 2`, so `e_0 = 2`; `A = 2`, so `e_last = 3` and `e_max = 4` | the receiver is the ring farthest from the source. With `A = 2` every element lies in the diamond; `A = 1` would release them all (the rim case) |
  | Locks `N_g` | `{0}` on rings 0–2, `∅` on ring 3 | each ring steps on about one cell in `d_g`, by port class. Ring 3 steps only by carry, so its carry-out, the aeon boundary, comes once per turn of the whole chain: 932–1,461 cells (mean 1,189) on uniform bytes, 920–1,834 on this repository's text. Each receipt reports the aeon's length |
  | Reflectors `F_g` | `p ↦ −p mod d_g` | the ring's own reflection: an involution whose one fixed point is 0 (every `d_g` is odd) |
  | Initial configuration | every ring at phase 0 | the fallback before any key is published |
  | Screws | one axis `e_z` through the origin for every ring, pitch 0; node `k` of ring `g` at the quarter turn `⌊4k/d_g⌋` of the unit circle, `(1, 0), (0, 1), (−1, 0), (0, −1)` (several nodes share one) | each node's phase `k/d_g` in turns read at the rational rotations of finite order, which in the plane are exactly the quarter turns ((a), "The period is combinatorial"). Integer placements make every quadrance an integer (`q_Q = 1`), and on one circle `Q_a ∈ {0, 2, 4}`. **Openness, declared:** the least source-to-receiver path attenuation `2^(−Σ_a β_a Q_a/2)` within `e_last` hops is at least the receiver's grain `1/L_R` on a majority of windows, measured by [`hnn_lattice_growth`](../../research/notebook/hnn_design/README.md) in release (the suite no longer builds the campaign field): 4,328 of the 5,005 phase configurations (`openness configurations`), 2,627 of the 3,074 receiving windows of `n*` uniform bytes, SplitMix64 from seed 0 (`openness uniform`), and 73,740 of the 85,877 receiving windows of the pinned cut, `docs/plans/THE_REBUILD.md` at `fed5488c`, 171,754 bytes (`openness cut`). The earlier sixteen integer points of `x² + y² = 65` spaced distinct nodes at `Q ≥ 4`, up to 260, and left the path open on 3.9% of windows (review C2), which no word test saw because every `Q = 0` at rest. The refine receipt reports each window's path attenuation. Pitch 0 keeps the class family finite across aeons: with a pitch, the relative winding of two rings stepping at different rates, and so `Q_a`, grows without bound over the cut, and every unlocked contact is shifted out. The pitch enters with the lock addresses in campaign 2 |
  | `β_a`, `L` | `β_a = 2`, the lattice generator `2q_Q/L`, with `L = 1`: `κ_a = 2^(−Q_a) ∈ {1, 1/4, 1/16}` | the least nonzero exponent on the lattice. With the quarter-turn placements it keeps an aligned contact whole and shields a misaligned path below the grain (the openness row above); a finer `L` would carry currents in `ℚ(θ)` |
  | `h`, `Y_g`, `Y_a` | `h = 1`, `Y_g = 2`, `Y_a = 2` | `2/h` for unit storage; `Y_a = 2c²/h` matched to the initial `C_a = I` |
  | Receiver grain | `L_R = 16` | its code tolerance of 1/16 bit per cell |
  | Offsets | `Δ = {1}`; a window of one cell | the least offset |
  | Steps | `γ_U = 1`; `η_x = 1/2` for every factor family, preconditioned by `h_x` | the pure normal solve; half of the preconditioned factor step |
  | Sign generator | entry `(i, j)` of locus `ℓ` is `+1` or `−1` by the low bit of SplitMix64 of `(0, ℓ, i, j)` | exact, deterministic and recorded; no float |
  | Crib | the `W_crib = 64` cells that closed each aeon (its last cells, already ingested and scored), at offset `δ = 1`, truncated after its last held-out cell | past cells only, so no key is learned from a cell later scored (review D1); well below the aeon; 63 edges per ring against at most 13 port classes |
  | `n*` | 6,148 cells | the counting formula above |
  | Cut | the standing real cut (Decision 23): `.local/cuts/standing-real-cut-campaign-1.bin`, written by `research/notebook/hnn_design/standing_cut.py`, the development stream's last 6,148 cells with the final 1,190 held out; population 6,148 = `n*`; recorded by scope and counts, its hashes in #73 | `Field::declare` refuses it if shorter than `n*`; the held-out cells are the stream's own later occurrences; the evaluation partition stays unspent |
  | Constitution budget | `B_Θ = 2^33` exact bits (1 GiB of numerators and denominators, statistics included) | the host reference's declared memory for the constitution |
  | Carrier lattices `L_ℓ` | `L_ℓ = ⌈log₂(2 L_R X_ℓ)⌉`: 9, 9, 10, 10 for the four rings' elements and standings; 10 for ring 2's `R`; 9, 9, 10, 9 for the four channels; `⌈log₂(32 · population)⌉` for ring 0's ports (22 on a cut of 2^17 cells; 23 on the notebook's pinned cut; 18 on the standing real cut of 6,148 cells) | `X_ℓ` bounds the ℓ1 norm of the operand one read of the locus sums: its fan-in (`2d_g`, `k_a`) for unit-scale waves, the population for the moment's counts. For the linear loci (`E`, `R`, `W_c`) a carried remainder then moves one read by at most `1/(4L_R)`, below the grain (`remainder_below_grain`), and a carried Gram stays positive definite. The factor loci enter the word quadratically or trilinearly (`C = ccᵀ`, `K = bbᵀ`, `D = FFᵀ`, `W_s = −ffᵀ`, the slices, the pair port), so the same `L_ℓ` does not give that bound for them: their product bound is part of the word-level certificate owed in #62. Never tuned on held-out bits (Decision 22) |

- **The initial constitution and its priors (R3 D2).** A linear locus starts at zero where another
  map carries its covector, and at declared signs otherwise. A square or product factor starts at a
  declared nonzero value, because at zero its covector vanishes and it would never move.

  | Locus | Form | Initial value | Update |
  |---|---|---|---|
  | `E_0` (`10 × 256`) | linear | 0 | normal law, `H_0 = I`, `B_0 = 0` |
  | `E_0^(δ)` | `Σ_(ρ<m) e_ρ (a_ρ·x)(b_ρ·y)` on the pair `x ⊗ y`, rank `m = 2d_0 = 10` | `e_ρ = 0`; `a_ρ`, `b_ρ` from the sign generator | factor steps on `e`, `a`, `b` (`E_0^(δ)` is carried in this factored form, R3 §5) |
  | `R` (`512 × 22`) | linear | sign generator, times 1/2 | normal law, `H_0 = I`, `B_0 = R_0` |
  | `W_c,g` (`2d_g × 2d_g`) | linear | 0 | normal law: feature the contrast `c_t`, covector the element adjoint's `u_t`; `H_0 = I`, `B_0 = 0` |
  | `W_s,g = −f_g f_g*` | square | `f_g = ½I`, so `W_s,g = −¼I` | factor step |
  | Slices `A_ρ,g = u_ρ v_ρ* − v_ρ u_ρ*`, `ρ < 2d_g`, rank 1 | skew | `u_ρ = e_ρ`, `v_ρ = e_(ρ+1 mod 2d_g)`; with every class `+1`, `Σ_ρ A_ρ,g` is the skew cyclic shift of the realified ring | factor steps on `u`, `v` |
  | `q_g` | the standing | 0, so every sheet class is `+1` | preconditioned step through the lock chart |
  | `c_a`, `b_a`, `F_a` | squares | `I`, `½I`, `½I`: `C_a = I`, `K_a = ¼I`, `D_a = ¼I` | factor steps |

  [agent-inferred: `E_0 = 0` makes the first faces uniform, exactly 8 bits per byte, and `R_0 ≠ 0`
  gives `E` a nonzero first covector; if both started at zero, neither would ever move.]
- **The exposure protocol:**
  - the cut is exactly the field's declared population, so the `n*` guard of `Field::declare`
    cannot be bypassed (`expose` refuses any other length; review D2); it is read in order, as one
    stream, into one moment;
  - keys: the first aeon runs on the declared initial configuration, since no cell has been seen.
    At each aeon boundary, after `close_aeon`, `locate_keys` runs on the crib that closed the aeon:
    its last `W_crib` cells, which were ingested and scored, truncated after its last held-out cell,
    and never before the aeon's opening. The configurations at the crib's opening are the
    boundary's lift stepped back over it (ring `g`'s advances depend only on the cells, the locks
    and the earlier rings' trajectories), and each published key is carried over the crib to the
    boundary (`keys::locate_closing`; review D1: a crib read ahead learned keys from cells then
    scored as targets, held-out ones included). The caller supplies the cells from the exterior
    stream; the machine keeps none;
  - at each receiving window, `refine` runs on the moment and `compare` runs against the next `A`
    cells. On the training part the return is deposited; then those cells are ingested;
  - the cut's pinned held-out targets are compared and reported, and never deposited;
  - the aeon boundary is the joint clock's carry-out (R2 M12).
- **The budget and stop rule (R3 §5; #62 "Step 4 (#73) owed").**
  - **The check.** `deposit` computes the successor constitution exactly and counts its exact bits
    (every numerator and denominator of `Θ`, the normal statistics included) before publishing.
  - **The refusal.** If the count exceeds `B_Θ`, `deposit` returns
    `HnnError::ConstitutionBudget { bits, budget, commit, loci }`, naming the loci that grew most.
    The predecessor stays published. Nothing is rounded, skipped or retried at a coarser grain:
    each deposit is carried on its locus's lattice with its remainder exact (Decision 22).
  - **What follows.** No further deposit is admitted. The run continues with `ingest` alone to the
    held-out part, where it runs `refine` and `compare` as declared.
  - **The report.** The run is reported as incomplete, with:
    - the stop's commit and cell count;
    - the constitution's bits per deposit up to the stop (the curve);
    - the held-out bits of the last published constitution.

    A timeout is reported the same way: an unfinished run at its deadline.
  - [established-bounded; measured] Under the exact law the chain control reached a budget in two
    or three deposits (1,126 → 10,883 → 623,415 bits). With the remainders kept exact on the
    lattice, campaign 1's declared field reached 250 Mbit after 21 deposits, at 21 s a deposit.
    Under Decision 22's refining remainder it grows from 0.19 to 1.37 Mbit over 40 deposits on the
    pinned cut, far below `B_Θ = 2^33`
    ([`hnn_lattice_growth`](../../research/notebook/hnn_design/README.md),
    `growth campaign 40 declared`).
- **Data → menu (review D2; R2 H4).** Run per ring, in carry order `g = 0, …, G−1`, with the existing
  `compression::keys` owners and addition 7:
  - **Ports** are `ℤ/d_g`, and the port chart `port_g(x) = code(x) mod d_g` is known before any key
    (R2 H4c, H4g).
  - **Edges.** Every pair `(x_k, x_(k+δ))` of the crib window that closed the aeon, at the declared
    offset `δ`, is an edge `port_g(x_k) — port_g(x_(k+δ))`, labelled by its position `k` counted
    from the crib's opening.
    - No admission depends on the key, which was the circularity (R2 H4a).
    - A pair the machine does not carry shows up as a failing loop. It is never filtered out as a
      non-crib.
  - **One stage per edge (R2 H4b, H4e).** The stage is the reflected return at the earlier cell's
    position, `ReflectorMachine::stage(position(key_g, steps_g(k)))`, with the ring's declared
    reflector `F_g`.
    - It is an involution, so an edge is traversed either way.
    - The rotor's advance between `k` and `k + δ` is not a stage.
    - A menu `Loop` is a closed path of edges, built with `Loop::new` whose closure computes the
      stages from the candidate key. So the menu is evaluated per candidate, never fixed in advance.
  - **Candidates (R2 H4f).** A candidate is `key_g ∈ ℤ/d_g`, the ring's initial clock, with the
    plugboard images at the menu's ports.
    - The lock `N_g` is declared constitution, not a candidate, so there are `d_g` keys per ring,
      not `d_g · 2^(d_g)`.
    - For `g > 0`, ring `g` is located under the earlier rings' published or fallen-back
      configurations, which fix the carries into it (R3 K3). A plural earlier fibre is not
      branched over.
  - **Propagation, not enumeration (R2 H4d).** Addition 7's `propagate` returns the fibre in
    `d_g × d_g × edges` steps.
  - **The gauge.** `ReflectorMachine::gauge` is checked by `Gauge::new`. It is exact on ring `g`'s own
    menu, and a later ring's carries may split an earlier ring's orbit.
  - **Publication.** When a ring's fibre is one gauge orbit, its gauge-fixed member is published:
    `S_g(p_0) = 0` at the least port `p_0` the crib's menu visits in ring `g`'s port chart, and
    exactly one member of each orbit satisfies it.
    - **The gauge convention is a declared symmetry-breaking choice (R3 K2).** The rotor gauge acts
      on every key, so the menu locates only the orbit, not `key_g`. The field ignores the plugboard
      in campaign 1, but it reads absolute phases through `P_R^(τ_R)` at the open and through the
      screw placements in `Q_a`. Two members of one orbit therefore give different fields, and the
      member with `S_g(p_0) = 0` is a convention, not a finding. The convention is recorded in
      `Field::describe`. [agent-inferred: making the field consume the key only through
      gauge-invariant quantities would remove the phase reading that selective stepping exists to
      supply.]
    - The plugboard images are reported. The field does not consume them in campaign 1, since the
      learned `E_g` carries what a plugboard would.
  - **Fallback (R2 H4h).** An empty fibre, reported with its minimal failing loop, or a fibre of
    more than one orbit leaves the ring at its current configuration (at the first aeon, the
    declared initial configuration), and the machine runs on that.
  - **Re-keying at an aeon boundary, and the open moment (R3 K1).** A key is the ring
    configuration at an aeon's opening. It is located at the opening of the crib that closed the
    previous aeon, and carried over that crib's ticks (under the configurations it was located with)
    to the boundary.
    - **Publication re-configures and never rewrites.** A published key sets ring `g`'s phase class
      in `λ` at the boundary, keeping its winding. It is not applied to any past cell.
    - **The open moment is untouched.** Its bins hold the phases the cells actually met under the
      configuration in use when they were ingested, and that is what the machine read. Nothing is
      recomputed, so no cell is needed.
    - **Why not rewrite.** Rewriting the past would need each past cell's step count under the new
      keys. A key change on ring `g` moves its wrap times, and so the carries into every later ring,
      for every past cell. Only the cells could recompute that, which would be a tape.
    - **The relative phase moves.** At the next open, `P^(τ_g)` reads the moment from the
      re-configured clock, so every past cell's phase relative to now moves by the jump. The receipt
      reports each ring's jump.
    - Pending ratios keep their producing anchor `λ`, a clock reading from before the jump.
  - [established-bounded; measured]
    [`propagation.py`](../../research/notebook/hnn_design/propagation.py), `d = 7`, cuts produced
    by a true machine:
    - the fibre always contains the truth;
    - 16 independent crib pairs pin it to the truth's rotor-gauge orbit (7 members), and the gauge
      fixing to one;
    - a `δ = 1` chain visits only 2–3 ports and leaves the fibre plural (35–42 members);
    - a random cut gives an empty fibre.

    Only the `δ = 1` chain rows use campaign 1's menu form, one stream at an offset. The
    independent-pair rows use two-stream edges `port(x_k) — port(y_k)`, which campaign 1's data →
    menu map never forms (R3 N1). On real text an empty or plural fibre is the expected first
    result, and the report is the finding.
- **Types:**
  - `Ring`, `Contact`, `Field`, `Constitution`, `NormalLaw`, `Current`, `SourceMoment`, `Word`,
    `ReceivingPhases`, `HolonRatio`, `RatioCovector`, `PendingRatio`, `Pullback`, `Deposit`,
    `AeonBoundary`, the ids and `Handle`, `ExecutionPort`, `Reference`;
  - the additions outside `hnn`: 1, 2, 3, 4, 6, 7 and 8.
- **Tests,** one per law:
  - **Keys:**
    - a declared rotor configuration is recovered from a synthetic crib as its full consistent
      family with its gauge, never as a point;
    - propagation equals brute force on every menu below `IMAGE_FAMILY_CEILING`;
    - the gauge fixing picks exactly one member per orbit;
    - a ring whose lock no input fits keeps its configuration;
    - adding an edge only shrinks the fibre;
    - an empty fibre falls back to the current configuration;
    - ring `g` is located under the earlier rings' published or fallen-back configurations;
    - re-keying at a boundary moves only `λ`'s phase classes, and leaves the open moment's bins,
      offset counts and window unchanged;
    - the crib that closed an aeon is stepped back exactly to its opening, and a key located there
      is carried over its ticks to the boundary; the port refuses a crib before the first boundary
      or longer than the closed aeon, and the exposure's crib holds no held-out cell (review D1).
  - **Moment:**
    - a per-cell ingest equals the clocked closed form under selective stepping;
    - for any rational encoder, `⟨M, E⟩ = m̃`, and the encoder covector equals its exact directional
      derivative;
    - `Field::declare`'s `n*` is the least `n` with `N(n) < |A|^n`, certified by exact integers at
      `n* − 1` and `n*` (137 on the three-ring control, 6,148 on campaign 1's field), and the
      declaration refuses a population shorter than it;
    - the window overwrites, and its bits are counted;
    - a rotation transport has no ingest port (`compile_fail`).
  - **Propagation:**
    - the Swing is an involution and a `W`-isometry;
    - the cone holds exactly;
    - with lossless elements and contacts and `W_c = 0` the global power `P` is constant exactly;
      otherwise it changes by exactly `−h Σ_a ω_a*D_a ω_a + (h/2)Σ_r Y_r⟨x̄_r, W_s,r x̄_r⟩ + Π_c`;
    - `U_a` is a partial isometry whose reverse is `U_aᵀ`, and the untransmitted part reflects;
    - a declaration with a per-ring exponent is refused;
    - on a small field at a nonzero class configuration (not at rest), the path attenuation is
      computed exactly and compared with the grain `1/L_R`; campaign 1's openness on a majority of
      windows is a notebook measurement with its committed command (review C2; the testing
      protocol).
  - **Reaction:**
    - with skew slices, `½|y′|² = ½|y|²` exactly;
    - with `W_s ≠ 0`, the midpoint balance holds;
    - with `W_c ≠ 0`, the drive balance holds exactly, and some input makes the contrast port's
      power positive;
    - a complex-bilinear block is refused at declaration.
  - **Word adjoint:**
    - `⟨g, T v⟩ = ⟨T* g, v⟩` exactly up to the logits `f`, with `T` the separately implemented
      tangent map;
  - **Ratio:**
    - the real covector is `p̃ − q` in the declared odometer chart, and `⟨p̂ − q, p̃ − q⟩ > 0`;
    - the phase covector is `−q_c Δ_c` in turns on the windowed gap, the cut's winding its branch;
    - a byte target's phase is `(τ_R(j) − d_R w)/d_R` in the cut's frame, `w` its branch, from
      selective stepping over the targets, and ingesting those targets afterwards reaches the same
      `λ_R`;
    - over a long stream (6,000 cells of the chain control, `τ_R/d_R` past 100 turns) every window's target phase stays
      in `[0, 1 + 2A/d_R)` and the phase covector below 1 (review C1);
    - a common rechart leaves `ℓ` unchanged;
    - `CarriedPower` normalizes exactly, and the face is constant on its fibre;
    - reading every exponent down moves each cell's code length by less than `1/L_R`.
  - **One cut:**
    - with intervening refines but no deposit, a delayed `compare` equals the immediate one exactly;
    - after a deposit, it returns the residual against the emitted face;
    - a word opens at zero change, whatever preceded it.
  - **Deposition:**
    - the prox-step identity holds at the carried operands, and the carried Gram and map move by
      exactly their updates (value plus remainder);
    - division with remainder is the nearest lattice point, ties upward; deposits keep every entry
      on its lattice and every remainder in its half-open cell;
    - applied + carried + released = the exact sum of the updates, over real deposits; the released
      total of each entry stays below half a unit, and a carried remainder's bits within
      `L_ℓ + 2k_m + 1 = L_ℓ + 4⌊log₂ m⌋ + 3`; the collapse leaves the remainders and deposit counts of retained
      loci;
    - a locus outside the diamond is unchanged, and a normal statistic sums only over its diamond
      window;
    - a deposit whose successor exceeds `B_Θ` is refused with `ConstitutionBudget`, and the
      predecessor stays published;
    - `C_a`, `K_a` and `D_a` stay PSD under every update, with no clamp;
    - reaction deposits have `ε_k = 0`;
    - `q` changes only by deposit, and a sheet class only across zero.
  - **Collapse:**
    - every admitted reading is identical before and after, exactly, with every released item
      replaced by arbitrary values;
    - the recursions release exactly the loci the diamond rule names, and replacing any one retained
      item changes some reading: on the six-ring path, 72 of 156 entries at `A = 2` and 132 at
      `A = 1`, as in `release.py`;
    - `deposit_descends`: collapsing then depositing equals depositing then collapsing;
    - `V` deletes whole loci;
    - a pending ratio that does not factor is refused, naming its separator;
    - `close_aeon` is refused except at a carry-out, and refuses an admitted family larger than the
      previous boundary's.
- **Done when:**
  - the laws and tests above pass;
  - `bash tools/lean_check.sh` passes with `HNN` in the Framework;
  - on the standing real cut, these are reported:
    - per ring, the key fibre: its size, gauge orbits, failing loops and whether it fell back;
    - the held-out bits on `p̂` against the baselines, beating online order-0 or recording the
      located failure;
    - the state bits per source bit, with and without the collapse. They are equal on the declared
      field, whose diamond covers it, and the collapse is exercised by its synthetic tests;
    - the constitution's bits per deposit (#62, "Step 4 (#73) owed"), and the budget stop when it
      comes, as an incomplete run with its curve;
    - each aeon's length and each ring's re-keying jump;
    - the moment's bits against `n*`;
    - the released dimension at each aeon boundary.

#### Campaign 2. Rings and contacts store, lock and flow

- **Laws:** Lean item 8, and:
  - each ring is a complex parametron: `C_g = Bᵀ W_C B`, `K_g = Bᵀ W_K B`, with modes
    `K v = ω² C v`;
  - its tick conserves the mode energy;
  - its section crossing is its clock tick, and phases advance inside a word (R2 M6). Each change
    of a port's reference admittance between ticks is applied as the mismatched two-port
    reflection `Γ = (G_old − G_new)/(G_old + G_new)`, `T + Γ² = 1`, so the power stays exact;
  - multi-rate rings form an `EpochTower` with the Kac grain ratio;
  - the pump `−p cos(2θ − ψ)` is blind to the half-turn sheets, the sheets carry the Ising lock, and
    the perceptron is one receiver face;
  - the contact's constitution resonates at `ω_a² = K_a/C_a`, folds where `K_a` crosses zero and
    breaks in the boost region (Griffith). Its site kind is read each word.
  - Boosts `K_a ⋡ 0` are admitted from here (R2 H3). `K_a` is then carried unsquared, and:
    - a declaration or deposit that makes `M_a` singular is refused with its singular direction;
    - the expanding part is released at the word's end like all of the change;
    - the balance is stated with the indefinite storage.
  - a locked contact `q v_a = p v_b` has its Farey address, and the mediant is the cheapest lock
    between neighbours;
  - two ring clocks lock at their address, and otherwise their natural epoch grains are the
    convergents (`aeon::TwoClocks`);
  - the field's committed balance is exact. The word's power balance is exact per word, with the
    contrast ports' power `Π_c` stated, and passivity is proved per word wherever every `K_a ⪰ 0`
    and every `W_c = 0`;
  - the reaction material is factored through its bilinear cores and the mode quotient. In the
    prototype this material was 95% of the state (D6).
- **Tests:**
  - the ring tick conserves the mode energy exactly;
  - the ring's clock ticks equal `ring_crossings`;
  - the pump is blind to the sheets;
  - the contact's site kind follows the sign of `K_a`;
  - lock addresses and mediants are correct;
  - two locked clocks read whole windings on every cycle;
  - the whole-field balance residual is exactly 0 at every word.
- **Done when**, on the standing real cut:
  - the held-out bits are reported against campaign 1 and the baselines;
  - the contact site-kind census after learning is reported (rotation, null, boost);
  - the balance residual is exactly 0 at every word;
  - state bits per source bit are reported against campaign 1.

  Pump/Floquet locking stays open in #62.

#### Campaign 3. Release through modes, dormancy and far fields

- **Laws:** Lean item 9, and:
  - **Dormant rings.** Two receiver families are declared: the exterior receiving family and the
    admitted future family that contains it.
    - A dormant ring's mode is retained standing, not a persisting wave (Decision 1):
      - its constitution and lock, which the collapse keeps when an admitted cycle receiver reads
        them through some admitted word;
      - its clock in `λ`, which keeps winding. That winding is the persistent interior motion in
        the fibre that `Objects/RelativeCompleteness` asks for.
    - A fitting antecedent excites the mode within a word.
  - **Release through modes** over the rings' rational components.
  - **Founding** by interconnect from the cokernel residual, within capacity.
  - **Release** at width zero at the receiver's grain.
  - **Far-field moments:** the moment's quotient against the receivers, and `Δ` derived from it.
  - **Frozen aeons (R3 R4).** An aeon that admits no deposit may release the value kernel of its
    constitution. Its descended blocks no longer have the junction, Cayley or two-port form, so
    this campaign first specifies how a descended block ticks, and only then admits the frozen
    aeon.
  - Participation is compressed into (mass, current) classes where they are kernel-equivalent
    (`Computation/AttentionModeCompression`).
- **Tests:**
  - a dormant ring survives an aeon boundary and is read later by a cycle receiver, the
    later-phase separator of #62 item 6;
  - a released part changes no admitted reading;
  - the split is `C`-orthogonal per component;
  - a founded ring reaches its cokernel face;
  - an offset no receiver reads is dropped at the boundary.
- **Done when**, on the standing real cut:
  - dormant rings are kept across boundaries and read at held-out positions, with the bits at those
    positions reported with and without them;
  - the released and founded counts are reported against capacity;
  - the held-out bits are reported against campaign 2 and the baselines.

#### Campaign 4. The motor chart: serial screw words

- **Laws:** Lean item 10, and:
  - a `SerialChain` of situated screws is a source and receiver chart of the same field;
  - its Jacobian columns are the recharted Lie generators;
  - a receiving wrench returns to the joint rates by the transpose;
  - a requested face's joint fibre stays plural where it is.
- **Tests:**
  - the endpoint is the ordered product of the joints;
  - `⟨w, Jθ̇⟩ = ⟨Jᵀw, θ̇⟩` exactly;
  - a requested face returns its complete joint fibre and residual;
  - no simulator is involved.
- **Done when:**
  - on a pinned real motion recording (exterior data: a public motion-capture clip whose skeleton is
    a serial chain, read into ℚ at its recorded precision), the held-out endpoint faces are reported
    against a constant-velocity baseline, with fibre, residual and units (rad/m, m, W);
  - the standing text cut is re-measured and shows no regression.

#### Campaign 5. Holonic Encoding, context and joint prediction

- **Laws:** Lean items 11–12, and:
  - `E` is a learned boundary element relation, with `D E = ρ` and `E_next T_a = U_a E` for each
    declared action. Where one fails, its separator is kept;
  - the grain comes from the interaction and the receiver (`JointReceiverDescent`);
  - the context is the causal cut restricted to the admitted receivers;
  - `Γ_m` is one joint refinement read at `m` stations, released through campaign 3's law;
  - a participating receiver reads through `JointLaw::interact`.
- **Tests:**
  - each square holds or returns its separator;
  - changing the exterior alphabet leaves the ring count and widths unchanged;
  - `Γ_m` differs from the product of its marginals on a parity witness;
  - a text receiver reconstructs valid Unicode through its receiving relation.
- **Done when**, on the standing real cut with Holonic Encoding replacing the exterior cell chart:
  - the held-out bits are reported against every baseline;
  - `Kt` against the literal is reported;
  - state bits per source bit are below 1 on the population;
  - the outputs, including failure outputs, are read and shown.

The standing retrospective cases are the pinned exposure, the 773–776 restart control, events
3406683 and 3398355, and the complex-product code case. They are the acceptance of step 8, and no
campaign control replaces them.

### (e) The port map

[definition] The history paths are under `crates/holonics-cuda/src/` at `13f8c734` unless noted,
with `NE` for `native_ecology/constitutive_fibre/field/` and `INC` for
`hnn/coupled_wave/body/field/incident/`. Each port is recorded in #73 as history path → new owner →
law → test.

| Law | Ported from | New owner | Dropped |
|---|---|---|---|
| Moment, composite powers | `INC/machine_source.rs` (`MachineSourceMaps::{apply, moment, anchor}`) | `hnn::moment` | the episode type and its per-episode clocks; moments on non-closing transports; the resident coefficient section (step 5) |
| Directed and offset source ports | `INC/machine_source_contacts.rs` | `hnn::moment` | per-edge relation retention; the `.pairings.json` sidecar; offsets on the learned chart |
| Delayed comparison at the contemporary constitution | `INC/machine_episode.rs` (`RetainedComparison`, `contemporary_word`) | `hnn::{pending, reference}` | `GeneratorEpisodeTape`; the per-occurrence word; the legacy-slot prepared boundary; the frozen-word and tape decoders |
| The incident word | `hnn/coupled_wave/body/field/incident.rs` | `hnn::{word, propagation}` | `ReactionLaw::Legacy`; the geometric `Φ(y,p)`; operands re-read from the evolving state each tick; the persisted solver choice; device ball radii (step 5) |
| The word's energy chain | `INC/energy.rs` | `PortReceipt::balances` (`hnn::propagation::TickBalance`) | its `f64` readings |
| The machine as a core Holon | `INC/holon_chart.rs` (`ResidentHolonChart`) | `Field::holon()`, read-only | resident packets; the delegation table |
| Receiving phases | `INC/machine_receiving.rs` | `hnn::receiving` | the `response_port_start` slot semantics |
| Machine declaration and charts | `hnn/field_geometry/{machine.rs, machine_factor.rs}`, `INC/machine_transport.rs` | `Field`, `Ring`, `Contact`; Lean `GeneratorMachineCharts` | the width-12 realification as a type; the untagged legacy spelling; `GeometricFieldSpec` versions |
| Scattering and its adjoint | `NE/junction/operative/source/{reflection.rs, reflection_target.rs, reflection_commit.rs, map_action.rs}` | `hnn::propagation`, as the junction Swing | **the global solve** (§8.1; it survives only as the continuum-limit reading); the dense source factor; `recent_producers`; the frozen-cut replay |
| Contact material | `NE/junction/operative/source/action/{contact_amplitude.rs, contact_scale.rs}` | `Contact`'s constitution, `Deposit` | the scalar amplitude `ρ_a` as the contact's whole material (§8.6); the word "template"; the dyadic upward projection (the factor carriers are PSD by construction) |
| Material factor return | `NE/junction/operative/factor_return.rs` | `Deposit` | the `returns` journal; `NativeConstitutiveField.history` |
| Normal law | `NE/material_transport/normal/{direct.rs, constitution.rs}` | `NormalLaw`, per locus | the dense support normal (1,537 × 513, 1.865 GB); the zero-mean-prior legacy meaning; the legacy validator |
| Normalized receiver and pullback | `NE/receiver/normalized/{section.rs, pullback.rs, phase.rs, pair.rs}` | `hnn::{ratio, receiving}` with `CarriedPower` | committed faces; the imaginary slot written as zero; the alternate `ExponentialPotential` and `PacketModulus` faces |
| Equal-drive internal mode | `NE/internal_mode.rs` | campaign 3's dormant-ring test | its separate refusal path |
| Complex parametron | `cuda_refine/complex_parametron.rs` | already `holon::parametron`; consumed by `Ring` from campaign 1 | device refinement (step 5) |
| Pair contact and serial chain | `holonic_interaction/helical.rs`, `holonic_chain/serial.rs`, `exact_contact.rs` | already `holon::contact`; consumed by `Contact` and `MotorChart` | — |
| Factored moment storage | `factored_moment/{storage.rs, section.rs, spine.rs}` | `NormalLaw` storage; campaign 2's reaction factorization | the card layout and the membrane shell kernels (step 5) |
| Observable-moment reuse and descent | `receiver_history_compression/{observable.rs, compression.rs, factored_forms.rs}` | `hnn::{retention, encoding}` through `compression::{FaceMap, Retention}` | `projective_history.rs` and `membrane.rs`, which have no consumer |
| Kernel-mode reduction | `crates/holonics/src/exact_linear/kernel_modes.rs` at `551d6c5d` | campaign 3's participation classes | — |
| Presentation cost, Landauer, winding inertia | `presentation_cost.rs`, `landauer.rs`, `winding_inertia.rs` | readings only: `CompressionCost`, `ExactWork`, bits | the energy and erasure axes, unknown until an energy receiver exists |
| Rest and delivery | `INC/rest.rs`; the stream and its drivers | not step 4: `Field::describe` is the one exact code | every layout and decoder tagged `\x01`, `\x02` or `\x05`; the session kinds |

[definition] **The do-not-port list, line by line.**
1. **The per-occurrence tape and frozen-cut replay.** In history these were `GeneratorEpisodeTape`,
   `evaluate_generator_episode`, the `\x01`/`\x02` rest tags, the frozen-cut replay of
   `reflection_commit.rs`, and the ordered tape of Lean `GeneratorSourceEpisode`. They are excluded
   by the moment law and by guards 1–3.
2. **`returns` journals and completed-update archives.** In history these were `returns.push`,
   `NativeConstitutiveField.history`, `recent_producers` and Lean `ContactAmplitudeState`. They are
   excluded by guard 4.
3. **Slot, session and episode wires.** In history these were `response_port_start`, the session
   owners, the `HnaStream` session kinds and the `athena_*` drivers. They are excluded by the verbs
   of the port.
4. **Byte and nibble codecs.** They are excluded by guard 9.
5. **Q/K/V caches and foreign forward graphs taken whole.** Participation is the Swing's anchor over
   the field's own contacts, and the offset window is a ring. Equation extraction is step 6.
6. **Any Lean in the HNN pipeline.** Excluded by guard 7.
7. **Floats inside a law.** Excluded by the exact charts and by guard 12.
8. **Global instantaneous solves** over the contact graph. They are excluded by the local tick and
   guard 14 (§8.1).
9. **Rounding inside a law:** committed faces, rebases to a carrier grain whose dropped residual is
   unaccounted or unbounded (history's per-commit centres, whose dropped radii summed without
   bound), and enclosures standing in for a chart. They are excluded by `CarriedPower` and guard 15
   (§8.4). The lattice deposit (Decision 22) is a representation with its decoder and residual:
   applied + carried + released is the exact update, and the released total stays below half a
   unit over every aeon since the locus's founding.
10. **Lossless source accumulation on a non-closing ring, or below capacity presented as lossy.**
    Excluded by guard 1 (§8.5; R2 H1).
11. **A change carried from word to word:** history's published `s′, b′` endpoint and every
    wave-carrying current. Excluded by guard 16 (R2 C2c, C3).

### (f) Measurement

[definition] **How a run is read.** Every number comes from an `InteractionReturn` and is reported
with its units, population and clock. The host reference's exposure (`Reference::expose`) gathers
them into one readout, `hnn::reference::Exposure`, whose fields are named below.
1. **Bits, on the face the adjoint consumes.**
   - `L_target|model = Σ_j −log₂ p̂_j(t_j)` is exact on the face `p̂` at the receiver's grain, with
     its fibre `ε` reported. It is split into its KL part and phase excess, with the winding.
   - The baselines are fitted online on the same exposure with a declared prior (review E2):
     - order-0 and order-1 with the Krichevsky–Trofimov prior;
     - PPM (order 2, exact, in `hnn::reference`);
     - xz and zstd bits per character, with their description cost: computed outside the crate
       (no processes in `holonics`), owed to the application that runs the exposure.
   - Failing to beat online order-0 is reported as a failure.
   - One face serves learning, selection and report (D4).
2. **The first law of learning over an aeon.** `ΔC = exchange + deposition` (aeon A7), with the
   released part counted as exchange, through `aeon::EnclosedLedger` (the enclosed first law; Lean
   `Aeon/Production/FirstLaw.{ledger_telescopes, ledger_is_first_law, enclosed_contains,
   enclosed_telescopes}`). Beside it, the face's comparison
   with the literal per aeon: `Σ_k ℓ_k + Σ_k g_k = n·log₂|A|`, exact algebra whose `g_k` is negative
   wherever the face predicts worse than uniform, so it is a reading, not a budget ([the perceived-difference record](../../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md)).
3. **Cost against the literal (review E3).** `Kt = |Field::describe()| + K_keys + L_target|model + ⌈log₂ ExactWork⌉`.
   - The first term is the model, the second the located keys (`⌈log₂ d_g⌉` per published key: what
     learning located is paid for; review D1), and the third item 1's bits.
   - The literal is `⌈log₂|A|⌉ · n`, and the pivot pays off exactly when `Kt` is smaller.
   - Over a declared population the description is paid once.
4. **State against source, in bits.**
   - The exact bit lengths of the `Current`, the `SourceMoment`, the open pending ratios and the
     constitution.
   - State bits per source bit, with and without the collapse.
   - The moment's total bits per source bit against its capacity crossover `n*` (R2 H1).
   - The constitution's bits per deposit by carrier (entries, remainders, solved charts), against
     Decision 22's bound, and the released tails' bits: the exposure's `constitution_curve`, one
     `CurvePoint` per published commit (the mount's first): its `commit`, its `CarrierBits`, and the
     reaching deposit's `released_bits` and `stepped` entries (zero at the mount).
   - The peak bits inside a word, which bound the change: `peak_word_bits`, the largest
     `ReceiptDetail::Refine::peak_bits` over the exposure's refines.
   - The released bits and dimension per aeon.
   - Coordinate counts stay flat in `N`, and the bits are the test. The baseline is the prototype's
     2,936 bytes at `N = 2`–128.
5. **Work, time and rates (review E4).**
   - The `ExactWork` of each method.
   - `N_face/dt` and `N_update/dt` per receiver clock (objects §10).
   - Wall time is an exterior face recorded with its clock.
   - Cold setup, generation, update, ingestion, rest and egress are reported separately.
6. **Locality.** The loci reached per deposit (the diamond), each ring's tick count, and the cone
   per word. Beside them, the openness of the source-to-receiver path (review C2): `open_windows` of
   the `windows` read, the receiving windows whose refine receipt's `PathAttenuation` was open at
   their cut, so a shielded receiver is reported as a located cause.
7. **Numerical health.** The receivers' fibres, and the device's ball radii and residual
   certificate (step 5). No committed-face residual exists.

[definition] **Unknown is not zero.** The following are reported as unknown whenever no receiver
counted them:
- energy in joules and device power;
- bits per joule;
- occupancy, and any other counter nothing counted.

A timeout is an unfinished run at its deadline.

| Campaign | Declared receiver | Success |
|---|---|---|
| 1 | The receiving faces on the standing real cut; the menu's loop-closure faces; the law tests | Every law identity holds exactly. The key fibre is reported with its orbits and failing loops. The held-out bits beat online order-0, or the failure is recorded with its located cause. State bits are reported with and without the collapse, the moment's total bits against `n*`, and the constitution's bits per deposit. |
| 2 | The same cut; the ring mode-energy face and the whole-field balance | The balance residual is exactly 0 at every word. The site-kind census and the held-out bits against campaign 1 are reported. |
| 3 | The same cut; a cycle receiver | Dormant rings are kept and read later, with their bits reported. Release is at width zero or refused. The held-out bits against campaign 2 are reported. |
| 4 | A pinned real motion recording; the same cut | A requested face returns its complete joint fibre and residual. The held-out endpoint faces are reported against constant velocity. The text cut shows no regression. |
| 5 | The same cut through Holonic Encoding; the two squares | Each square holds or returns its separator. The held-out bits are reported against every baseline. State bits per source bit are below 1, and the outputs are read. |

[project-postulate] **No benchmark theatre.**
- A regression control is never the milestone (D8), and the standing retrospective cases keep their
  failed status until step 8 changes it.
- Every product number carries its baselines, units, population and failure count.
- No scalar of progress is formed.
- A number that no run produced is not written.

### (g) Guards that make the rejected forms impossible

[definition] Each rejected form is excluded by a construction. A type construction is proved by a
rustdoc `compile_fail` doctest, which needs no new dependency. Lints are enforced by
`#![deny(clippy::float_arithmetic, clippy::disallowed_types, clippy::disallowed_methods)]` in
`hnn` and by `crates/holonics/clippy.toml`'s `disallowed-methods` and `disallowed-types`; the
receipt runs `cargo clippy -p holonics --all-targets -- -D clippy::disallowed_types -D
clippy::disallowed_methods -D clippy::float_arithmetic`. Each `compile_fail` doctest states its
error code, checked with `RUSTC_BOOTSTRAP=1 cargo test -p holonics --doc hnn` (stable rustdoc
ignores the codes), and says whether its guarantee is structural. No guard is a source-text scan
(review A8).
1. **No tape in the moment; no lossless source below capacity presented as lossy (R2 H1).**
   - `SourceMoment` is sized once, from the `Field`, and accepts closing source rings only. A
     rotation transport has no ingest port (`compile_fail`).
   - `Field::declare` computes `n*` by the counting formula, on exact integers, and refuses a
     declared population shorter than it.
   - A capacity test checks the count, not one slot's bits: `log₂N(n)` per source bit is at least 1
     below `n*` and below 1 past it, at `n` = 2 … 4,096 on the three-ring control (R3 H1).
2. **No word outlives its return.** `Word<'c>` borrows `&'c Field` and owns its tick operands.
   `pull_back(self, …)` consumes it, and it is not `Clone`. No field of `Field`, `Current`,
   `PendingRatio` or `InteractionReturn` has a lifetime parameter (`compile_fail`).
3. **A pending ratio holds operands only:** the anchor `λ`, `M`, the `ReceivingPhases` and the
   commit.
   - No constructor accepts a material, a word or a face.
   - The resident owns it, and `compare` consumes its id when it succeeds.
   - `refine` refuses beyond the pending capacity.
   - The one other operand the resident keeps across methods is the first law's `Arrived` ((c),
     "The host reference"): the last compared pending ratio with its `A` target cells. There is at
     most one, the next compare replaces it, it is counted in the state bits, and only the ledger's
     deposition and release steps read it.
4. **No journal.** `Constitution` holds only the current parameters, the normal statistics, their
   carried remainders and each locus's deposit count: no list of deposits, updates, gradients or
   producers. Its fields are private. `deposit` and the
   collapse are its only mutators.
5. **Retention only by the collapse, only at aeon boundaries.** `close_aeon` is the only operation
   that reduces the constitution, and the resident accepts it only at the joint clock's carry-out
   (R2 M12). An aeon is carried by its lift point, `O(G)` integers.
6. **No clock outside the lift point and the word's hop clock (R2 L3).** No `hnn` type holds a clock
   except `λ` in `Current` and the word's own `navigator::Clock` in `Word`, which is structural in
   the type definitions. The one sanctioned exception is key location's fibre of clock-keyed
   candidates (`RingKeys::fibre`; "Candidates" in the data → menu map), a reading of
   `locate_keys` that no state keeps. That aeon, epoch and cycle are the only time words is a
   review rule, not a type guarantee, and no identifier scan runs.
7. **No Lean in the pipeline.** `holonics` keeps its four dependencies, and `clippy.toml` disallows
   the `std::fs` and `std::process` entry points, denied in `hnn` (an exterior notebook allows
   them where it reads).
8. **No templates.** Output faces are `ρ_R` readings, and no port method returns a string.
9. **The codec is not the architecture.** `Field::declare` fixes the ring count and widths without
   the exterior alphabet. A test changes the alphabet and checks that they do not change. The
   stepping classes are not covered by that test: `port_g(x) = code(x) mod d_g` lets the codec's
   integer numbering choose the lock classes, so they are a codec-dependent exterior chart until
   campaign 5's Holonic Encoding replaces it (R3 §4).
10. **No scalar operand.** `Word::pull_back` accepts only a `RatioCovector`, which only a
    `HolonRatio` constructs (`compile_fail`).
11. **Learning is locating keys and depositing covectors,** never "a current changes a later
    current's standing". Keys change only through `locate_keys`. The constitution, the standings
    `q` included, changes only through `deposit` of a `compare` return and through the collapse
    (Decision 1). `refine` has no path to it.
12. **No floats.** `#![deny(clippy::float_arithmetic)]`, and `f32`/`f64` are disallowed types.
13. **No compatibility.** There is one exact code, `Field::describe`; no legacy reader, alias or
    `Legacy` law arm.
14. **No global solve (§8.1).** `propagation.rs` exposes only junction-local solves. A cone test
    checks that an impulse at any ring is supported within `t` hops after `t` ticks, exactly.
15. **No rounding (§8.4).** No API returns a committed centre. The only grain reading is
    `CarriedPower` at a face, which returns the carry, the phase class and the fibre. No port method
    takes a free tolerance: `release` reads its receiving phases' grain, and the collapse releases
    only exact complements (R2 §2), never a carried remainder. A deposit's released tail is fixed by
    the locus's deposit count, reported in its receipt, and bounded over every aeon since the locus's founding
    (Decision 22). A constitution over its bit budget is refused
    (`ConstitutionBudget`), never rounded (R3 §5).
16. **No change outlives its word (R2 C2c, C3).** `Current` has no wave or contact-state field.
    Waves and contact states are fields of `Word` only, created at zero by its open and dropped at
    its return (`compile_fail` on building a `Current` from a `Word`'s waves).

### Decisions

Each settled decision and its source (R3 H5). Two kinds of source are distinguished:
- **Brandon's ruling:** his words, with their date, where one applies.
- **Agent-inferred:** the primary's inference. "From the derivation (record §8.n)" means the light
  record's §8.n, inferred from Brandon's September 24 derivation; he stated none of §8 as a step-4
  ruling, and the record says so. Brandon may override any agent-inferred decision.

1. **The medium changes only by deposition, and at an aeon boundary by the collapse.** The change's
   bound part is not absorbed into the standing. The consequences:
   - `q` is part of `Θ` and moves only by deposit;
   - `refine` publishes only faces;
   - a word opens at zero change and releases it at its end.

   Source: Brandon's ruling that deposition is the only law changing a constitution
   (ELEMENTARY_OBJECTS §8, "Deposition is the only law by which a constitution changes", in the
   objects he cemented on September 22), and his September 22 objection, "Why are we vaguely
   attributing 'learning' to 'something changes something else later' again". The consequences
   are agent-inferred from the derivation (record §8.2, "changes, not states"). It answers R2 C3
   and R2 §6 item 2.
2. **Campaign 1 runs with selective stepping, and participation is fixed by keys**, learned only
   through keys.
   - Given the classes, the response is linear in the moment.
   - Nonlinearity enters only through the key and lock classes: ring phases, notches, sheet
     classes, and the receiver's grain. They are finite within an aeon, and across aeons at
     campaign 1's declared pitch of zero.

   Source: Brandon's ruling that learning is locating keys, in the objects he cemented on
   September 22 (ELEMENTARY_OBJECTS, keys: "Learning is locating keys: inferring the configuration
   and gauge of relevant navigators from loop-closure constraints"), with his Enigma/Bombe reading
   of September 21. The capability consequence
   (the response linear in the moment given the classes, participation not learned in campaign 1)
   is agent-inferred from the derivation (record §6 and §8). It answers R2 §3.1–3.2 and R2 §6
   item 1.
3. **Local propagation.** A change moves one contact per tick, inside a causal cone of speed one
   hop per tick. There is no global solve, and the connection heat equation is only the continuum
   limit (review A1, B3).

   Source: Brandon's rulings: September 1, "The way that 'weights' … are updated is a propagating
   local thing"; September 11, "their states are determined by particles around them and
   propagating waves, not by spooky action at a distance"; September 22, "my brain's regions … are
   only affected by the propagating action that would reach the independent region". The tick's
   form is agent-inferred from the derivation (record §8.1).
4. **Changes, not states.** The word propagates differences on a medium whose operands are fixed at
   the cut, and a receiver reads the front at its epochs.

   Source: agent-inferred from the derivation (record §8.2), whose words are "the geometry is one
   thing but the light we see is the change itself".
5. **Participation is the junction Swing's anchor, with one exponent per contact.** One operation
   is both normalized participation and `2P_D − I`, and the global power is conserved exactly with
   lossless elements and `W_c = 0` (measured).

   Source: agent-inferred from record §8.1 and the Swing of objects §3 (R2 C1).
6. **Retention is the collapse onto what the admitted future distinguishes** at aeon boundaries,
   and the change is released at every word's end.
   - It releases only the exact complement: the time-indexed causal diamond and structural rank,
     in learning aeons only; the value kernel is a reading, and frozen aeons move to campaign 3.
   - It is per ring, it reaches the constitution and the pending ratios, and a deposit commutes
     with it (`deposit_descends`).
   - The collapse releases no carried remainder (a remainder is not an exact complement). The
     deposited constitution's bits grow logarithmically by Decision 22; the word-level certificate
     of the lattice rule stays open in #62 ("Step 4 (#73) owed").

   Source: Brandon's rulings that retention is a quotient sufficient for the admitted future
   (CLAUDE.md §1, "Retention is a quotient sufficient for the admitted future"), and September 10:
   "I don't store the exact picture of how a fucking song sounds in my mind I remember the key
   parts of the waves". The collapse's form is agent-inferred from the derivation (record §8.3;
   review C3, D4; R2 C2, M3–M5; R3 R1–R4).
7. **Exact inside, grain only at the face.** `s = n + r` is carried as a carry and a phase class in
   `ℚ(θ)`, the sub-grain remainder is the receiver's fibre, `L_R` is derived from the receiver's
   code tolerance, and nothing is committed (review A2, B1, B2, C1; R2 M2).

   Source: Brandon's rulings: August 18, "a sort of holonic softmax interpretation involving
   modulus/remainders"; August 27, "we do not fuck with floats internally"; September 23, "we
   literally just don't ever collapse into approximations that destroy information (no floats)".
   The chart is agent-inferred from the derivation (record §8.4).
8. **Rings close by default.** Campaign 1 admits no rotation ring, and a closing ring's moment is
   lossy only past its capacity `n*`, which the declaration computes by counting (review A3, B5;
   R2 H1; R3 H1).

   Source: Brandon's ruling of September 3, "The idea of 'retained lookup' or 'lossless corpus
   encoding' is literally wrong and problematic". Prime periods and the capacity rule are
   agent-inferred from the derivation (record §8.5).
9. **The contact carries its own constitution** `(C_a, K_a, D_a)` as a midpoint two-port on a
   partial-isometry channel. `K_a ⪰ 0` in campaign 1, and boosts come from campaign 2. Rings carry
   screws, and the score is the pair quadrance of the two screws (review B6, C5; R2 H3, M8).

   Source: the pair contact and parametron are elementary objects Brandon cemented on
   September 22. The contact's constitution is agent-inferred from the derivation (record §8.6).
10. **Keys lead from campaign 1.** Key location is propagation over the menu's edges, per ring in
    carry order under the earlier rings' published or fallen-back configurations, with declared
    locks, reflectors and port charts. The fallback is the current configuration. A key is
    re-located from the crib that closed each aeon (past cells only, never a held-out one; review
    D1), re-configuring the clocks and never rewriting the open moment; the gauge-fixed member is a
    declared convention (review D2; R2 H4; R3 K1–K3).

    Source: Brandon's ruling that learning is locating keys (September 22, as in Decision 2). The
    procedure is agent-inferred.
11. **Far fields carry moments.** Offsets and moment orders are those the receivers distinguish from
    campaign 3, and the window is an overwritten shift register (review A7, C8; R2 M5, M7).

    Source: the phase-carried source moments of the retention audit (September 22, now CLAUDE.md
    §1). The far-field reading is agent-inferred from the derivation (record §8.7).
12. **Release goes through modes.** FOUND is only what no mode reaches, and founding is a Holarchy
    join within capacity (review F7, F8).

    Source: RIDE/FOUND is the objects' emanation and resonance (cemented September 22). Releasing
    through modes first is agent-inferred from the derivation (record §8.8).
13. **The pending read** uses the anchor `λ` and `M` at the contemporary constitution (review C2).

    Source: CLAUDE.md §1, "a comparison observed after an update is read through the contemporary
    constitution and returns its residual"; the anchor form is agent-inferred.
14. **The port.** The resident owns the moments, pending ratios and staged deposits. The port adds
    `locate_keys`, `release` and `discard` and states each method's consumption.
    `InteractionReturn` is generic, the aeon trigger belongs to the joint clock, and `close_aeon`
    takes admitted `ReceivingPhases` (review D1, D2; R2 M10–M12; R3 D1).

    Source: agent-inferred.
15. **The return keeps the word's own waves or checkpoints** and claims no inverse (R2 H2).

    Source: agent-inferred.
16. **Every campaign is done on the standing real cut,** with online baselines (review E1–E4).

    Source: Brandon's ruling of August 26, "we want an *inferred response* and not a manually posed
    outcome that you cherry-picked".
17. **Owners, not new nouns:**
    - `InteractionReturn` made generic;
    - `Constitution` the one owner of Θ;
    - `Parametron` in `Ring` from campaign 1;
    - block `ConnectionIncidence`;
    - menu edges as the open paths of a `Menu`;
    - no `Key` type (review F).

    Source: Brandon's ruling of September 22 (ELEMENTARY_OBJECTS): "A new noun that is not one of
    them, or a composition of them, is a design defect".
18. **`GeneratorSourceEpisode`'s directed-contrast law moves before the file is retired** (review
    B5, F6).

    Source: agent-inferred, under Brandon's ownership rule of September 23 (CLAUDE.md §4: keep each
    law once, in its owner, with its consumer).
19. **Guards are types and lints, not source scans** (review A8).

    Source: agent-inferred from Brandon's September 24 message on tests, "I do not trust that the
    tests can comb through anything valuable".
20. **Campaign order:** 1 keys, the change and the collapse; 2 storage, lock and flow; 3 release,
    dormancy and far fields; 4 motor; 5 encoding, context and joint prediction.

    Source: agent-inferred from Decisions 2–12 (the first revision); keys lead by Decision 10.
21. **Campaign 1's declarations** (R3 D2): the field, the initial constitution and its priors, the
    exposure protocol, and the bit budget with its stop rule, which refuses and reports, never
    rounds.

    Source: agent-inferred. Each rule is stated with its reason in campaign 1, and Brandon may
    override any.
22. **Deposition on a declared carrier lattice, with the remainder carried at a precision that
    refines with the locus's deposit count.**
    - Every entry of a locus `ℓ` (its maps, factors and statistics) lives on `2^(−L_ℓ)ℤ`, with
      `L_ℓ = ⌈log₂(2 L_R X_ℓ)⌉` declared by rule. At the locus's `m`-th deposit (counted from the
      constitution's founding over the deposits with a nonzero update there, never reset), with
      `k_m = 2⌊log₂ m⌋ + 1`, the Elias-gamma length of `m` (the field's own code): the exact update
      plus the carried remainder splits at the nearest point of `2^(−L_ℓ−k_m)ℤ` into `y_f + e`, and
      `y_f` at the nearest lattice point into `q·2^(−L_ℓ) + r`, ties upward (the Ratio's `div_rem`).
      `q·2^(−L_ℓ)` is applied, `r` carried and `e` released and reported in the deposit's receipt.
      No float enters.
    - **Accounting.** Applied + carried + released = the exact sum of the updates, always.
    - **The residual is bounded for all time.** `|e_m| ≤ 2^(−L_ℓ−k_m−1)`, and the gamma lengths
      satisfy Kraft with equality in the limit (`Σ_m 2^(−k_m) < 1` for every finite count), so the
      released total stays below half a unit and every lattice value within one unit of the exact
      sum of what reached it. The carried Gram stays within `n·2^(−L_ℓ) ≤ 1/(2L_R)` of the exact one
      in operator norm, hence positive definite.
    - **Bits.** A carried remainder takes at most `L_ℓ + 2k_m + 1 = L_ℓ + 4⌊log₂ m⌋ + 3` bits
      (`remainder_rat_bits_bounded`), whatever the aeon's length.
    - **The collapse releases no remainder.** It releases only exact complements (guard 15), and a
      remainder is not one: releasing it can move a later lattice value by a unit. A locus the
      collapse deletes leaves whole, with its remainder, reported.
    - **Why.** Exact rational deposition compounded (1,126 → 10,883 → 623,415 bits over two
      deposits on the chain control). On the lattice, a remainder kept exact accumulated every
      update's denominator, and no aeon bounds it (an aeon is a first passage of the joint clock
      with no upper bound; "Bits" above). The remainder is the representation's residual, so the
      exact-representation law governs it, not retention at an aeon: against every sequence of
      tails, the residual stays bounded over every aeon since the locus's founding exactly when
      `Σ_m 2^(−k_m) ≤ 1`. Summability admits many schedules; the gamma lengths are chosen as the
      field's own complete code (agent-inferred), and they keep the bits logarithmic. A released
      tail is bounded in coefficients, not certified for the faces: that needs the word-level
      sensitivity owed in #62, as the unread carried remainder already does. Releasing
      remainders at each aeon collapse instead (the first form of this decision) let the residual
      grow by up to a unit per aeon and broke guard 15.
    - **Precedent.** History's native commits rebased to a dyadic centre and dropped the radius at
      every commit, recording the sum of dropped radii as "not a trajectory bound" (`13f8c734`,
      `IncidentRebaseResidual`). Carrying the remainder bounds that sum. The counterfactual bound
      through the word's sensitivity (`Objects/CommitRebase.commit_chain_residual`) stays owed.

    Source: agent-inferred from CLAUDE.md's exact-representation and retention laws, after
    Brandon's September 25 messages (the release point is a mathematics question; aeons carry flux
    and entropy, and the conservation of faces is what they need). Lean `HNN/LatticeDeposit`. Brandon may override it.

23. **The standing real cut is the tail of the conversation data's development stream.** The design
    names one pinned *development* cut of the conversation data with held-out targets (review E1,
    Decision 16). The private exposure dataset (`holonics.conversation-exposure.v1`, 24,768
    occurrence families) declares its own partition at its temporal cut: 22,449 development families
    before it, 617 evaluation families at or after it, 1,702 deferred. The cut is the development
    stream's last 6,148 cells, of which the final 1,190 are held out: the stream's own later
    occurrences, so no held-out cell precedes a training cell. The evaluation partition is not read
    into it and stays unspent for the outcomes' frozen task splits (step 8). Cells are the UTF-8
    bytes of each family's first view's visible parts in the dataset's declared order; roles and
    provenance are not encoded. The population is `n* = 6,148`, the smallest the declared field
    admits, which keeps the exposure near the projected six hours (3,074 windows); the held-out
    length is one mean aeon of the joint clock on uniform bytes, `⌈5·7·11·13·2⁸/1,077⌉ = 1,190`, set
    from the field, not the data. `research/notebook/hnn_design/standing_cut.py` writes the cut and
    its manifest (hashes, counts, held-out range) to `.local/cuts/`; `hnn_exposure -- cut-file`
    reads the held-out range from the manifest; the notebook reports the cut by scope and counts
    only, and #73 records its hashes.

    Source: agent-inferred from the design's review E1 and Decision 16 and the dataset's declared
    partition. A first pinning took the held-out cells from the evaluation partition; review found
    that it would spend step 8's split, and it was replaced before any receipt. Brandon may
    override it.

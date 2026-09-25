# The rebuild

**Status:** active, September 24. This plan replaces the restructure plan, which is in git history
at [`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).
Tracked in #63. Steps 0–3 are done (September 24); step 4 (the HNN law, #73) is next.

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
    retained as a separator, interior or defect. `Millennium/CokernelCalculus` states this calculus
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
  - Zeros are landmarks of spectral placement: `RH/FosterTanks` reads the zeros as LC tanks, and
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
- **BSD.** The kernel of the descent face is the doubles (`Millennium/FamilyKernel`). The rank counts
  independent navigators. The obstruction lives in a cokernel.

Their Lean in `Millennium`, `RH`, `Mathematics` and `Computation` under `lean/Holonics/` and `lean/HolonicsResearch/` is the most developed
use of the framework. It is not scheduled behind the HNN: work on a target proceeds alongside any
step. Each reusable law it finds lands in the shared objects (a navigator, a kernel/cokernel
statement, a landmark), not in a problem-named silo.

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
  law of its owner.
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
   - **Port from history as needed.** `receiver_history_compression`, `winding_inertia`,
     `identity_atlas`, `exact_linear::kernel_modes`.
4. **The HNN law in `holonics::hnn`, over aeons** (#73). The HNN is the compression machine at
   scale:
   - its retention is step 3's kernel quotient;
   - its learning is locating keys;
   - its release is the split between resonating and emanating.

   Its field is chains of parametron rings joined by pair contacts. It has:
   - source moments `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`, with `Ĝ_g` the navigator's transport;
   - the power-neutral reaction (Cayley step);
   - the normal constitution and deposition;
   - loss as the logarithm of the Holon ratio;
   - retention as the future-sufficient quotient at aeon boundaries.

   It is built with a host reference, in the machine's own order
   ([objects table](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#the-machine-in-the-elementary-objects)):
   1. ratio and one cut;
   2. rings gain storage and flow (`C`, `L`, pump);
   3. keys: configuration and clock inference by loop closure, and Farey lock addresses;
   4. the motor chart (serial screw words);
   5. Holonic Encoding, context, joint prediction and release (HNN_FORMULA).

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
   - Equation extraction compresses a foreign realization into navigators and element relations
     (the six steps in HOLON).
7. **Lean curation.**
   - Remove the duplicate theorems the audit found.
   - Rename the directories named after the prize ("Millennium", "RH") by subject.
   - Rename generator names to navigator names where they mean the object.
8. **Applications** (a workbench, an Athena application, a simulator), rebuilt on the library
   under the lessons record's requirements.
   - An outcome is one of:
     - a trainable model;
     - a first usable Athena;
     - frontier-level usefulness on consumer hardware.
   - Each outcome freezes its task split and shows failure outputs.
   - Conversation data follows the [data rules](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/CONVERSATION_DATA.md).
   - The simulator follows the [interface table](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary).

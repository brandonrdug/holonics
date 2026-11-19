# The consolidation

**Status: November 18.** C1 to C4, C6 and C8 (a to d) are read and merged. C5 keeps the kernels' headers. C7 keeps the dated reasoning in the items' comments; every Rust module
of the two engine crates opens in §5's form since November 18. C8 keeps the timing read of
`vendor/num-bigint` and `hnn::overture`'s line in #146; its part e (#995) retired 175 items inside the engine and the card crate. C9 was taken on November 18 (its notes under the step). C10 is the PC's, with
the sizes restated under it. This plan is the order of one campaign: the repository is reduced to the
machine that runs, the engine gets one owner cut by object, and its laws are stated once.
[#603](https://github.com/brandonrdug/holonics/issues/603) carries its boxes, and every commit and
pull request of the campaign cites it with `Refs #603`. [THE_REBUILD](THE_REBUILD.md) keeps the
construction's order and points here. The campaign changes no law of the machine.

It was asked for on November 14. Brandon wants to read the live engine himself, and he named what
stops him: the tree holds millions of lines, most of them data or retired machinery, and nothing
says where the machine that trains begins. He left the organization to Claude. A review of the same
day measured the tree (§1 gives its figures) and proposed eleven moves; this plan decides them, and
the build thread on the PC carries them out. The decisions are made here and are not brought back
for a nod. A step that meets a fact this plan missed revises the plan in the same pull request and
says which fact.

## 1. What stands today

Every figure is given with its part. The line counts are the review's and this plan's own reads of
`main` at `ba180139`.

| Part | Size | What it is |
|---|---|---|
| All tracked lines | 6,636,715 | 71% data: records, receipts, papers |
| Rust and CUDA | about 458,000 | the engine's path is about 38,000 of them |
| `crates/holonics/src` | 323,478 | `hnn/` holds 213,000; the engine's law is `hnn/tower/field.rs` (9,058) with `field/moment.rs` (850) and `field/scale.rs` (478), and 5,023 lines of its tests |
| `crates/holonics/examples` | 52,123 | the harness: one dispatch file routes 204 commands; the live line's are in `store_train.rs` (3,707) |
| `crates/holonics-cuda` | 49,400 | the engine's card realization is `src/hnn/field.rs` (5,095) and `kernels/field.cu` (6,408 lines, 103 kernels, 12 more in two headers) |
| `lean/` | about 641,000 | the formal mathematics; it stays as it is |
| Root guides | `CLAUDE.md` and `AGENTS.md`, 85.7 KB each | the same text but for about forty lines |
| `research/records` | 1,859 dated records, 111 receipt directories | data; it stays |

**The live chain.** A lap of the line that trains runs through these files:

```text
crates/holonics-cuda/examples/field_pass.rs                         the binary (modes: train, parity, time, …)
  includes by #[path]  crates/holonics/examples/solenoidal_alpha.rs
    → solenoidal_alpha/complete_language.rs                         the dispatch (204 commands)
      → complete_language/store_train.rs                            train-store, read-store, write-store, readings
          borrows the codec, the region and the passage's cut from  complete_language/field_train.rs
          and three argument helpers from                            complete_language/tower_train.rs
  → holonics::hnn::tower::field                                     the law (host reference)
  → holonics_cuda::hnn::{Card, CardField}  →  kernels/field.cu      the card realization
```

**Four facts the plan is built on.**
1. Gate 1 (`tools/gate.sh`) runs no test of the engine. Its library and example tests are all of
   the October lines.
2. The engine's file is not self-contained. It takes about forty small items from the October
   machine: widths, refusals and series arithmetic from `hnn/tower.rs`; the exponential and
   logarithm faces from `hnn/keyed_modes.rs`; `coupling_code` from `receiver/coupling.rs`;
   `wide_mul` from `compression/landmark/context`; `reach` from `number/census`; the units from
   `hnn/units.rs`.
3. The codec, the region a trainer owns and the passage's cut are defined in the harness of the
   older line (`field_train.rs`, which also reads about thirty `FIELD_…` environment switches).
   They are parts of the machine: the codec is its boundary chart, a region is its support, and a
   pass's place is carried in the learner's state.
4. The names collide. `hnn/` already holds October modules called `field`, `constitution`,
   `contact`, `moment` and `realization`, and the guides bar "the field" as a name for the store
   ([CLAUDE.md](../../CLAUDE.md), Method, November 12).

## 2. The anchor: one move

The review found that the tree already states the engine's unification under several names. This
section fixes it as the plan's anchor, because the cut of §5 follows from it. The reading is
`agent-inferred` from the atlas rows named below; the direction is Brandon's (a unification is the
recognition that two methods are one computation under two notations).

**The object and the operation.** The object is the [Ratio](../ELEMENTARY_OBJECTS.md#9-ratio): a
normalized quantity carried as an undivided pair, a mass `M` and a current `J`, and divided once,
at the receiver that reads it. The operation is the pair's composition along an index:

```text
step      (M, J) ← (γ M + m,  γ J + m c)        a term of mass m and content c arrives; γ carries what stood
compose   (γ₂, m₂, j₂) ∘ (γ₁, m₁, j₁) = (γ₂ γ₁,  γ₂ m₁ + m₂,  γ₂ j₁ + j₂)     associative for every γ
release   y = J / M                              once, at the receiver; never between steps
```

With `γ = 1` the steps are sums: they commute, so any partition of the terms gives the same bits.
With `γ ≠ 1` (a turn with a leak) the steps keep their order and stay associative, so the chain can
be cut into blocks and joined. The engine runs this one move over five index sets:

| Index set | In the engine | `γ` | Its chart in a discipline |
|---|---|---|---|
| the sources a site meets | the contact: `e_ij = 2^(z_ij)`, `y_i = Σ e D ṽ / Σ e` | 1 | attention ([`resolvent.attention-chart`, `norm.attention-gibbs`, `norm.mass-current-associative`](../atlas/README.md)) |
| the sites along a strand | the carry circle: `Q_t = κ_t b_t + γ_t Q_(t∓1)` | a rotor with a leak, read once a site | the selective scan of a state-space model ([`resolvent.ssm-realization`, `tower.field-scan-gate-once-a-site`](../atlas/README.md)) |
| the ticks at a site | `x ← x + O y`: a running mean on a site that only fills | 1 | a residual stream; its clock is the logarithm of the tick count (`tower.field-tick-running-mean`) |
| the sections of a lap | the deposit's two moments at rates `2^(−3)` and `2^(−8)` | `1 − 2^(−r)` | an optimizer's moments; the rate is a temperature (`deposition.rate-temperature-standing-spread`) |
| the states of a lap | the lap's mean | 1 | an average of iterates (`tower.field-lap-mean`) |

So attention is the contact and the selective scan is the carry: two charts of one move, which
differ only in whether what stood is carried at `γ = 1` or turned and leaked. What "selective" and
"attention" both name is that the term's mass or the step's `γ` is read from the input. The guides
already hold the classical statement ([HNN_FORMULA](../HNN_FORMULA.md#state-space-convolution-and-diffusion-are-one-realization),
"State-space, convolution and diffusion are one realization", and
"[Classical restrictions and modal compression](../HNN_FORMULA.md#classical-restrictions-and-modal-compression)"),
and Lean holds the pair's associativity
(`Computation/AttentionModeCompression:weighted_summary_associative`).

**Three kinds of computation.** Every phase of the engine is one of three, and the card treats each
its own way:
- a **sum**: terms at `γ = 1`, summed in integers on any partition of the card, same bits;
- a **gate**: a function of one site alone (a lock's exponent, a carry's `γ` and `κ`), read once a
  site, every site at once;
- a **chain**: steps at `γ ≠ 1` along an order, joined block by block.

**What follows for the layout.** One module holds the pair and its one release. Each phase's module
names its index set and its kind in its first lines. The card's kernels are grouped the same way.
A reader who knows the one move then reads every phase as that move on another index.

**What does not transfer, and what is owed.** The classical forms normalize inside the sum and
store floats; here the pair stays undivided at declared widths and the release is one rounding.
Whether the built carry keeps its chain's bits when cut into blocks has not been read for this
plan: a product released to its grain at every step is not associative in its bits. That reading,
and one family of sum and scan kernels for all five index sets, are the engine line's builds (§11),
each with its guess fixed first. The associativity of the ordered composition is owed a Lean
statement beside the weighted summary's; C7 adds its box to #410 unless `HNN/CarryGate` already
holds it.

## 3. The decisions

Each is stated with its reason and its scope.

**D1. The engine gets its own crates.** `crates/engine` holds the law and the host reference,
`crates/engine-cuda` its card realization, `crates/athena` the commands. Reason: a crate boundary
is checked by the compiler. Once the engine builds without `holonics`, nothing retired can reach
the live line, every retirement is safe by construction, and the address a reader opens is one
directory. A module inside `crates/holonics` would leave the boundary to habit, and the collision
of names (fact 4) would force the retirements to come before the reading. Scope: the Rust and CUDA
of the live line.

**D2. "Engine" names the built realization; no type is named "Field".** The HNN is the machinery as
the theory states it ([HNN_FORMULA](../HNN_FORMULA.md)); the engine is its one built attempt, the
one that trains, named with its receipts. Inside it the store is the `Constitution`, a region's
support is a `Region`, and the prefix `Field` leaves every type (§5 gives the map). Reason: the
guides bar "the field" as one object (November 12), and a reader should meet the objects' names.
Scope: type and module names. D4 keeps everything a receipt reads.

**D3. The codec, the region and the passage's cut are engine modules.** Reason: they are geometric
parts of the machine (fact 3; Brandon's critique of the whiteboard, November 14). Where a part is
computed, on the host or on the card, is a realization chosen by measured rate, and it is never the
part's place in the law. Scope: they move bit for bit. Replacing the codec's table of classes with
a symbol's word on located rings is a law build of the engine's line (§11), not a move.

**D4. What a receipt reads does not change.** The printed lines (`STORE_SECTION`, `STORE_SAVE`,
`FIELD_CARD`, `FIELD_PROFILE` and the rest), the saved states' text, the kernels' names and the
commands' words keep their present form through the whole campaign. Reason: the line's logs, the
tools that parse them and the reproduction of a lap compare these lines, and a renamed line is a
difference no receipt can tell from a changed law. Scope: until #603 closes; a rename after that is
its own change with its own reproduction.

**D5. A change either moves or alters, never both.** A commit that moves code changes no token of
it beyond paths, visibility and imports; a commit that edits text or names moves nothing. Every
step that touches the engine is held by the three receipts of §8. Reason: a move that also edits
cannot be checked by reading its diff, and on November 11 a commit described as a reading had
changed a training comparison. Scope: every step from C3 on.

**D6. The October machine retires by #603's test; a law never retires.** A module with no path from
the live crates is retired once any law that only it states has an owner in Lean or a guide, or its
box in #410. Its atlas rows stay, with their `R:` owner repinned to the last commit that held the
code. Reason: the anti-reduction law (every operator has a caller in the live learner and an
acceptance that vanishes when it is removed), and the rule that Lean holds the mathematics and Rust
holds what runs. The grand image is the theory's, and it stands in the guides, Lean, the atlas and
the records. Scope: `crates/holonics`, `crates/holonics-cuda`, the examples, `accelerators/`,
`tools/`. Lean is not in scope.

**D7. Data stays, where it is, as data.** `research/` is the data tree and keeps its present paths:
the records stay in one flat directory. Reason: he lets data accumulate and means to recycle it; a
record links another by its bare name, and every link from an issue, a pull request or a note
outside the tree points at the flat path. Moving 1,859 records into month folders would rewrite
thousands of links for a listing nobody reads from the top (`agent-inferred`; the review proposed
the folders). What changes: the code tree holds no data and compiles none (C9), `.gitattributes`
marks `research/` as documentation so the host's language statistics count the code, and a
generated index lists the records by month.

**D8. Laws are stated once.** `CLAUDE.md` is the one statement of the laws and the practice.
`AGENTS.md` holds Codex's role and binds it to `CLAUDE.md`. `docs/THE_ENGINE.md` is the one guide
to the engine. `CONSTRUCTION_STATE.md` holds the position and nothing else. Reason: two copies of
85.7 KB were edited in step for every rule and differed in forty lines; a third statement of a law
in a status file is how a stale one comes to govern.

**D9. A declared extent is named as a declaration.** The ticks, the lanes, the widths and the reads
are counts the declaration fixes where the theory gives a law (§10). The campaign writes, beside
each, the part it sizes, the reading that sized it and the law it stands in for. It replaces none:
that is law work with a fixed guess, the engine line's.

**D10. The laboratory repository is an archive** (Brandon, November 14). Its 204 KB operating
context is replaced by a short note in the same change as this plan; nothing there schedules work.

## 4. The target layout

```text
README.md  CLAUDE.md  AGENTS.md  CONSTRUCTION_STATE.md  Cargo.toml
crates/
  engine/          the law and the host reference            (package holonics-engine)
    src/           one module an object (§5); each with its tests beside it
  engine-cuda/     the card realization                       (package holonics-engine-cuda)
    src/           the driver, the card, the realization cut as the law is (§6)
    kernels/       engine.cu and one header a phase
  athena/          the commands: train, read, write, parity   (package athena, binary athena)
  holonics/        what #603's test keeps of the library; expected to be little
docs/
  THE_ENGINE.md    the one guide to the engine
  THE_MACHINE.md, ELEMENTARY_OBJECTS.md, HNN_FORMULA.md, …   the theory's guides, as now
  atlas/  canon/  plans/
lean/              unchanged
research/          data: records (flat, with INDEX.md), receipts, papers, notebook, design, fixtures
tools/             the tools a live script or a guide's practice calls
```

`crates/holonics-cuda`, `accelerators/` and `vendor/` are expected to leave (C8 decides each by its
test).

## 5. The engine's cut by object

`crates/engine/src/`, in the order a reader follows a section. "Today" names items of
`hnn/tower/field.rs` unless another file is given. The build thread holds the code and may move an
item to a better module; the rule for a doubtful item is that it goes with the object whose law it
states, and an item that measures the machine without changing what the state carries or the
deposit consumes is a ruler.

| Module | Object | Today | Kind and index |
|---|---|---|---|
| `lib.rs` | the Holon as one object | the map: the one move, the modules in order, the declared extents | |
| `width.rs` | precision | `FACE_BITS`, `MATERIAL_BITS`, `MOVE_BITS`, `COVECTOR_BITS`, `SHARE_BITS`, `CONTACT_BITS`, `STATE_BITS`, `fit32`, `fit64`, `refuse`, the error, `reach`, `wide_mul` | |
| `ratio.rs` | the Ratio: the pair and its release | `SeriesRow`, `Sums`, `Exponential`, `exp_series`, `ln2_face`, `log2_face`, `div_nearest`, `ratio_to_power`, `ratio_adjoint`, `half_turn`, `release` | the one move |
| `declaration.rs` | the declared extents | `FieldDeclaration`, `FieldLayout`, the draws' counts, its text | |
| `constitution.rs` | the constitution: the store and its loci | `Field`, `found`, `to_text`, `from_text`, the temperatures and decays | |
| `founding.rs` | founding a part at zero | `grown`, `laned`, `contacted`, `lettered`, `with_carry`, `with_triads`, `with_opening`, `with_junction`, `with_mark`, `with_depth` | |
| `codec.rs` | the boundary chart | `FieldCodec`, `units_of`, `question_text` (`field_train.rs`); `Units` (`hnn/units.rs`) | |
| `region.rs` | a region: its support and its ports | `Region`, `Port`, `Echo`, `ClassLists`, `port_reading`, `admit_region`; `TrainRegion` (`field_train.rs`) | |
| `passage.rs` | the passage's cut and a pass's place | `StorePass`, `PassSlice`; `Piece`, `Slice`, `Stretch`, `Cut` (`store_train.rs`); `problems_of`, `mix`, `shape`, `weighed_domain`, `held_out` (`field_train.rs`) | |
| `navigator.rs` | rings, clocks and paces | `ring_periods`, `Paces`, `ring_phasor`, `turn_phasor`, `skin_of`, `temperature_of`, the frame, `BlankClocks` | gate, a site |
| `moment.rs` | the source moment and the opening | `moments_of`, `opening`, `open`, the cavity; `field/moment.rs` | sum over a site's strand |
| `contact.rs` | the contact and the tick | `lane_chart`, the classes and supports, `lock`, `Shares`, `Crowd`, `tick`, `FieldPass`, `pass` | gate (the lock), then sum over the sources; sum over the ticks |
| `carry.rs` | the strand: pair, carry circle, junction, triad | `strand_mate`, `carry_coupling`, `carry_friction`, `carry_gate`, `junction_gamma`, `junction_forward`, `CarryGates`, `triad_products`, `affine_joint` | gate, then chain along the strand |
| `face.rs` | a receiver's face and its code | `TowerFace`, `face_of`, `faces`, `tied`, `face_code`, `weighed_code`, `code_of`; `coupling_code` (`receiver/coupling.rs`) | gate, an open site |
| `adjoint.rs` | the return through the producing operands | `covector`, `transposed`, `affine`, `outer_sum`, `returned`, `tick_return`, `clock_return`, `read_and_return`, the routes | the forward's kinds, reversed |
| `deposit.rs` | deposition | `deposit_step`, `on_step_grain`, `toward`, `FIRST_RATE`, `SECOND_RATE`, `RateParts`, `PartTravel`, `MaterialMean` | chain over the sections; sum over a lap |
| `release.rs` | reading until agreement, and writing | `settle`, `redraw`, `certified_passes`, `sample_realized`, `release`, `SettlePass`, the mark | |
| `level.rs` | a level on its news | `landmarks`, `landmarks_of`; `field/scale.rs` (`level_declaration`, `level_split`, `LEVEL_HARMONICS`) | |
| `realization.rs` | the port a realization implements | `FieldRealization`, `HostField`, `FieldRead`, `FieldNext`, `FieldReceipt`, `RealizationCounters` | |
| `learner.rs` | a section: read, return, deposit | `FieldLearner`, `section_realized` | |
| `ruler.rs` | readings no law consumes | `HeldRead`, `TickRead`, `HeldRows`, `OpenRows`, `ReachSums`, `TickNews`, `CrossingTension`, `letter_balance`, `entropy` (the reaction and mirror readings retired with #995, held at `867430ea6`) | |

**A module's first lines** state, in this order: the object; its equations in the present tense, at
their declared widths; its kind of computation and its index set; the kernels that realize it; its
Lean owner; its atlas rows; the records that derived it, as links. Nothing dated stands in a
header: the derivation's history is the records'.

**The names** (C5's second pull request): `Field` → `Constitution`, `FieldDeclaration` →
`Declaration`, `FieldLayout` → `Layout`, `FieldLearner` → `Learner`, `FieldRealization` →
`Realization`, `HostField` → `Host`, `CardField` → `Resident`, `FieldCodec` → `Codec`,
`FieldPass` → `Forward`, `FieldRead` → `Read`, `FieldNext` → `Next`, `FieldReceipt` → `Receipt`,
`TrainRegion` → `OwnedRegion`. The saved text and the printed lines keep their words (D4).

## 6. The card's cut

`crates/engine-cuda/src/` takes `cuda.rs` and `ffi.rs` (the driver), `hnn/card.rs` with
`DeviceError` (the card and its census), and `hnn/field.rs` cut as the law is: `resident.rs` (the
open, the upload, the pools and the `Realization`), `moment.rs`, `contact.rs`, `carry.rs`,
`face.rs`, `adjoint.rs`, `clock.rs`, `level.rs`, and `profile.rs` (the launch records, the profile
and the yardsticks).

`kernels/engine.cu` stays one translation unit, so the image holds the same kernels under the same
names, and it includes one header a phase: `series.cuh` (limbs, the exponential), `moment.cuh`,
`cavity.cuh`, `contact.cuh` (chart, frame, classes, sums, shares, current), `carry.cuh` (pair, the
gates, the scan, triad), `face.cuh`, `adjoint.cuh`, `clock.cuh` (paces, skin, blanks), `level.cuh`
and `yard.cuh`. Each header's first lines state its kind (sum, gate or chain), the block and thread
layout that realizes it, and the host module it is at parity with. The build script's digest list
names the new files.

## 7. The commands

`crates/athena` builds one binary, `athena`, whose words are today's: `athena train train-store …`
is `field_pass train train-store …`. The line's scripts change the binary's path and nothing else.
It depends on the two engine crates and on nothing in `crates/holonics`.

**Which commands are live.** The dispatch routes about fifty commands through the card today,
twenty-seven of them the store line's and most of those readings built for one scored guess. A
command is live when one of three holds:
1. a run or read script of a line that is training calls it (C1's inventory);
2. a guess that is fixed and unread needs it;
3. it is the acceptance apparatus: parity, the time read, the profile.

The rest retire with the harness, each named in the pull request with the record that scored it;
the record is its receipt and history holds its code. Reason: a reading a live line's script calls
is consumed code (November 11), and a reading whose guess is scored is a ruler that did its work.
The live readings sit in `crates/athena/src/ruler/`, one file each, named rulers.

**The older line.** `train-field`, its switches and its twenty-four other commands retire once no script
of a training line calls them. Where the code passage is still read as the yardstick, it is read
through the store line's commands, never through a second trainer. No reading a line is scored by
is lost: each one a live script still calls gets its store-line form first, in its own pull
request.

**Parity moves onto the store line** before the harness is cut (C2): today `parity-field` forms its
sections as `train-field` does, so the engine's only card-against-host check depends on the trainer
that is to retire.

## 8. The three receipts

Every step from C3 on is held by these. Each is a reading of the build, and a step reports what it
read.

- **Parity.** From the line's last saved state, on the store line's sections and declaration, the
  card's faces and covector entries equal the host's on every site, and the learners' texts are
  equal after each section. Required for every pull request that touches the engine's Rust or its
  kernels.
- **Reproduction.** From the line's last saved state the build trains the line's own sections, and
  `tools/reproduction.py` reads its `STORE_SECTION` and `STORE_SAVE` lines equal to the line's,
  timings and schedule fields aside, with `cmp` of the states; then the line's read script, run on
  the lap's saved state, prints the lap's own read lines. Required each time the binary a line
  trains or is read with is replaced, and at the end of C3, C5 and C6 whether or not it is.
- **Timing.** Control, the build, control, inside one hold of the card lock on the same sections.
  A difference inside the control's spread is no difference. Required at C3 and C5, where a crate
  or module boundary could change what the compiler inlines. Guess, fixed here: within the spread
  at both, since the release profile links with whole-program optimization and no hot path gains a
  crate boundary it did not have.

The line keeps training on its staged binary while the campaign's pull requests merge. A build
enters the line only by its reproduction.

## 9. The steps

Each step is one loop or a few, ends in a merged pull request with its receipt, and is done when
its line below holds. The order is by dependency; C8 may interleave with anything after C6.

**C0. The plan** (the cloud; this change). This file, #603 rewritten to its boxes, the pointers in
THE_REBUILD, README and CLAUDE.md, `AGENTS.md` as Codex's role file, `.gitattributes`, and the
laboratory's archive note. No code.

**C1. The live set, by coverage** (the PC; no change to the machine).
- The inventory first: every command line of the run and read scripts of each line that is
  training, and every tool they call, written to `commands.txt` with private paths replaced by
  names.
- Then one instrumented build of the line's binary in its own target directory
  (`RUSTFLAGS="-C instrument-coverage"`, release profile; `llvm-profdata` and `llvm-cov` from the
  toolchain's `llvm-tools` component), run under the card lock from a copy of the line's last saved
  state, writing only to scratch: a few sections of `train-store`, each command of the read script
  once, one `write-store`, and the same with `FIELD_PROFILE` for the kernels launched.
- `tools/live_set.py` (new, with its test in gate 1) reduces the export to the receipt
  `research/records/receipts/<date>_live-set/`: `rust_files.tsv` (file, executed lines, lines,
  executed functions, functions), `kernels.tsv` (kernel, launches), `commands.txt`, and the tree's
  commit, the state's name and the declaration it ran.
- The prediction, fixed here: the files with an executed line are the chain's of §1 (with
  `field/moment.rs` and `field/scale.rs`), `hnn/tower.rs`, `hnn/keyed_modes.rs`, `hnn/units.rs`,
  `receiver/coupling.rs`, `compression/landmark/context`, `number/census.rs`, the card's
  `cuda.rs`, `ffi.rs` and `hnn/card.rs`, and the crates' `lib.rs` and `mod.rs` files. A file
  outside that list is a dependency this plan missed, and C3 carries it.
- What the reading decides: which files, commands, tools and kernels outside the engine are
  candidates to retire. It decides nothing inside the engine's files: a branch the line's present
  declaration does not take is still the law of a state founded another way, and the campaign moves
  the engine whole.
- Done when the receipt is merged and the prediction is scored, a miss included.
- Read November 14 ([the receipt](../../research/records/receipts/2026-11-14_live-set/README.md)). 16 of the tree's 335
  compiled files executed, and all 16 were predicted. No executed file stands outside the list, so the plan missed no dependency
  of the run. Six predicted entries ran no line:
  - `receiver/coupling.rs` and `compression/landmark/context`, which the engine reaches only through its host reference
    (`port_reading`, `one_end_length`); C3 still carries them;
  - `ffi.rs`;
  - the declaration-only `lib.rs` and `mod.rs` files.

  The line launched 86 of the 163 declared kernels. None of the 48 kernels outside the three field sources was launched. The
  reading also found that every script calls a tool that stands outside the tree (`measure.py`, below in C2).

**C2. Gates for the live line** (the PC).
- Gate 1 runs the engine's host tests (`tower::field` and its moment's), or the part of them that
  fits beside the other checks with the rest in gate 2, by their measured time.
- `parity-store`: parity as §8 states it, on the store line's sections, with the line's whole
  declaration (lanes, carry, triads, opening, junction, mark, levels).
- Gate 3 for the engine is `parity-store` and the reproduction.
- `tools/measure.py` (the run's wall time and peak resident set, 6 lines) comes into the tree with a test in gate 1. Today every
  run and read script of the line calls it from another worktree's untracked `.local/`. The next launch of each script calls it
  from `tools/` (C1's reading, November 14).
- Done when a deliberately altered constant in the engine fails gate 1 or gate 3, and the unaltered
  tree passes both. The alteration is not committed.
- Read November 14 ([the receipt](../../research/records/receipts/2026-11-14_engine-gates/README.md)).
  - Gate 1 runs 122 of the engine's 123 host tests (42 s). The 150 s one goes to gate 2.
  - Gate 3 is `tools/gate_engine.sh`: `parity-store` on 3 of the line's sections, 24 reproduced, and the lap's read.
  - The unaltered tree passed both gates. Two alterations failed gate 3, each by a different arm:
    - the deposit's divisor, by the reproduction, first at section 10;
    - a kernel's `ln 2` grain, by the parity's covector.
  - Parity alone, or 3 reproduced sections alone, would have passed the first.

**C3. The lift** (the PC; moves only).
- Tag the tree first: `archive/tree-before-consolidation` at `main`, pushed from the PC.
- `crates/engine` receives `hnn/tower/field.rs`, `field/` and their tests whole, and one file of
  the items of fact 2, moved from where they stand. `crates/engine-cuda` receives `cuda.rs`,
  `ffi.rs`, `hnn/card.rs`, `hnn/field.rs`, the three field kernel sources and the part of the build
  script that compiles them.
- `crates/holonics` and `crates/holonics-cuda` import what moved, for as long as they stand. This
  is an import and never a second copy.
- The guard lints of gate 1 (no floats, the disallowed types and methods) run on the engine crates
  in the same change, and on `athena` at C6. A guard that is not run does not hold.
- The atlas rows whose owner is `holonics::hnn::tower::field` (about eighty) name the new owner in
  the same commit.
- A leaf the move would have to edit to keep compiling may retire first, by D6's test.
- Done when the engine crates build with no dependency on `holonics`, and parity, reproduction and
  timing hold.
- The host part, read November 14:
  - `crates/engine` holds `field`, with the items it borrowed moved from where they stood. They are
    five files (`inherited/{tower,keyed_modes,coupling,context,census}.rs`), not one, because two
    names stand in two of the files (`reach`, `UNIT_BITS`).
  - The borrowed items are larger than fact 2 said. The tower's 29 named items reach 45 with their
    own dependencies (450 lines), and `coupling_code` brings 15 of `coupling.rs`'s items. `fit64`
    calls the census, so `number/census.rs` moves whole, keeping its counters single.
- The card part meets two facts the plan missed:
  - `Card::open` loads the October image (`hnn.ptx`, from `hnn.cu` and its headers) and keeps its
    module for the October owners' launches.
  - `DeviceError` carries the October's refusals beside the card's own:
    - the October's: `OffLattice`, `Word`, `Carrier`, `Malformed`, `Status`, `EpochFlow`,
      `InverseExact`, `WordExact`, and `Hnn` from `HnnError`;
    - the card's: `Driver`, `NoKernels`, `Census`, `ForeignBuffer`, `Launch`, `Shape`.

  The card realization reaches neither: it launches only its own image and returns only the card's
  refusals. So the card part comes in three commits, each held by gate 3:
  1. the card opens with no image, and the October owners open it with theirs;
  2. the card's refusals become their own type, into which the October's error converts;
  3. the move.

  A third fact surfaced when the card moved: five October files added methods to the card (`impl
  Card` in `lattice.rs` twice, `execute_exact.rs`, `inverse_exact.rs` and `epoch.rs`). An inherent
  impl cannot stand outside the type's crate, so those blocks became extension traits in one more
  alteration, before the move.

  The guard lints run on `crates/engine` from the host part. On `crates/engine-cuda` they find 25
  uses of floats, all in the card's yardsticks (`CardField::yardsticks` and `Yardsticks`, a ruler of
  its rates). They join gate 1 when C5 cuts the yardsticks into `profile.rs` as a named ruler.

**C4. The codec, the region and the passage come in** (the PC; moves only). From `field_train.rs`,
`store_train.rs` and `hnn/units.rs` into `codec.rs`, `region.rs` and `passage.rs`, bit for bit.
`codec.rs` says in its first lines that the table of classes stands until the symbol's word
replaces it, with the rule's date. Done when `store_train.rs` imports nothing from `field_train.rs`
or `tower_train.rs`, and parity and reproduction hold.
- Read November 14. Two facts the plan missed:
  - The store's `Slice` held a file, and the guards keep the file system out of the engine. So a slice
    now reads through `PieceBytes`, and the store's file (`SliceFile`) stays in the harness. This was
    one alteration, before the move.
  - The codec parses its text with the harness's `count`, so `count` moved with its consumer into
    `codec.rs`.

  `units.rs` moved whole as its own module rather than into `codec.rs`, so its history follows it.
  The harness keeps what reads files and prints lines: `units_of`, `held_text`, `micro_bits`,
  `step_transfer`, `positive` and `STATE_BUDGET`. They now stand in `complete_language.rs`, where
  every command file sees them.

**C5. The cut by object, then the names** (the PC). Two pull requests: the moves of §5 and §6
(code, tests, kernels), then the renames. Done when no file of the engine holds two objects, no
type is named "Field", and parity, reproduction and timing hold after each.
- The cut, read November 14 (the receipt's C5 section):
  - The host and the card are cut by object, every line kept. The pass's place goes to
    `learner.rs`, because its text reads the tower's `Result`.
  - `field` and the card's `hnn::field` stand as façades that re-export the modules, so every
    path holds until the renames.
  - Gate 3 is equal. Timing holds once the hold's order is balanced: the card's runs fall into two
    states that a plain alternation confounds with the build.
- Owed to C5's second part:
  - The kernels' headers (§6).
  - The `inherited` items' distribution into `width.rs`, `ratio.rs`, `face.rs` and `deposit.rs`.
  - The renames. Three of §5's names collide with names that stand: `Layout` and `Realization`
    with the card's launch layout and its realization, and `Resident` with an October card owner
    (`holonics_cuda::hnn::port::Resident`). The renames choose around them.
- The renames, read November 15: `Field` → `Constitution`, `FieldDeclaration` → `Declaration`, `FieldLearner` → `Learner`,
  `FieldRealization` → `Realization`, `HostField` → `Host`, `CardField` → `Resident`, `FieldCodec` → `Codec`, `FieldPass` →
  `Forward`, `FieldNext` → `Next`, `FieldReceipt` → `Receipt` and `TrainRegion` → `OwnedRegion`, in every crate, kernel comment,
  three tools' comments, the engine guide and 134 of the atlas's live owners (`R:`); owners pinned at a commit keep their names.
  Two names were chosen around what stands (`agent-inferred`): `FieldLayout` → `Loci`, since the card's launch `Layout` stands in
  `hnn::card` (the layout's object is the constitution's loci, by block), and `FieldRead` → `ReadLogits`, since `std::io::Read` is
  imported beside it in the commands and `inherited::census::Reading` stands in the engine (the struct is a read's logits and their
  echoes). `Realization` and `Resident` no longer collide: the card's realization type is `Resident` itself, and the October card owner
  retired with C8a. The saved text and the printed lines keep their words. Gate 1 passed, and gate 3 on lap 17 is equal (parity on 3
  sections, 24 reproduced, the read byte for byte). Timing holds in one balanced hold on 24 of the line's sections from lap
  16's `STATE.3000` (a warm-up, then control, renamed, renamed, control, control, renamed, renamed, control): the control's runs
  read 712.1 to 712.9 ms a section, the renamed build's 712.2 to 713.6, every run's section lines equal to the first's. Done for
  C5 save the kernels' headers and the `inherited` items' distribution.
- The `inherited` items, read November 15: each stands in the module of its object. The grains, the refusal, the carriers' fits and
  the wide product are in `width`; the release, the exponential and logarithm faces, the nearest quotient, the half turn, the ratio's
  adjoint and the code of a ratio (the October `code_of`, renamed `ratio_code` beside the face's own `code_of`) are in `ratio`; the
  tower's face, its codes and the certificate's comparisons are in `face`; the maps and the covector are in `adjoint`; the deposit's
  step and rates are in `deposit`. The receiver's coupling at temperature one and the width census are objects of their own, so they
  are the modules `coupling` and `census` (agent-inferred: the plan's table put the coupling in `face`, but one file holds one object).
  The keyed modes' copy of the unit grain went with them, `width` holding the one. Gate 1 passed, and gate 3 on lap 17 is equal. Timing was not
  re-read: the items moved within one crate with their bodies unchanged. Owed to C5: the kernels' headers. Two types of the card's
  profile still carry the old word (`FieldTimes`, `FieldProfile` in `hnn/profile.rs`; read November 18), which C5's done condition names.

**C6. The commands** (the PC). `crates/athena` with the live commands by §7's rule; the dispatch,
`train-field`, its switches and the retired readings leave; `field_pass` leaves. Done when
`athena` depends on the engine crates alone, the line's scripts run on it, and the reproduction
holds with the reads' lines.
- Read November 14 and 15 (the receipt's C6 section):
  - `athena` holds the store line's live commands (`train-store`, `write-store`, `found-lane`,
    `next-pass`), its live reading (`ruler::cavity`), the parity (`parity-store`) and the exterior's
    shared reads and writes. The binary keeps field_pass's words and the card's measures
    (`yardstick`, `attributes`, `reserve`, the profile). It depends on the engine crates and `rayon`.
  - The field line retired (`field_train.rs`, `field_parity.rs`: 5,896 lines, held at `7a1eb3ce7`),
    and 22 store readings and foundings, each guess read (held at `264161d8e`).
  - Gate 3 is equal on lap 13, the line's last saved state, and timing holds state for state in a
    balanced hold. The line goes on from lap 14 on `athena`.
- Three facts the plan missed:
  - `field_pass`'s `time` mode routed only `time-field`. On the store line the time read is
    `train-store`'s own section lines, which every timing hold reads, so `time` left with it.
  - The exterior items C4 left in the harness are shared by the harness and the commands. They are
    `athena::exterior`, and the harness imports them back until C8.
  - The harness's dev-dependency on `athena` reaches the card crate, and clippy lints a workspace
    member it compiles as a dependency. Gate 1's guard lints now name their crates (`--no-deps`), so
    the card's owed float lints (C3) do not enter a lint that never named them.
- Owed to C8: the harness (`solenoidal_alpha`, its tower and native lines) leaves with the
  examples, and `tools/seen_passage.py`, a ruler of `train-field`'s withholding, with the tools (C8d).

**C7. Headers, comments and the engine guide** (the PC or the cloud; text only).
- Every module and kernel header takes §5's form. A comment's dated reasoning moves to the record
  that holds it, or to a new dated record where none does; a constant keeps one sentence of reason
  and its link. The word "exact" leaves the comments, as the precision law asks.
- `docs/THE_ENGINE.md` is written against the cut: what the engine is; the one move (§2); the
  pipeline in order, each phase with its object, equations, module, kernels, kind, widths, Lean and
  atlas rows; the declaration, extent by extent (§10); the three kinds of computation and where a
  section's time goes; the commands and the lines they print; a reading route through the files;
  the guards as they stand on the engine; what is owed.
- THE_MACHINE's twenty-two guards each get one of three ends, in a table in the guide: it holds on
  the engine as a lint or a failing doctest in an engine crate; it holds as a practice rule in
  CLAUDE.md; or it retires with the object it guarded, with the reason.
- The operator contract in ELEMENTARY_OBJECTS and the owners in HNN_FORMULA name the engine's
  modules.
- Done when a reader can go from the guide's pipeline to each phase's file and kernel by a link,
  and parity holds (a kernel's comment changes its digest).
- The guide, read November 15: `docs/THE_ENGINE.md` stands, against the cut as it is: what the engine is, the one move with
  its five index sets and three kinds, the pipeline phase by phase (object, equation, host module, card module and kernels,
  kind; the Lean owners beside), the line's declaration word by word with the part each sizes, the saved state line by line,
  where a section's time goes (from lap 17's own lines), the commands and their lines, a reading route, and the guards'
  table, moved from THE_MACHINE, which points to it. The headers, the operator contract's and HNN_FORMULA's owners, and the
  dated reasoning in the comments are C7's still; no kernel changed, so parity is not touched.
- The headers, read November 15: the seventeen modules C5 cut from `field.rs` (`width` to `ruler`) open in §5's form: the object, its
  equations, its kind of computation and index, its kernels with their card module, its Lean owners, the atlas rows whose live owners
  stand in it alone, and its records. The items' own dated reasons stay where they stand. Rust comments only; no kernel changed. Owed:
  the kernels' headers with the kernels' cut (C5), and `codec`, `region`, `passage`, `units` and the card's modules, which kept their
  own first lines.
- The rest of the headers, read November 18: `codec`, `region`, `passage` and `units` open in §5's form, each fact read from the items
  below it, and nine modules of `crates/engine-cuda/src/hnn` name their object, the host module that states their equations and
  THE_ENGINE §3, whose table of kernels by card module was read against the code that day and holds. The first lines they held stand
  word for word in [the record of the move](../../research/records/2026-11-18_THE_CODEC_THE_REGION_THE_PASSAGE_AND_THE_UNITS_OPEN_IN_THE_CONSOLIDATIONS_FORM_AND_THEIR_FIRST_LINES_STAND_HERE_AS_THEY_WERE.md),
  with five comments that named owners gone from the tree. Rust comments and two manifests' comments only: no kernel and no build
  script changed, so no digest moved. Gate 1 ran in the cloud container on it (`tools/gate_nocard.sh`, below).
- Gate 1 with no card, November 18: `bash tools/gate_nocard.sh` runs `tools/gate.sh` in a container against a stand-in for the
  driver library (the one tie gate 1 has to a card is the link of athena's test binary). It reads no kernel, so it gates a change
  that leaves every crate's compiled tokens as they were and is a read before the PC's gate 1 for any other.

**C8. The October machine retires** (the PC; several pull requests, leaf first).
- In order: the card's October modules and kernels, then `crates/holonics-cuda` whole; the examples
  and the notebook's example wiring in `Cargo.toml`; the October tower and `hnn/`; then
  `receiver`, `holarchy`, `physics`, `compression`, `number`, `geometry`, `navigator`, `holon`,
  `aeon` and `ratio`, each by D6's test; `accelerators/`; the tools no live script or guide calls,
  with their tests.
- Each pull request lists what it retires, the last commit that held it, and for each atlas row
  that cited it: the Lean or guide owner that keeps the law, or the box added to #410. Its tests
  leave gate 1 in the same change, and every guide link to a deleted file is repinned to a commit.
- `hnn::overture` is joined to the engine or its state is written in #146.
- `vendor/num-bigint` leaves when a timing read in one hold shows the host's section time the same
  without the patch; the engine uses big integers, so this is read and not assumed.
- Done when `cargo check --workspace` builds only crates with a path from `athena` or a consumer
  named in an open issue, and gate 1 runs only checks of what stands.
- C8a, read November 15: `crates/holonics-cuda` (37,768 lines) and `accelerators/` retired whole,
  held at `d6bbd1644`. No file of the engine crates or of `athena` changed, so C6's gate 3 and timing
  stand for them. Each card owner realized a law stated in `crates/holonics`, its atlas row or its
  record. The 37 atlas rows keep their rows: two items that live in the engine's card crate name it,
  and the rest name their files at that commit. Owed to C7: the prose of about twenty guides still
  names `holonics_cuda` owners as current (the operator contract among them).
- C8b, read November 15: the examples (about 42,000 lines), the notebook's three `[[example]]`
  entries, holonics's dev-dependency on `athena`, and the listener's tools with their tests retired,
  held at `8a77b7755`; gate 1 lost the six controls that ran them. The notebook's files stay as data
  (D7). `hnn::overture` lost its two consumers (the overture examples); it is joined to the engine
  or its state is written in #146 when `hnn/` retires.
- C8c, read November 15: `crates/holonics` (about 306,000 lines) retired whole, held at `d5ed4adc1`. After C6 no path from
  `athena` reached any module of it, and no open issue names one as a consumer (#404 names the lifted field, #76 the October
  card's debts, #410 laws of `number`). D6's test, read on the atlas: 904 rows named a library owner; 7 entries the library
  re-exported from the engine now name the engine, and 2,123 entries name their file at `d5ed4adc1`. 310 of the rows had no
  Lean or live owner; their law stands in the row itself, a guide entry with its record, as D6 asks. THE_MACHINE's
  twenty-two guards each have an end in its table (two hold on the engine as lints, thirteen as practice rules, seven retire
  with their objects); C7's engine guide carries the table. Gate 1 lost the library's fourteen controls and its guard lints
  and doctests, which now run on the engine. `tools/holonics_text_terrain.py` reads the Rust of `crates/*/src`. #404 and #76
  take their state lines.
- Owed after C8c: the tools no live script or guide calls (C8's last item), and `vendor/num-bigint`'s timing read.
- C8d, read November 15: the tools sweep. 28 files of `tools/` (3,785 lines) that no guide, no run script written in the last three days,
  no crate and no standing tool calls retired, held at `457450864`: the October listener's and V92/V93 campaign tools
  (`complete_language*`, `durable_training_*`, `native_output_pool`, `bounded_native_v92_controller`, `rate_guard_v92`, the two capture
  tools, `listener_diagnostic_contract.md`), the October tower's readers (`answer_digits`, `arithmetic_lines`, `arithmetic_looks`,
  `text_looks`, `tower_circuit`, `tower_modes`, `landmarks`), the field line's state tools (`pace_rates`, `round_state`, `split_report`)
  and `seen_passage`, with their five tests; gate 1 lost the seen passage's controls. Four atlas owners name them at that commit. Kept
  though no live script calls them, each for its input: `corpus_passage.py` and `code_passage.py`, which wrote the store and the held
  passage the line reads, and `holonics_text_terrain.py` with `arithmetic_terrain.py`, the terrain of the Holonics text, the product's
  first subject. The standing tools' tests that gate 1 did not run join it where they read only what they write (the mailbox, the copy
  length, the human messages' fixtures); `test_corpus_passage.py` needs `pyarrow`, which the PC's Python lacks, and stays out of the gate.
- C8e, read November 18 (#995): D6's test inside the three crates. 175 items that no command, test or kernel reached retired, held at
  `867430ea6` (2,861 lines): the October driver in `cuda.rs` and `ffi.rs` (121 items), the October launch layouts and the card's own
  image path in `hnn/card.rs` (29), and 25 readings of scored guesses in the engine, most in `ruler.rs`. They were read two ways, a
  static inventory and rustc's dead-code analysis of the three crates merged into one binary under athena's `main`. Five atlas owners
  name them at that commit. The card's `Layout` and `Realization`, which C5's renames were chosen around, left with them; the names
  chosen then stay (D5). Read beside it, with nothing to retire:
  - the kernels: every entry of `kernels/field.cu` and `field_cavity.cuh` (117 written out and the eighteen the contact macro makes)
    is launched by name from a module of the resident;
  - the commands: the 48 words `athena`'s `main.rs` routes are the words of the engine guide's §7, and §7 names no word that
    nothing routes;
  - the tools (C8's last item, read again): 77 files, of which 55 are named by a gate, a guide, a crate or a standing tool. The other
    22 are host rulers written from November 16 to 18. Ten are called by a run script of the last two days on the PC, ten more are
    named by the record that used them, and two by neither (`arms_ruler.py`, `frontier_ruler.py`). None is October's, and none
    retires while its line runs. No guide lists them, so a design finds them by `ls tools/` and their docstrings.

**C9. Position, order and data** (the cloud or the PC; text only).
- `CONSTRUCTION_STATE.md` holds the position: each line that trains, its commit, its state, its
  last readings by region, and what is queued. What it held before is linked at a commit.
- THE_REBUILD's §3 describes the store line; the status lines of #404 to #407 are current;
  CLAUDE.md's repository table and its issue list describe the tree as it stands.
- CLAUDE.md's method rules keep their bar, their reason in a sentence, their scope and the link to
  their record; an occasion's full account moves to its record where the record lacks it. No rule
  loses its reason.
- `tools/records_index.py` writes `research/records/INDEX.md`, one line a record by month, and its
  test runs in gate 1.
- Done when the README's map, the guides and the position agree with the tree, checked by a link
  test over the root guides, `docs/` and the records' README.
- The position, the method rules and the issues, read November 18 (#991):
  - `CONSTRUCTION_STATE.md` keeps its newest section and a dated list of the four layers that stood under it, held at `8314281c5`
    (54 KB to 17 KB). A new position goes on top and the one under it joins the list.
  - CLAUDE.md's method rules, the card rule and the waiting standard keep their bar, a reason in a sentence, their scope and their
    link, grouped as a design, a line's lap (numbered 1 to 11 in a lap's order) and a reading and its telling. Their text as the
    guide held it stands word for word in
    [the method rules' record](../../research/records/2026-11-18_THE_METHOD_RULES_THE_CARD_RULE_AND_THE_WAITING_STANDARD_WITH_THEIR_OCCASIONS_AS_THE_GUIDE_HELD_THEM_BEFORE_IT_KEPT_EACH_RULES_BAR_REASON_SCOPE_AND_LINK.md).
    A second reader compared the two rule by rule and seven dropped clauses were restored. A fact the plan missed: the bars and
    scopes are most of the text, so the guide went from 113.6 KB to 108.7 KB. A shorter guide is fewer rules, and that is a
    decision about the rules, never a step of this campaign.
  - `tools/lap_check.py` reads a lap's run script against the lap's rules and `tools/runs.py start` prints its notes; its controls
    run in gate 1. It is the one new tool of the step, and its reason is that no lap script of November 18 called `read-loudness`.
  - CLAUDE.md's issue list and its `crates/athena` row describe the tree, and the status lines of #404 to #407 are current. #405 to
    #407 still carry boxes written on the October route; restating them is the lead's.
- The guides against the tree, the link test and the index, read November 18 (the second pull request of that day):
  - `docs/THE_ENGINE.md` §1 to §9 were read against the code: nine card-module cells of the pipeline corrected and all 118 kernels
    placed, the declaration's words and the saved state's lines brought to what `declaration.rs` and `learner.rs` write, and 19
    command words that `athena` routes added to §7's table. §6 stays lap 17's reading and says so.
  - 241 places in the README, `crates/README.md`, THE_REBUILD and nine guides that named an October owner as current name the
    engine's owner or a commit; THE_REBUILD's §3 describes the store line.
  - `tools/link_check.py links` reads every relative link of the root guides, `docs/` and the records' README (75 files, 1,585
    links, none broken), and `link_check.py atlas` reads every atlas owner that names the tree (12,322 owners; 203 were repaired,
    136 of them October owners now pinned at their commit). Both run in gate 1 with their controls.
  - `tools/records_index.py write` writes `research/records/INDEX.md` from the file names (1,685 records by month), and gate 1
    fails while the index is behind them. A change that adds a record regenerates it.
  - Bars that outlived the audit of November 18 outside CLAUDE.md read as dated readings: RETRACTIONS, THE_MACHINE's guard 18, the
    canon's README, the records' README (with October's set-aside pieces routed by subject), the lessons of September 29, the
    record of the stores of October 26, AGENTS.md's executor clause, HNN_FORMULA, HOLON and HNN_ATHENA_FOUNDATION.
  - Still C7's: `docs/THE_MACHINE.md` (20 places) and `docs/plans/HNN_ATHENA_FOUNDATION.md` (14) name October owners in text kept
    as the record of its date; `kernels/field_moment.cuh` names `holonics::hnn::tower::field` (a kernel header's comment changes its
    digest, so it goes with a parity read). The headers of `athena`'s `main.rs`, `engine-cuda`'s `lib.rs` and `hnn/field.rs` were
    brought to the tree with #995.
  - The atlas's grades, read November 18: 110 rows carried a grade outside the README's seven. 27 are `measured`, readings of the
    machine with their record, and the README now declares that grade. 20 carried a status of the October validation queue on Lean
    owners that stand in the library, and are `formal-checked`. 63 rows of the September and October machines, each with an owner in
    history, keep the dated status they were written with. `link_check.py atlas` reads the field in gate 1
    (`ATLAS_GRADES declared=3884 dated=63 broken=0`).

**C10. The close.** C1's reading is run again and its receipt set beside the first; the sizes of §1
are restated by part; `python3 tools/repo_census.py` reads clean on the PC; #603 is closed by hand
with the commits.
- The sizes, read November 18 on `main` at `c50e4612` (lines of tracked files, each with its part; §1's figures of November 14 beside):

  | Part | November 14 | November 18 |
  |---|---|---|
  | All tracked lines | 6,636,715 | 6,280,323 in 13,579 files |
  | Rust and CUDA under `crates/` | about 458,000 | 46,378: `crates/engine` 22,658, `crates/engine-cuda` 18,733 (`kernels/field.cu` 7,711 of them), `crates/athena` 5,062 |
  | `vendor/num-bigint` | | 17,034 |
  | `lean/` | about 641,000 | 617,650 |
  | `tools/` | | 15,143 in 79 files |
  | Guides under `docs/`, the atlas aside | | 27,259 |
  | Records, receipts and papers under `research/` | 71% of the tree | 5,550,480, which is 88% of the tree: receipts 3,618,707, records 1,193,654, the rest 738,119 |
  | `CLAUDE.md` and `AGENTS.md` | 85.7 KB each | 108.7 KB and 3.9 KB |

- The PC's trunk, read November 18 through a mount, which reads and never changes: 68 worktrees stand under `.local/wt`, 35 with a
  `target/`. The line's run scripts read their keys, units and codec from the untracked `.local/` of four of them (`store-trainer`,
  `section-edge`, `field-card`, `depth-sweep`), so those four are kept by name in any sweep, or the line's inputs are first copied
  under the main checkout's `.local/`. The census and the sweep are the host's (the trunk contract).

## 10. Declared extents that stand in for laws

Brandon's critique of November 14: counts written into the pipeline read as rigid engineering
where the theory gives a law. Each is a declaration today. C5 writes this table into
`declaration.rs`, beside each field.

| Extent | Today | The law it stands in for | Where the tree already holds it |
|---|---|---|---|
| The ticks `K` | 4: four applications of the constitution, five states `x⁰` to `x⁴`, the face read from the last | depth from settling: a site ticks until its face stops moving at its receiver's grain | the tick is a running mean whose clock is the logarithm of its count (`tower.field-tick-running-mean`); `read-ticks`, `read-depth` |
| The lanes and their width | lanes of 32, each added by a copy: a third and then a fourth on November 14 | width from the capacity price: a part is as wide as the information it carries pays for | `code.capacity-price`, `radix.register-composition`; the third lane's price read at 0.040 and the fourth's at 0.025 (G188, G189), and a lane's width to be read from its readers' travel (the record of November 14) |
| The reads `R` | 2: the second read marks the engine's own placements | reads until agreement: a region is read until two successive reads agree at the receiver | the mark's record of November 14; Lean `HNN/ReadsTwice` |
| One width as every block's row length | one count, copied | a size belongs to its part | CLAUDE.md, Method, November 12 |

The split of the heads into still and turned stays as declared; he read it as sound.

## 11. What the campaign leaves to the engine's line

The cut makes each of these a change in one module. None is part of #603; each is a build with its
guess fixed first.
1. One family of sum and scan kernels for the pair over its five index sets, and the carry's chain
   read for whether its blocks join to the same bits (§2).
2. A symbol's word on located rings in place of the codec's table of classes.
3. Depth from settling, width from the capacity price, reads until agreement (§10).
4. The deposit realized on the card; it runs on the host today inside a card run.

## 12. Rules while the campaign runs

- A moving pull request is opened and merged the same day, and no law change touches the files it
  moves while it is open. Reason: a move and an edit of the same lines cannot be merged by reading.
- Merges are plain merge commits. Housekeeping runs on the PC's full clone; the cloud's shallow
  clone is read-only for ancestry.
- Nothing is built or run on a cloud box. Text-only steps may be written there.
- The workload is never cut to fit a step: a receipt is read on the line's own sections.
- A retirement deletes by explicit path, after the tag of C3 and with the last commit named.

# The repository restructure: organize around the elementary objects, retire the rest

**Status:** active design, September 23. Claude's whole-repository review supplied the retirement
census and paused-phase handoff; Codex's Rust/Lean dependency review and Brandon's 2–4-crate
direction refine the target below. **Governs** the [consolidation programme](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#consolidation-programme-phases-916)
and its [overgrowth census](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#overgrowth-census-and-retirement-programme-september-23):
retirement comes first, then consolidation of what remains, then the crate and Lean layout below.

[project-postulate] Brandon's rulings (September 22–23): the elementary objects are the only design
vocabulary; the Holon is the foundational object of the Lean mathematics and the Rust machinery; the
repository is Brandon's personal research programme with Brandon, Claude and Codex as its only workers;
consolidation includes deletion, and git history is the archive; names must say what a thing is.

## 1. Why the tree looks like this

[established-bounded; source-inspected] The repository has absorbed several generations of the
framework without retiring the previous one:

| Period | What happened | What it left |
|---|---|---|
| May 10 – Aug 3 | `~/Workspaces/laboratory` (1,658 commits): a Bevy/Avian sandbox became Eros, a deterministic stateful machine ("soma") receiving world events and returning conduct | the soma crates later imported here: `body`, `membrane`, `surface`, `soma-abi`, `mount`, `life`; laboratory itself is frozen and is cited as provenance |
| Aug 3 | holonics founded with a pure canon and a C++ CUDA engine blueprint | `archive/cpp-engine` (retired) |
| Aug 7 – 24 | laboratory law recovered; Eros steps; Phoenix bodies on the card; Athena alpha cultivated; the Millennium frame and catalogue | Rust engine growth; `holonic-life` as the Soma production surface; the Millennium Lean corpus |
| Aug 31 – Sep 9 | moment-front consolidation; HNA ("Holonic Neural Athena") recurrent ecology; SKE (Soulkiller) excitation; byte-history cultivation retired | `holonics-hna` (the acronym never matched the design); `holonic_intelligence` |
| Sep 11 – 20 | Athena plans reorganized; protein/biology applications (Boltz, RBX1, mmCIF) then dropped | physical/physicochemical receivers, protein issues and records |
| Sep 20 – 21 | operating guides consolidated; helical pair interaction, generator machine, incident field | `field_session`, `coupled_wave/body`, incident machine |
| Sep 22 – 23 | elementary objects cemented; the Holon as one object; `holonic-core`; consolidation phases 9, 10, 13, 15, 16 | this plan |

The theory advanced faster than the code was retired. Each new understanding (the Holon as a port
object, retention as a quotient, loss as a log-ratio, equation extraction) was added beside the old
representation, usually with a compatibility alias and a legacy decoder. The result, measured at
`c9012f17`:

- **Rust.** 16 library members and three application packages are declared in the current root
  workspace. `holonic-engine` is 548k lines of source (plus 111k in 178 examples) in one crate.
  `holonic-life` is 314k. By last commit, five crates have not moved since September 4 or earlier
  (`holonic-language` Aug 7; `holonic-body`, `holonic-membrane`, `holonic-surface`,
  `holonic-circulation-abi` Sep 4) and four only as collateral of other work (`holonics-workspace` Sep 8,
  `holonic-structure` Sep 14, `holonic-abi` Sep 18, `holonics` is a 52-line facade). The live crates are
  `holonic-core`, `holonic-words`, `holonic-engine`, `holonics-hna`, `holonic-life`, with
  `relational-geometry` and `holonic-mount` beneath them. Package names disagree with their directories (`holonic-life` →
  `life`, `holonic-body` → `body`, `holonic-mount` → `mount`, `holonic-abi` → `soma-abi`,
  `holonic-membrane` → `soma-membrane`, `holonic-surface` → `soma-surface`).
- **Engine consumers.** 41 engine modules (63k lines) have no referencing file outside themselves; 40
  more (80k lines) have one or two, usually a single example. See the census in the consolidation plan.
- **Lean.** `formal/elementary-holonics/ElementaryHolonics` has 1,387 files and 486k lines. The
  `Framework` closure, which is the actual foundation, is 188k. Millennium is 368k lines in 1,004 files,
  RH 35k. 23 files are imported by nothing. The directory name `formal/` hides the mathematics.
- **Research and docs.** `research/` is 2,576 tracked files (1,298 records, 480 experiment files, 344
  paper files). `archive/` keeps 2,260 tracked files in the tree even though git history is the archive.
  `docs/` has 39 guides and 16 plans.
- **Issues.** 45 open GitHub issues. None tracks the consolidation phases; several track the dropped
  protein work; most have not been updated since September 19–22. Campaign commits stopped citing issues.

These are the `c9012f17` snapshot, not a current deletion verdict. In particular, the current
`holonic-life` source is about 161k lines; the 314k above includes its then-current examples.
Recompute counts and dependency edges at R0. A low reference count does not prove that a theorem,
public API, saved wire or application boundary is disposable.

## 2. What is essential: the restructure is organized around these

[definition] Everything kept must be one of these objects, a composition of them, their device
realization, a boundary chart, or a measurement. The owner columns below name **current**
sources; §3 gives the target layout.

### 2.1 The Holon and its facets (the core)

| Object | Law (one line) | Lean owner now | Rust owner now |
|---|---|---|---|
| Holon `H=(K,∂_A;Π;𝒟;𝓔;G;π)` | the law and its ports, not its state; interconnection of Holons is a Holon; passivity proved | `Holon/{Law,Port,Dirac,Complex,Element,Generator,Restriction,Conformance}` | `holonic-core::{holon,law,port,dirac,complex,element,generator,restriction}` |
| Complex, holon/coholon pairing | `∂²=0`; `d=∂ᵀ`; Stokes; power is the pairing | `Objects/Pairing`, `Holon/Complex` | `holonic-core::complex` |
| Constitution (element relations) | storage `C`, `K`, resistive `D⪰0`, sources, active relations with power, pumps; modes `Kv=ω²Cv` | `Holon/Element`, `Holon/MomentStorage` | `holonic-core::element`; normal law `NormalConstitution`; moment storage |
| Generator | initial configuration (key), clock, phase lift; helix = circle + carry; fractal family = words, restrictions, scale square, first arrival | `Geometry/PhaseCarry`, `Holon/Generator`, `Foundation/FractalPacking` | `holonic-core::generator`; `relational-geometry::winding` |
| Helical pair contact | slip `J`, `Q=⟨Δ|Δ⟩`, `DQ=2J*Δ`, Farey lock address; contact material `ΣwJ*DJ` | `Transport/HelicalPairInteraction`, `Geometry/PairResonance`, `Millennium/Farey` | `holonic_interaction`, `holonic_chain`, `relational-geometry::screw` |
| Parametron | LC storage↔flow at `ω=1/√(LC)`, pump, half-turn Ising lock; perceptron = locked-sheet face | `Objects/Parametron` | `cuda_refine::complex_parametron` (device); no host owner yet |
| Tube, tower | longitudinal clocked span; transverse restriction with unique/plural/obstructed gluing; `Λ_DN` | `Transport/ContinuingTube`, `Foundation/IwasawaTower` | `holonic-core::restriction::{tube,tower,fibre,descent}` |
| Relative completeness (globe) | boundary bounds interior; coupled by conserved charges, not determined; persistent motion | `Objects/RelativeCompleteness` (full theorem owed, #62) | none |
| Deposition and retention | the only law changing a constitution; retention = future-sufficient quotient, never a tape | `Objects/{Deposition,Retention}`, `Foundation/Standing`, `Holon/Deposition` | `holonic-core::deposition`, `standing` |
| Ratio and loss | `R=Ĝ_(T←H)`, `ℓ=log R` with winding branch, covector `R⁻¹dR`, jets | `Objects/{Ratio,RatioPhase,RatioBlock}` | `exponentiated_ratio`; incident receivers |
| Receipt | field of per-region readings, own frame and clock; no global scalar | none | readings in each owner; bits readings in the exposure measurement |
| Keys and navigation | action fits a constitution (lock); learning = locating keys by loop closure (Bombe) | `Transport/{GeneratorTraceFaces,CellHolonomy}` | `relational-geometry::winding::Machine` |
| Reaction (power-neutral, Cayley step) | skew reaction; `(I−½K)y=(I+½K)p+W_c c`, gain 1 | `Holon/{Reaction,Cayley}` | `holonic-core::reaction`; `normal/direct/reaction_law.rs`; `kernels/enclosure_cayley.cuh` |

Exact algebra underneath: `exact_linear`, `prime_image_algebra`, `inertia`, `rational_polynomial`,
`primality`, `ExactRing`/`ModularWords` (now in `holonic-core`/`holonic-words`).

### 2.2 The machine (HNN) built from them

One continuing field: chains of parametron rings joined by helical pair contacts; the source enters as
phase-carried moments `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`; standing `q` and incident `Δ` feed the power-neutral
reaction; participation drives; one global `D/b`; receivers are Holons at ports; deposition changes the
constitution; the return reads the contemporary constitution. Owners now: `holonics-hna`
`native/{coupled_wave/body/field/incident*, field_session/*, field_geometry/machine*}` and engine
`native_ecology/constitutive_fibre/field/**`. Open work: GitHub #17, #16, #18, #61; source-port growth of
ring g0; closing the model-versus-uniform gap on the exposure sample.

### 2.3 Its device realization

Exact enclosure arithmetic on the card (sealed carrier words, radii, `SLOT_WORDS` receipts, Cayley step
kernels), the hardware cover and section partition, the device quadratic moment. Owners now:
`holonic-mount`, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`.

### 2.4 Boundary charts and measurement

- Text and conversation: the exposure source and cursor (`alpha/exposure.rs`, `examples/athena_exposure_field.rs`),
  conversation data (`applications/conversation-data`), bits readings (`field_session/measurement*`).
- Equation extraction ("Soulkiller" is only the name): foreign graph intake and the extracted operator
  (`holonic_intelligence`, `soulkiller`, `foreign_*`).
- Motor/robotics: intended; Isaac Sim is the kinetic standard; the articulated body is a chain of
  `SituatedScrew`s (`holonic_chain`). Not scheduled.
- The workbench CLI (`applications/holonics-workbench`).

### 2.5 Research mathematics as instances

Millennium (NS/Euler, Hodge, BSD, RH, P vs NP, Yang–Mills), Iwasawa, `Λ_DN`, Einstein: keep a
distinct theorem, derivation or open attempted construction when its hypotheses and conclusion
remain meaningful, including a standalone mathematical consumer. Connect reusable laws to the
elementary object they instantiate (winding ledgers, local factors, Farey, trace sequences,
heat flow); retire duplicate wrappers and failed names, not a subject because HNN does not
import it. A theorem is kept once, beside the object it instantiates.

## 3. Target layout

[project-postulate; agent-inferred] Names say what a thing is; package name = directory name.
Use **HNN** only for the established neural machinery; do not name new packages after lineage
(`soma`, `life`, `hna`), vague roles (`body`, `membrane`, `surface`, `mount`) or a product.
R0 may refine module placement, while the four-library ceiling and dependency direction guide
the cut.

### 3.1 Rust: the main `holonics` library owns the construction

The main package must be a **substantive library**, not the present 52-line facade. It owns the
Holon law, exact geometry and algebra, elementary operations and the backend-neutral HNN. A
separate HNN package would force the foundational package to depend on its implementation to
keep `holonics::hna`, closing the dependency cycle. Keep HNN as an internal module until an
actual post-retirement build/profile result justifies a public-path migration.

The target is three maintained libraries on this branch, four when Brandon adds Apple:

| Package | Internal ownership | Existing sources to sort at R0 |
|---|---|---|
| `holonic-words` | Small portable exact word ring and packet/section ABI shared by host and device, with a `no_std` arithmetic kernel compiled from one source. It owns the layout and refusal words both sides must agree on. No driver or HNN dependency. | `holonic-words` plus the shared `soma-abi::section_layout_cuda` law and validated layout definitions. Its present dependency on `soma-abi`/`body` must be reversed or retired. |
| `holonics` | Main library: the Holon and its facets, exact/geometry support, pair contact, parametron, tube/tower, deposition/retention, ratio/receipt, equation extraction as a Holon boundary, and an internal `hnn` module with a host/reference executor. No CUDA dependency. | `holonic-core`, `relational-geometry`, live `holonic-structure`, source-neutral and HNN parts of `holonic-engine`, `holonics-hna`, live `holonic-life`. |
| `holonics-cuda` | CUDA implementation of declared Holonics/HNN operations: driver, allocation, launch/section layout, resident kernels, checked receipts and transfer completion. It depends on `holonics` and `holonic-words` and implements the HNN execution port; it does not redefine the material or loss law. | `holonic-mount`, device ABI owners, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`. |
| `holonics-apple` (later) | Apple silicon implementation behind the same typed execution port, with its own kernels and placement. Create it only on Brandon's Mac branch after its actual implementation is ready. | No Linux-branch move. |

The dependency direction is `holonic-words → holonics → holonics-cuda` (and later
`holonics-apple`); arrows mean *may be used by*. Applications select a backend and depend on
`holonics` plus that backend. The current workbench remains an application package while R0
checks its deployment boundary; the 2–4 ceiling above counts maintained reusable libraries,
not a CLI's separate Cargo binary target. The main library's default build must work without
a CUDA SDK, driver or linker symbol. HNN is a feature/module inside it, with an exact host
reference. A CUDA caller passes `CudaExecutor` through the HNN execution port rather than
making `holonics` import the CUDA package. `holonics::hna` can remain a compatibility module
for the established API and wire names while its implementation is organized under `hnn`.
Device-specific constructors migrate to the backend package where necessary; name each
consumer and saved artifact before removing a path.
Initially keep `hnn` in the main package's default features to preserve public HNN imports;
`--no-default-features` is the lean source-neutral Holon build. No `cuda` feature on main may
introduce an edge back to `holonics-cuda`; applications select that dependency explicitly.

The internal source tree is organized by the elementary objects and their actual compositions:

```text
crates/holonics/src/
  lib.rs                 public typed entry; feature declarations and narrow re-exports
  holon/                 one Holon law: complex, ports/Dirac, elements, generators, restriction
  geometry/              exact frames, screw, phase carry, lock address, cell holonomy
  pair/                  helical contact, slip, quadrance and material return
  parametron/            LC storage, pump, sheets and locks (host law)
  tube/                  longitudinal transfer, tower restrictions and gluing
  deposition/            reached covectors, constitution change and retention quotient
  ratio/                 typed comparison, log branch and jets
  receipt/               per-region framed/clocked readings
  exact/                 rational, algebraic and word-backed implementation carriers
  extraction/            foreign equations as Holon element/generator relations
  hnn/                   field, source moments, generator inference, receiver, adjoint, session
```

`holon` is the one definition of the port object; `pair`, `parametron`, `tube`, `deposition`,
`ratio` and `receipt` are its elementary laws and compositions, not duplicate root Holons.
`exact` is supporting representation, not a competing ontology. `hnn` assembles those laws
into the continuing field; it does not copy their definitions. Most submodules should be
private until an actual caller needs a public contract. Application codecs (text, image,
motor) remain boundary charts at their consumers. The current engine's blanket public modules
and glob exports are not copied into this tree.

The root exports only the central `Holon` type and deliberate qualified modules. A caller
uses `holonics::pair`, `holonics::ratio` or `holonics::hnn`, not a flat engine-wide glob.
Preserve `holonics::geometry`, `holonics::structure` and `holonics::hna` as audited forwarding
paths while their real consumers migrate; each forwarding path has a removal decision tied
to a named caller or saved wire. In Lean, the public `Holonics` root imports the corresponding
object owners and a curated HNN specialization; `HolonicsResearch` imports that root. Exact
module/file names are settled against the existing proof import graph, not invented by copying
the Rust directory tree.

The HNN execution port is defined at its surviving consuming call, including the forward
field, complete geometry/feature pullback, material return, source order, receiving phase and
receipt. The host/reference implementation and CUDA implementation must return the same typed
relation at their stated precision. The present graph does **not** satisfy this cut: engine
imports `mount`; HNA imports engine and life; `holonic-words` imports `soma-abi`. Sever those
edges, preserve the shared arithmetic implementation, then move code. A module with a distinct
mathematical consumer survives in its object owner; unconsumed legacy scaffolding retires.

A separate `holonics-hnn` package is a measured fallback, not the default design. If the
surviving HNN still makes main-library rebuilds untenable after retirement, record that cost and an API
migration that keeps wire/schema identifiers and a named public entry; an HNN split must not
turn `holonics` back into a facade or duplicate elementary laws.

### 3.2 Lean: one Lake package, two import closures

Move the current package to top-level `lean/` in a separate mechanical phase. Its maintained
libraries are `Holonics` (the public elementary-object and Framework closure) and
`HolonicsResearch` (research instances with their own theorems and live mathematical consumers,
depending on `Holonics`). `Holonics` must not import `HolonicsResearch`. A standalone mathematical
theorem is a consumer in its own right; absence from the HNN build is not a deletion reason.
The present `ElementaryHolonics.lean` umbrella imports almost all of Millennium and RH; replace
it with curated roots rather than renaming that umbrella and calling it the foundation.
The public root presents `Holon`, pair contact, parametron, tube/tower, deposition/retention,
ratio/receipt and their geometry in the same object order as the Rust main library. HNN
theorems are a dependent specialization **inside** `Holonics`; `HolonicsResearch` contains
independent mathematical instances and cannot become an alternate foundation.

Generate the import closures before classifying files. Keep `Holon/`, `Objects/` and the
Framework's actual transitive owners together; sort `Geometry/`, `Transport/`, `Foundation/`,
`Physics/`, `Computation/`, `Algorithm/`, `Mathematics/`, `Millennium/` and `RH/` by dependency and
consuming theorem, not by folder name. Preserve the current `Soma.Holonics.*` declaration namespace
through the path move. Rename it to `Holonics.*` only in a later mechanical phase with all imports,
citations and proof clients updated and both library targets building.
If a current Millennium/RH module supplies a law imported by the core (for example Farey
addresses), move that law into the `Holonics` object owner and let `HolonicsResearch` import it;
never make the foundation depend on a research umbrella or copy the theorem in both roots.

Update Lake roots and executables, `tools/lean_check.sh`, CI, Rust Lean-citation tests, source
comments, docs/verification receipts, AGENTS.md and CLAUDE.md in the move. A link/import census
must catch every remaining `formal/elementary-holonics` and `ElementaryHolonics` reference.

### 3.3 Documents

- Top level: `README.md` gives the current map and target in one screen during migration, then
  the final map: public crate, HNN, device, Lean, docs, research and applications.
- `docs/`: the guides (`THE_MACHINE`, `ELEMENTARY_OBJECTS`, `HOLON`, `HNN_FORMULA`, notation, winding,
  helical geometry, development) and `plans/` (roadmap, this plan, the consolidation plan). Guides whose
  subject is retired are deleted; their live definitions move into `ELEMENTARY_OBJECTS`.
- `research/records/`: keep records that carry a distinct derivation, measurement, failed attempt
  or live provenance, including direct-message evidence, even when no current source imports them.
  Fold genuinely duplicate summaries into their guide. `research/papers/rendered` and
  `experiments/` need an artifact/source census; generated copies may be regenerated from kept
  sources only when that regeneration has been checked.
- `archive/`: delete from the tree (git history keeps it); CLAUDE.md/AGENTS.md cite revisions instead.
- Laboratory: stays frozen outside this repository; cite it by revision; import nothing further.

### 3.4 Operator contracts and acceptance

The package boundary follows the operation, not the old module tree. Each moved operator has
one owner and a short mapping in the census: supplied Holon/source and receiver; inferred
unknown; forward law; paired variation or proof obligation; CPU reference; device realization
if any; saved/wire face; consuming call. A move changes paths and dependency edges, not the law.
The HNN field still owes both terms of `δT=Σ a δ(UΨ)+Σ δa UΨ`; deposition changes the
constitution from covectors that reached the locus, and loss remains the logarithm of a typed
Holon ratio with its winding. A CUDA kernel's sealed-word/radius distinction, complete
`SLOT_WORDS` receipt, transfer completion and device placement remain device contracts, not
properties silently supplied by a new crate name. Lean proves named laws at their scope and
does not enter the runtime.

Before retiring an old package, verify a source-neutral `holonics` build without its HNN
feature, a host/reference HNN build, CUDA owner tests on the available card, an all-target
public/workbench check, the
two Lean library targets and the changed source-to-Lean citation/link scan. Inspect a saved
session through the new public path when one is named as retained. Record the specific commands
and results in the census; a build of an intermediate move is not the completed boundary check.

## 4. Order of work

1. **R0 census (first, nothing retired before it).** Record the exact HEAD, dirty files,
   worktrees/branches, build outputs and saved artifacts. Preserve the current uncommitted
   Lean/research work and paused WIP branches. Produce `docs/plans/THE_REPOSITORY_CENSUS.md` with
   one table per Rust owner/example, Lean import closure/standalone theorem, document/record and
   issue: path, elementary object or application, direct and transitive consumers, public/wire
   use, distinct result or superseding owner, disposition (**keep and own** / **fold** /
   **retire**), target and verification. Static references are leads, not proof of liveness or
   deadness. Verify proposed removal in grouped, reviewable cuts with all-target builds and
   owner tests; use Lean import closures plus named theorem/citation consumers. Show the census
   and concrete cuts to Brandon without making the inventory an indefinite approval gate.
2. **R1–R3 retirement passes** in the order engine/examples, life/soma crates, Lean research.
   For each cut, check the surviving workspace and actual consumers; for Lean, build both
   maintained libraries and the relevant research target after it exists. Until the move, build
   the existing `ElementaryHolonics.Framework` target and affected research modules. Keep
   theorem/record evidence not captured by an import count. See the consolidation plan's census.
3. **R4 compatibility debt:** remove aliases and legacy decoders not needed by a named saved artifact.
   Saved Athena coupled models from September 11 already fail to load; old sessions under
   `.local/campaign-2026-09-20` are superseded checkpoints.
4. **Finish the paused consolidation** (phases 11, 12a, 12b on their WIP branches; phase 14) on what
   remains. Rebase them after R1–R3.
5. **Layout moves (§3):** sever dependency cycles, establish backend-neutral HNN and CPU-only
   main-library checks, then move/rename packages in mechanical commits. Move Lean paths and roots
   separately from declaration-namespace edits. Keep the old `hna` and wire identifiers as
   described in §3.1 while their live consumers are migrated.
6. **Documents (§3.3)** and the GitHub issue reset (§5).
7. **Update CLAUDE.md and AGENTS.md** owner tables, `CONSTRUCTION_STATE.md`, the roadmap,
   `docs/REPOSITORY.md`, root README and mathematical/operator owner links to the verified new
   paths. During migration, operator guides label present paths and planned owners separately.

Build hygiene starts now: use one shared scratch target directory and
`CARGO_PROFILE_DEV_DEBUG=line-tables-only`; inspect each target/cache's owner before reclaiming
generated output. Remove a WIP branch's target only after its source is integrated or otherwise
preserved. The old engine graph's incremental output can be cleared after the split; do not use
`git clean`, blanket worktree deletion or a broad restore against the dirty research tree.
The current root `target/` measured **216 GiB** on September 23 (`du -sh target`); it is generated
build output, not a source-retention obligation. R0 records which active checks still need it
before a targeted or post-split `cargo clean` reclaims the space.

## 5. GitHub issues

- **Reset.** For each of the 45 open issues: keep (maps to an object in §2 and a live owner), fold
  into another issue, or close with a one-line reason and the superseding commit/record. Candidates to
  close or fold: the protein/structure issues (#11, #38, #44, #46, #51, #52, #53) after the biology
  pivot away; device issues (#12–#15, #50) fold into one device-realization issue after §3.1; Lean
  obligations fold into #62 and its successors.
- **Track the restructure.** Keep one parent issue and separately testable cuts where their
  owner and return differ: census/retirement, paused consolidation, Rust dependency cut,
  Lean-library move, and docs/consumer migration. Link them from this plan when created.
- **Practice from now on.** Every campaign cites its issue in the plan and in commit messages
  (`Refs #n`/`Closes #n`); a closing comment gives the commit, the verification receipt and any
  remaining scope; labels follow §2's objects (`holon`, `generator`, `pair-contact`, `parametron`,
  `tube`, `deposition`, `ratio`, `device`, `extraction`, `lean`, `research-math`) replacing the older
  label set.

## 6. Current state to carry

- Landed consolidation: phases 9, 10, 13, 15, 16 (`5c4bb58a`, `4dff57c8`, `5b7c89ab`, `7e204283`, `009e8363`).
- Paused, unverified: `wip/consolidation-phase-{11,12a,12b}` (worktrees `.local/p11-wt`, `.local/p12a-wt`,
  `.local/p12b-wt`), described in the consolidation plan's handoff section. Phase 14 remains open.
- Uncommitted in the main tree: RH, Millennium and Computation Lean files and September 22–23 records
  from recent mathematics work. These are ours; R0 commits or retires them.
- Measured machine position (campaign 1): exposure sample 516 frames / 13 returns, no refusals; receiver-ring
  energy bounded under the Cayley word; model/uniform 1.108× (still worse than uniform); ring g0 grows
  through the source port. These stay the machine's open items after the restructure.

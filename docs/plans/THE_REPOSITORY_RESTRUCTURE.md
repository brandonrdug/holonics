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
realization, a boundary chart, or a measurement. The owner column is the target home; §3 gives the layout.

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

### 3.1 Rust: four maintained libraries, one dependency direction

The 2–4 ceiling is for maintained Rust library packages. The target is four, including the
public `holonics` package. The workbench becomes a binary target of the public package; the
derivation atlas and plate are folded into an owning package's examples/tools or retired after
their R0 consumer check. Conversation-data remains a data preparation application. Do not create
an empty Apple package on this Linux branch.

| Target package | Owns | Existing sources to sort at R0 |
|---|---|---|
| `holonic-core` | The Holon law and ports, elementary objects, exact algebra, exact word rings, geometry (frames, screws, winding, contacts, holonomy) and source-neutral receiver/restriction laws. No CUDA, HNN session or product dependency. | `holonic-core`, `relational-geometry`, `holonic-words`, live `holonic-structure` and source-neutral engine owners. |
| `holonics-hnn` | Backend-neutral HNN: constituted field, helical pair interaction, generator machine, standing/deposition, ratio comparison, phase-carried source moments, receivers, session, rest and complete adjoint. Equation extraction lives here while its operative consumer is the machine. | `holonics-hna`, live `holonic-engine`/`holonic-life` machine owners, `holonic_intelligence`, `soulkiller`, `foreign_*`. |
| `holonics-device` | Device realization and host/device exchange: CUDA driver, launch/section layouts, exact enclosure kernels, receipts, hardware cover and resident sections. `cuda` is the implemented backend; an Apple backend may join later behind the same declared machine operation, on Brandon's separate branch. Share laws only when both backends implement the same contract. | `holonic-mount`, device ABI/layout owners, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`. |
| `holonics` | Main public crate and stable entry point. It exposes the core unconditionally and the HNN/device interfaces through explicit features and re-exports; it owns the CLI binary target but no second copy of a mathematical law. | Current `holonics` facade and live workbench. |

The dependency graph is `holonic-core → holonics-hnn → holonics-device → holonics` (the public
crate also depends directly on core and HNN); arrows mean *may be used by*. The HNN defines the
backend operation and a host/reference executor; the device package implements it. Neither the
core nor HNN imports a CUDA symbol, type or linker dependency. The public package selects CUDA
explicitly rather than making it the default on non-CUDA hosts. This cut must be demonstrated
by `cargo metadata` and a CPU-only build before files move. The present graph does **not** have
this property: engine imports `mount`, HNA imports engine and life, and `holonic-words` reaches
the legacy `soma-abi`/`body` chain. Detach those edges before merging or renaming packages.
The intended public feature policy is a CPU-capable default (`hnn` with its reference executor)
and opt-in `cuda`; the later Apple feature is platform-scoped. `holonics::hna` can remain a
public compatibility path through the facade while its implemented owner becomes
`holonics-hnn`. Feature names and re-export scope are checked against workbench callers and
saved artifacts before the old `native` feature is retired.

Within that graph, core owns the one `Holon` declaration and its `complex`, `port`, `element`,
`generator`, `restriction`, `pair`, `parametron`, `deposition`, `ratio` and `receipt` laws, with
exact geometry/algebra as their implementations. HNN owns compositions of those operations:
the pair-contact graph, constituted field, source moments, participating receiver, deposition
return and session. Its backend boundary accepts the same typed Holon/material/current and
returns the same receiving section and covector/receipt in the reference and CUDA paths. The
device package owns CUDA allocation, placement, kernels and checked transfer; it cannot invent
a different loss or material update. The public crate chooses an implementation and presents
stable paths. The concrete Rust trait signatures follow the surviving HNN consuming call at R0;
do not design a generic backend trait before that call and its adjoint are inspected.

HNN warrants its own package because its field/session implementation and change rate are
substantial, while source-neutral Holon mathematics must compile and be used without it. The
public `holonics::hna` and other established Rust paths receive an audited migration map; keep
only compatibility re-exports needed by live callers during the move. Wire/schema identifiers
and usable saved artifacts retain their existing contracts unless a named migration changes
them. A final path removal is not inferred merely from a package rename. Extraction is an HNN
module at this boundary, not a fifth package; if it proves independently reusable, revisit the
boundary with actual consumers instead of anticipating one.

Retire or fold after R0: `holonic-body`, `holonic-membrane`, `holonic-surface`,
`holonic-circulation-abi`, `holonics-workspace`, `holonic-language`, `holonic-structure`, the
remainder of `holonic-life` and `holonic-engine`, and unused `accelerators/` targets. An event-law
module with a distinct theorem or live consumer moves to its object owner; one with neither is
retired. A package count is an outcome of those owner decisions, not a reason to suppress a law.

### 3.2 Lean: one Lake package, two import closures

Move the current package to top-level `lean/` in a separate mechanical phase. Its maintained
libraries are `Holonics` (the public elementary-object and Framework closure) and
`HolonicsResearch` (research instances with their own theorems and live mathematical consumers,
depending on `Holonics`). `Holonics` must not import `HolonicsResearch`. A standalone mathematical
theorem is a consumer in its own right; absence from the HNN build is not a deletion reason.
The present `ElementaryHolonics.lean` umbrella imports almost all of Millennium and RH; replace
it with curated roots rather than renaming that umbrella and calling it the foundation.

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

Before retiring an old package, verify a source-neutral `holonic-core` build, a host/reference
HNN build, CUDA owner tests on the available card, an all-target public/workbench check, the
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
   core checks, then move/rename packages in mechanical commits. Move Lean paths and roots
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

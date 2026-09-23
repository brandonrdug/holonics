# The repository restructure: organize around the elementary objects, retire the rest

**Status:** plan, September 23. Written by Claude (Opus 5.5) from a whole-repository review; GPT-6 (Codex)
iterates on it and executes it. **Governs** the [consolidation programme](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#consolidation-programme-phases-916)
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

- **Rust.** 16 crates. `holonic-engine` is 548k lines of source (plus 111k in 178 examples) in one crate.
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

Millennium (NS/Euler, Hodge, BSD, RH, P vs NP, Yang–Mills), Iwasawa, `Λ_DN`, Einstein: kept where a
Framework owner, a live campaign or a cited record uses them, as instances of the objects above
(winding ledgers, local factors, Farey, trace sequences, heat flow). A theorem is kept once, beside the
object it instantiates.

## 3. Target layout

[project-postulate; agent-inferred] Names say what a thing is; package name = directory name; no
acronyms, lineage names (`soma`, `life`, `body`, `membrane`, `surface`, `mount`, `hna`) or product names
in crate names. Codex refines this after the census (§4), which may merge further.

### 3.1 Rust crates

| Target crate | Contains | From |
|---|---|---|
| `holonic-core` | the Holon object and facets; exact algebra; exact machine words | `holonic-core`, `holonic-words` (fold in), exact parts of `holonic-structure` |
| `holonic-geometry` | exact frames, screws, pairs, winding/carry/address, cell holonomy | `relational-geometry` (rename) |
| `holonic-device` | CUDA driver boundary, word layouts, enclosure kernels, hardware cover, section partition, resident section, device moment | `holonic-mount`, `holonic-abi`, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition` |
| `holonic-machine` | the HNN field: constitution, generator machine, incident body, reaction, deposition, receivers, session, rest | engine `native_ecology/constitutive_fibre/**`, `holonic_interaction`, `holonic_chain`, `standing`, `receiver_release`, `exponentiated_ratio`; `holonics-hna` `native/**`; the live parts of `holonic-life` |
| `holonic-extraction` | foreign graph intake and the extracted operator | engine `holonic_intelligence`, `soulkiller`, `foreign_*`, low-precision weights |
| `holonics` | the public facade re-exporting the above | `holonics` |
| applications | `holonics-workbench` (CLI), `conversation-data` | keep; `derivation-atlas`, `holon-plate`: census |

Retire or fold after the census: `holonic-body`, `holonic-membrane`, `holonic-surface`,
`holonic-circulation-abi`, `holonics-workspace`, `holonic-language`, `holonic-structure`, the remainder of
`holonic-life` and `holonic-engine` (event laws, receivers and mathematics with no consumer), and
`accelerators/` (`rust-gpu`, `cuda-smoke`, `cuda-kernel`) unless the device crate uses them. The 26
event-law modules either become instances inside the owner of the object they instantiate or are deleted
(most have no consumer; phase 16 unified their scaffolding before this was known).

### 3.2 Lean

Move `formal/elementary-holonics` to a top-level `lean/` (one Lake package), with two libraries:

- `Holonics`: the foundation: `Holon/`, `Objects/`, `Geometry/`, `Transport/`, `Foundation/`, `Physics/`,
  and the `Framework` entry points renamed as the library's sections (Core, Geometry, Dynamics,
  Information, Physics, Computation). Only the `Framework` closure (188k lines) plus files a live
  consumer cites.
- `HolonicsResearch`: Millennium and RH, depending on `Holonics`; kept per §2.5, the rest deleted.

Update `tools/lean_check.sh`, the engine `lean_citations` test, `lakefile`, CLAUDE.md and AGENTS.md
paths in the same commit. The namespace `Soma.Holonics.*` in current files becomes `Holonics.*`.

### 3.3 Documents

- Top level: `README.md` gives the map in one screen: crates, `lean/`, `docs/`, `research/`,
  applications.
- `docs/`: the guides (`THE_MACHINE`, `ELEMENTARY_OBJECTS`, `HOLON`, `HNN_FORMULA`, notation, winding,
  helical geometry, development) and `plans/` (roadmap, this plan, the consolidation plan). Guides whose
  subject is retired are deleted; their live definitions move into `ELEMENTARY_OBJECTS`.
- `research/records/`: keep records a guide, plan, issue or Lean/Rust owner cites; fold superseded
  records into their guide; delete the rest. `research/papers/rendered` and `experiments/`: census.
- `archive/`: delete from the tree (git history keeps it); CLAUDE.md/AGENTS.md cite revisions instead.
- Laboratory: stays frozen outside this repository; cite it by revision; import nothing further.

## 4. Order of work

1. **R0 census (first, nothing deleted before it).** One table per area (engine modules, life modules,
   other crates, examples, Lean files outside `Framework`, research records, docs, issues) with columns:
   path, lines, consumers (build-confirmed: delete the module on a branch and run
   `cargo check --workspace --all-targets`; for Lean, the import closure), the elementary object it
   serves (§2) or none, superseded by, disposition (**keep and own** / **fold into owner** / **delete**),
   target (§3). Put the tables in `docs/plans/THE_REPOSITORY_CENSUS.md`. Brandon reviews the
   **keep** column; everything else proceeds.
2. **R1–R3 deletion passes** in the order engine/examples, life/soma crates, Lean research,
   each with a workspace check, `lake build Holonics` (the Framework closure) and the surviving
   suites. See the consolidation plan's census section.
3. **R4 compatibility debt:** remove aliases and legacy decoders not needed by a named saved artifact.
   Saved Athena coupled models from September 11 already fail to load; old sessions under
   `.local/campaign-2026-09-20` are superseded checkpoints.
4. **Finish the paused consolidation** (phases 11, 12a, 12b on their WIP branches; phase 14) on what
   remains. Rebase them after R1–R3.
5. **Layout moves (§3):** crate renames/splits and the Lean move. Moves are mechanical commits (no logic
   changes) so the history stays readable.
6. **Documents (§3.3)** and the GitHub issue reset (§5).
7. **Update CLAUDE.md and AGENTS.md** owner tables, `CONSTRUCTION_STATE.md`, the roadmap and
   `docs/REPOSITORY.md` to the new layout.

Build hygiene during the work: one shared scratch target directory, `CARGO_PROFILE_DEV_DEBUG=line-tables-only`,
delete a branch's target when it lands; `cargo clean` the main `target/` after the crate split (its
150 GB of incremental state is for the old crate graph).

## 5. GitHub issues

- **Reset.** For each of the 45 open issues: keep (maps to an object in §2 and a live owner), fold
  into another issue, or close with a one-line reason and the superseding commit/record. Candidates to
  close or fold: the protein/structure issues (#11, #38, #44, #46, #51, #52, #53) after the biology
  pivot away; device issues (#12–#15, #50) fold into one device-realization issue after §3.1; Lean
  obligations fold into #62 and its successors.
- **Track the restructure.** One issue per step in §4 (R0 census, R1–R3, R4, consolidation 11/12/14,
  crate layout, Lean move, documents), each linked from this plan.
- **Practice from now on.** Every campaign cites its issue in the plan and in commit messages
  (`Refs #n`/`Closes #n`); a closing comment gives the commit, the verification receipt and any
  remaining scope; labels follow §2's objects (`holon`, `generator`, `pair-contact`, `parametron`,
  `tube`, `deposition`, `ratio`, `device`, `extraction`, `lean`, `research-math`) replacing the older
  label set.

## 6. Current state to carry

- Landed consolidation: phases 9, 10, 13, 15, 16 (`5c4bb58a`, `4dff57c8`, `5b7c89ab`, `7e204283`, `009e8363`).
- Paused, unverified: `wip/consolidation-phase-{11,12a,12b}` (worktrees `.local/p11-wt`, `.local/p12a-wt`,
  `.local/p12b-wt`), described in the consolidation plan's handoff section.
- Uncommitted in the main tree: RH, Millennium and Computation Lean files and September 22–23 records
  from recent mathematics work. These are ours; R0 commits or retires them.
- Measured machine position (campaign 1): exposure sample 516 frames / 13 returns, no refusals; receiver-ring
  energy bounded under the Cayley word; model/uniform 1.108× (still worse than uniform); ring g0 grows
  through the source port. These stay the machine's open items after the restructure.

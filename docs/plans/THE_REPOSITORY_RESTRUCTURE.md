# The repository restructure: organize around the elementary objects, retire the rest

**Status:** active design, September 23. Claude's whole-repository review supplied the retirement
census and paused-phase handoff; Codex's Rust/Lean dependency review and Brandon's 2–4-crate
direction refine the target below. **Governs** the [consolidation programme](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#consolidation-programme-phases-916)
and its [overgrowth census](THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md#overgrowth-census-and-retirement-programme-september-23):
retirement comes first, then consolidation of what remains, then the crate and Lean layout below.
Finalized by Claude's review of the Codex iteration (September 23): §0 states the decisions, and the
body sections are edited to agree with it.

[project-postulate] Brandon's rulings (September 22–23): the elementary objects are the only design
vocabulary; the Holon is the foundational object of the Lean mathematics and the Rust machinery; the
repository is Brandon's personal research programme with Brandon, Claude and Codex as its only workers;
consolidation includes deletion, and git history is the archive; names must say what a thing is.

## 0. Final decisions

[project-postulate; source-inspected] These settle the questions the Codex iteration left open.
Each is backed by a measurement at `d3b8b509`.

1. **Lean holds the mathematics; Rust holds what runs.** An unconsumed Rust module is deleted. If
   it carries a law that no Lean owner or guide states, that law moves there first, or it gets a
   #62 obligation. A checked Lean theorem is kept unless it duplicates another or wraps a
   superseded name. A record is kept if a guide, plan, issue or owner cites it, or if it is the
   only statement of a result. Otherwise it is folded into its guide as one line with a revision
   link, or into [RETRACTIONS](../RETRACTIONS.md) if the attempt failed, and then deleted. Git
   history is the archive.
2. **No forwarding modules, path aliases or feature-gated compatibility layers.** Every Rust
   caller is in this repository, so a move updates its callers in the same commit.
   `holonics::hna`, `holonics::structure` and similar paths are not kept. **Every old
   save-format reader goes** (Brandon, September 23): a saved artifact in an old format is a
   superseded prototype, so no legacy decoder is kept. `.local/artifacts` and `.local/campaign-*`
   stay on disk as private evidence, not as formats the code must read.
3. **The HNN is device-resident today; extract its smallest backend-neutral seam before moving
   its resident implementation.** Of 219 `native_ecology` files, 106 launch kernels or hold resident
   sections. So do 35 of 93 `holonics-hna` files. No host reference implementation of the HNN field
   exists, and `holonic-engine/build.rs` runs `nvcc`. The intended resident HNN still moves
   behavior-for-behavior into `holonics-cuda::hnn`. The measured package graph sets a prerequisite:
   `holonic-engine` depends on both `holonics` and `holonics-cuda`, while `holonics-cuda` currently
   depends on `holonics` and `holonics-portable`. Moving engine-owned code into CUDA before removing
   the engine-to-CUDA edge would create the Cargo cycle
   `holonic-engine -> holonics-cuda -> holonic-engine`. Its current consumers add a second
   constraint: `holonic-life` depends on both engine and CUDA, and `holonics-hna` depends on engine
   and life. Retarget those callers as part of the owner move; they do not authorize a reverse
   dependency from the backend into engine.

   The resident closure is larger than `resident_section.rs`: its nested `resident_section/**`
   modules call CUDA and import `holonic-engine::cuda_aperture::DerivedLaunch` and
   `embedding_fiber::{MountedReadout, ResidentReadout}`; the constitutive field at
   `native_ecology/constitutive_fibre/field.rs` and its `field/**` operators consume those sections
   and engine-owned current, wave, circulation and material owners; `embedding_fiber` itself owns
   CUDA-resident reads. The CUDA kernels under `holonic-engine/kernels/` are compiled by the engine's
   `build.rs`. HNA session consumers live in `holonics-hna/src/native/**`, and some device lineage
   consumers live in `holonic-life`. These owners must move or be retargeted with their consuming
   call; moving only the section module cannot invert the dependency.

   The first M1 packet is a backend-neutral boundary in `holonics::hnn` for the resident field's
   input section, returned section/receipt, and typed refusal, using the already shared
   `holonics-portable::wire` layout where host and device need identical words. Main owns the
   backend-neutral values, ordering and receipt meaning; it owns no CUDA handle, allocation,
   launch, stream, or device buffer. CUDA owns the resident allocation and converts to/from the
   shared words. The first implementation packet is: define this boundary in `holonics::hnn`, move
   the existing section-rest/receipt value owner to it, and retarget the current resident field
   call and its tests to consume/return that value. Keep the device section and its behavior in its
   existing owner for this packet. Do not add a crate, forwarding module, compatibility alias, or
   speculative public trait signature. This extraction is only the dependency-inversion seam: it
   does not claim a host reference or full method-by-method conformance.

   The section/receipt seam is necessary but not sufficient to move the field. Before the resident
   closure can compile in CUDA, M1 also moves or recasts the engine-owned current, wave, material
   and readout value owners it imports as main-library mathematical values or typed boundary
   operands. `DerivedLaunch` describes device admissions and belongs with the CUDA section/launch
   owner. The engine's other CUDA callers must likewise move to CUDA or call through a main-owned
   boundary, until no engine-to-CUDA edge remains. Keep device buffers, kernels, launch and
   completion in CUDA; do not pull them into main to satisfy an import.

   After these dependency cuts, M1 moves the resident closure with its current behavior, kernels
   and `build.rs` into `holonics-cuda::hnn`, updates HNA/life callers, and removes every
   `holonic-engine -> holonics-cuda` dependency edge. Campaign K2 in §4 later develops the complete
   backend-neutral field law, source moments, adjoint contracts, execution-port methods, host
   reference, and method-by-method relation to the resident CUDA return. `holonics-apple`
   implements that port later.
4. **Crate count: `holonics` and `holonics-cuda`, Apple later** (restored September 24). The
   draft stack had kept a `no_std` `holonics-portable` crate, made of the former `body` and
   `soma-abi` plus their NVPTX kernel wire, because the Soma NVPTX kernel compiled it. Only
   `holonic-life`'s superseded native-circulation lineage consumed that kernel, and that lineage
   is retired. Its section arithmetic now lives in `holonics::ratio::ring::section`, and the Soma
   PTX, gate binaries and register/live-event launchers are gone. The HNN keeps its C++ kernels,
   which `holonic-engine/build.rs` compiles.
5. **Minimal features.** Each feature combination compiles its own copy of the crate. On
   September 23 the engine had 39 incremental directories (150 GB). Main `holonics` has no
   feature that changes its dependency graph. R1 re-charts both type-level X11 callers before
   retiring `platform_x11`, the default `desktop-x11` feature and `x11rb`: the arithmetic receiver
   keeps exact headless snapshots and a scripted receiver/wave passage; `desktop_receiver` keeps
   one scripted local-star traversal and its TSV measurement receipt through `MemoryPlatform`.
   The earlier module-token scan missed these type-level consumers.
6. **Reception is one module.** Brandon's reading is that to receive is to measure and compare.
   So `receiver/` owns `ReceiverRole`, the joint `interact`/`receive` return, `Receipt` and
   `Ratio::between`. `ratio/` below it owns the arithmetic of comparison ("one per two"):
   presentation, division with remainder, residue/modulo, partial inversion with its nonunit
   fibre, lift/winding and jets. Rust impl blocks cross modules, so `Ratio<L,R>` is defined in
   `ratio/` and constructed from receipts in `receiver/`. This replaces the separate
   `holon/receiver` and `receipt/` of the Codex draft. Lean mirrors it as `Holonics.Receiver`.
7. **A Holarchy is what `interconnect` returns.**
   `Holon::interconnect(parts, gluing) -> Result<Holarchy, GluingDefect>`. `Holarchy::whole()` is
   the joined Holon. Retain identified constituents, cellular/interface maps, port identifications,
   generator provenance and child-scoped restrictions as the decomposition relation, not an event
   history. Port joins use namespaced references `(constituent, port name, kind)`; both references
   must resolve to external ports with compatible flow, effort and power units, and each port may
   occur in at most one join. A join identifies equal efforts and opposite flows, so shared
   interface power cancels. Complexes are joined only through explicit interface complexes and
   boundary-commuting maps into each constituent; connection transports must agree under the
   declared orientation. Pumps compose only when the gluing supplies child-to-joint clock maps
   whose elapsed-time squares commute and whose schedules agree at the joint ticks. Unjoined
   generators retain their own clocks. A restriction remains attached to its constituent unless
   an explicit common coarse target and commuting square justify a whole-Holarchy restriction.
   `view`, `count` and `refine` follow §3.1. A recursively generated family carries its
   constituent generator. This ties the new object to an existing operation rather than adding a
   parallel constructor.
8. **No empty modules.** `physics/`, `holarchy/` and `receiver/` are created by the commit that
   lands their first implementation with a consumer. The existing `diffusion` receipt and
   interaction owners move into them then. The design tables in §3 are the contract, not a
   scaffold to create ahead of time.
9. **The restructure and new construction are separate.** The restructure moves and retires
   existing code with its current behavior, verified by existing suites. New objects and laws
   (complete interconnect, active receive, Holarchy, physics instances, the information port, the
   HNN host reference) are construction campaigns on the new layout, each with its own issue. The
   Codex draft ordered the physics construction ahead of the HNN and CUDA migration, which would
   have left the tree half-moved behind open research.
10. **The Lean foundation is cut at a few measured edges.** The R0 `Framework` closure
    (188k lines) contains 292 Millennium files (119k lines) and 52 RH files (13k lines). They enter
    through few edges:
    - At R0, `Framework.Core` reached five small Millennium modules **transitively** through
      Foundation imports: `Gluing`, `HolonicDirectedPassage`, `Receiver`, `ReceiverHistory`, and
      `Separation`. Their generic declarations have moved to Foundation owners; the measured
      current Core source closure has no Millennium or RH import path.
    - The former `Objects/Ratio → Millennium/HolonicGaugeCovariance →
      HolonicConnectionVariation` edge pulled 45k lines across 105 files. Ratio-facing gauge and
      connection calculus now has core owners at `Objects/Ratio/GaugeCalculus` and
      `Geometry/ConnectionCalculus`; the research curvature-covariance theorem remains in
      `Millennium/HolonicGaugeCovariance`, which imports its curvature owner directly. This source
      cut removes that direct research import path. It does not by itself remove the overlapping
      source closure: before Physics #105, `Objects/Ratio` reached 47,269 lines through its separate
      `Physics/InformationDifference` import. That research edge has since been cut; the stacked
      Physics/Dynamics source graph now reaches 16 modules / 4,340 lines from `Objects/Ratio` and
      three modules / 538 lines from `Physics/InformationDifference`. Keep the earlier 47,269-line
      figure historical, and measure Lake artifacts separately from the source graph.
    - `Framework.Geometry` also imported `Millennium/HolonicConnectionCurvature`, re-exporting its
      four-force carrier closure. The facade consumes no curvature declaration. It now imports
      `Geometry/ConnectionCalculus` directly; the periodic-box research theorem also imports that
      owner directly because it uses only the generic base chart. Curvature, Bianchi, gauge
      covariance and variation remain in their research owners, whose actual consumers still import
      them. The source closure and exact importers are recorded in `LEAN_CORE_R3_EDGES.md`.
    - At R0, `Holon/MomentStorage` imported `Millennium/HolonicQuadraticMomentCondensation`,
      whose `HolonicGranularBoundaryRadiation` import pulled 48k lines across 111 files. The
      generic quadratic moment and receiver contraction now live in `Holon/QuadraticMoment`;
      `MomentStorage` and `ScrewGeometry` import that owner directly. Distinct research
      condensation theorems remain in the Millennium file. Other Framework imports still reach
      research, so this local cut does not establish a research-free Framework.
    - `Framework.Physics` reaches 345 research files.

    Moving the declarations these edges actually use into `Holonics` owners removes most of the
    research from the foundation. R3 does this before the path move. It measures the remaining
    closure and records it.
    The first five Core ingress cuts have now moved their generic declarations to Foundation:
    a source-import traversal from `Framework.Core` reaches 26 in-package modules and no
    `Millennium` or `RH` module. The full `Framework` facade still has the distinct Ratio and
    MomentStorage research ingress listed above; those cuts remain R3 work.

## 0.11 Status and method, September 24

[established-bounded; measured] The audit of the Codex stack (67 draft PRs, #77–#143) found its
changes correct but almost entirely moves: Rust −2%, Lean +0.5%, 59 files deleted in 159
commits. The census defaulted to *keep*, counting any reference as proof of liveness, even a
reference from other dead code or from a superseded machine. On `restructure/retire` the stack
tips were joined and retirement run by **reachability from declared roots**, with the compiler
as the test.

- **Roots:** the main library, the HNN crate's field/native sessions and stream, the workbench,
  the six current Athena field examples, the CUDA driver, the elementary-object owners the
  operator contract names, and equation extraction.
- **Retired:**
  - `holonic-life`, the native-circulation machine and its Soma lineage (membrane, body,
    `soma-abi`, the NVPTX kernel and its PTX, the register/live-event launchers);
  - `holonics-workspace`, `holonics-portable`, `holon-plate`, `derivation-atlas`;
  - 53 unreachable engine modules;
  - every engine and main-library example and 28 superseded HNN examples;
  - the September 4–5 HNA recurrent-token session API;
  - `archive/`, whose 194 Markdown links are rewritten as permalinks.
- **Result:** Rust went from 1,181,217 to about 537,000 lines, and crates from 16 to 4. The
  workspace all-target check and the host suites pass; GPU results are recorded in the receipts.

**Method from here:** declare the roots, delete everything they cannot reach in large batches,
run one workspace build per batch, and restore only what the build proves is needed. Behaviour
suites (GPU) run once per step and for any change to HNN behaviour. Use one PR per plan step,
not one per module.

**Remaining:**
- R4: remove the HNN's positional/old-length rest decoders and serde defaults for absent legacy
  fields.
- The HNN crate's non-field sessions: native, wave, coupled-wave and mathematical, checked
  against the field.
- Lean: the duplicates and wrappers the audit found, the Physics research ingress, and the M2 move.
- M1: move the resident HNN into `holonics-cuda` and retire the `holonics-hna` name.
- R5 records and D (docs, README).

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
The current R0 source audit already found actual type-level callers or distinct unported laws
for the first eight of those historical “zero-reference” engine modules. The 41/40 figures
are a search queue, never a retirement list; see [THE_REPOSITORY_CENSUS](THE_REPOSITORY_CENSUS.md).

## 2. What is essential: the restructure is organized around these

[definition] Everything kept must be one of these objects, a composition of them, their device
realization, a boundary chart, or a measurement. The owner columns below name **current**
sources; §3 gives the target layout.

### 2.1 The Holon and its facets (the core)

| Object | Law (one line) | Lean owner now | Rust owner now |
|---|---|---|---|
| Holon `H=(K,∂_A;Π;𝒟;𝓔;G;π)` | the law and its ports, not its state; interconnection of Holons is a Holon; passivity proved | `Holon/{Law,Port,Dirac,Complex,Element,Generator,Restriction,Conformance}` | `holonics::{holon,law,port,dirac,complex,element,generator,restriction}` |
| Complex, holon/coholon pairing | `∂²=0`; `d=∂ᵀ`; Stokes; power is the pairing | `Objects/Pairing`, `Holon/Complex` | `holonics::complex` |
| Constitution (element relations) | storage `C`, `K`, resistive `D⪰0`, sources, active relations with power, pumps; modes `Kv=ω²Cv` | `Holon/Element`, `Holon/MomentStorage` | `holonics::element`; normal law `NormalConstitution`; moment storage |
| Generator | initial configuration (key), clock, phase lift; helix = circle + carry; fractal family = words, restrictions, scale square, first arrival | `Geometry/PhaseCarry`, `Holon/Generator`, `Foundation/FractalPacking` | `holonics::generator`; `holonics::geometry::winding` |
| Helical pair contact | slip `J`, `Q=⟨Δ|Δ⟩`, `DQ=2J*Δ`, Farey lock address; contact material `ΣwJ*DJ` | `Transport/HelicalPairInteraction`, `Geometry/PairResonance`, `Millennium/Farey` | `holonic_interaction`, `holonic_chain`, `holonics::geometry::screw` |
| Complex parametron (HNN physical instance) | LC storage↔flow at `ω=1/√(LC)`, pump, half-turn Ising lock; perceptron = locked-sheet face | `Objects/Parametron` | `cuda_refine::complex_parametron` (device); no host owner yet |
| Tube, tower | longitudinal clocked span; transverse restriction with unique/plural/obstructed gluing; `Λ_DN` | `Transport/ContinuingTube`, `Foundation/IwasawaTower` | `holonics::restriction::{tube,tower,fibre,descent}` |
| Relative completeness (globe) | boundary bounds interior; coupled by conserved charges, not determined; persistent motion | `Objects/RelativeCompleteness` (full theorem owed, #62) | none |
| Deposition and retention | the only law changing a constitution; retention = future-sufficient quotient, never a tape | `Objects/{Deposition,Retention}`, `Foundation/Standing`, `Holon/Deposition` | `holonics::deposition`; `holonics::receiver::standing` |
| Ratio and loss | `R=Ĝ_(T←H)`, `ℓ=log R` with winding branch, covector `R⁻¹dR`, jets | `Objects/{Ratio,RatioPhase,RatioBlock}` | `holonics::ratio::exponentiated`; incident receivers |
| Receipt | field of per-region readings, own frame and clock; no global scalar | none | readings in each owner; bits readings in the exposure measurement |
| Keys and navigation | action fits a constitution (lock); learning = locating keys by loop closure (Bombe) | `Transport/{GeneratorTraceFaces,CellHolonomy}` | `relational-geometry::winding::Machine` |
| Reaction (power-neutral, Cayley step) | skew reaction; `(I−½K)y=(I+½K)p+W_c c`, gain 1 | `Holon/{Reaction,Cayley}` | `holonics::reaction`; `normal/direct/reaction_law.rs`; `kernels/enclosure_cayley.cuh` |

Exact algebra underneath: `exact_linear`, `prime_image_algebra`, `inertia`, `rational_polynomial`,
`primality`, `ExactRing`/`ModularWords` (now in `holonics::ratio::ring`).

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
`holonics-cuda`, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`.

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
Holon law, exact geometry and algebra, elementary operations and the backend-neutral HNN law.
The resident HNN realization belongs to the backend (§0.3). A separate `holonics-hnn` package
is not needed: the law sits in main, and each realization sits in its backend.

The target is three maintained libraries on this branch, four when Brandon adds Apple (§0.4):

| Package | Internal ownership | Existing sources to sort at R0 |
|---|---|---|
| `holonics-portable` (§0.4) | A dependency-free `no_std` leaf for exact body/ABI laws compiled by both host and detached Rust CUDA kernel. | Former `body`, shared section arithmetic, and kernel-shared wire schemas live here (`holonics_portable::wire`); host exact rings live in `holonics::ratio::ring`, section refusals in `holonics-cuda::section_layout`. The unused `soma-abi` current, Holon, and presentation schemas were retired after the production wire move left them with test-only consumers. |
| `holonics` | Main library: typed ratio/remainder/inversion and jets; geometric frames, exterior cells, pair and tube/tower charts; the one Holon law with active receiving, composition, restriction and deposition; a proposed receiver-relative `Holarchy`; fluid, wave, spacetime and thermal constitutive instances; equation extraction as a Holon boundary; and the backend-neutral HNN: field law, source moments, adjoint contracts, execution-port trait and host reference, the last built in K2. The complex-parametron chart is an HNN physical chart. No CUDA dependency and no `nvcc`. | `holonic-core`, `relational-geometry`, live `holonic-structure`, the source-neutral parts of `holonic-engine` (extraction included), and the law/declaration parts of `holonics-hna` and live `holonic-life`. |
| `holonics-cuda` | CUDA realization: driver, allocation, transfer completion, section layout and partition, hardware cover, the `.cu` kernels and their `build.rs`, and `hnn/`, the resident HNN field moved as it is (§0.3). It depends on `holonics` and implements the HNN execution port as K2 defines it. It does not redefine the material or loss law. | the former `holonic-mount` owner (now moved), engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`, the resident `native_ecology/**` and `embedding_fiber`, the resident `holonics-hna` `native/**`, and the device files of `holonic_intelligence`. |
| `holonics-apple` (later) | Apple silicon implementation behind the same typed execution port, with its own kernels and placement. Create it only on Brandon's Mac branch after its actual implementation is ready. | No Linux-branch move. |

The dependency direction is `holonics-portable → holonics → holonics-cuda` (and later
`holonics-apple`); arrows mean *may be used by*. The detached Rust CUDA kernel also
depends on `holonics-portable` directly. Applications select a backend and depend on
`holonics` plus that backend. The current workbench remains an application package while R0
checks its deployment boundary; the 2–4 ceiling above counts maintained reusable libraries,
not a CLI's separate Cargo binary target. The main library's default build must work without
a CUDA SDK, driver or linker symbol. `hnn` is a module of it, not a feature (§0.5). A CUDA
caller passes the backend's executor through the HNN execution port rather than making
`holonics` import the CUDA package. Until K2 defines that port method by method, applications
call the resident HNN in `holonics-cuda::hnn` directly. There is no `holonics::hna` module:
callers move to the new paths in the moving commit (§0.2).

The internal source tree follows an **operator dependency**, not a catalogue of independent
substances. The conceptual order is ratio/remainder and partial inversion → geometric
transport/phase/carry → the Holon law → its pair and tube operations → compound Holarchies and
HNN realizations. This is not a literal import order: pair contact requires participating
Holons, while the geometric `ScrewPair` chart can be constructed before their material is
known. A parametron is a pumped LC Holon instance used by HNN, not a prerequisite for defining
all Holons.

```text
crates/holonics/src/
  lib.rs       Holon and deliberate qualified public operations
  ratio/       one per two: presentation, division/remainder, residue/modulo, partial inverse
               with its nonunit fibre, lift/winding, jet; word rings if words folds in (§0.4)
  geometry/    complex/exterior/metric, frame/connection, clock, carry/phase, pair and tube/tower charts
  holon/       law, state, ports/Dirac, elements, generators, restrictions, interconnect,
               contact, continue, deposition/retention
  receiver/    ReceiverRole, interact/receive -> InteractionReturn, Receipt, Ratio::between
  holarchy/    Holarchy returned by interconnect: whole, constituents, typed gluing, view/count/refine
  physics/     fluid, wave, thermal, spacetime, information (each created with its first implementation)
  extraction/  foreign equations as Holon element/generator relations
  hnn/         field law, source moments, adjoint contracts, execution port, host reference (K2)

crates/holonics-cuda/src/
  driver/      context, module, stream, allocation, transfer completion (from former holonic-mount)
  section/     resident sections, SLOT_WORDS, section partition, hardware cover
  hnn/         the resident HNN field and session, moved as it is
  extraction/  device parts of equation extraction, if kept
kernels/       .cu/.cuh sources and build.rs
```

There is **no public `exact` object/module**. Integer/rational/algebraic/matrix carriers live
privately beside the operators that use them; exact source descriptions and certified
remainders are the default mathematical contract. The proposed `holonics-portable` leaf is a `no_std` shared implementation carrier for the
body/ABI/word laws the detached kernel and host both compile. It is not a second mathematical
foundation. A dyadic `0.5` and `1/2` can have the same exact numerical face; the ratio object
also retains the comparands, units, source, possible winding and chosen presentation when a
future operation needs them.

| Planned operation | Law and return | Current foothold / missing join |
|---|---|---|
| `Ratio::present`, `compare`, `compose`, `invert` | Carry the typed numerator/denominator pair; compare two received faces only after their sources, frames, clocks and units are joined. Cross-multiply where valid. Inversion has an explicit nonunit/zero fibre, not an invented reciprocal. | Lean `Objects/{Ratio,RatioBlock}`; Rust `RatioFace` and scoped `RatioFamily`. A general typed owner is owed. |
| `div_rem`, `residue`, `lift`, `jet` | `a=bq+r` with divisor, quotient and remainder retained; modulo is the selected residue face, winding/carry the lift. Logarithmic and higher jets retain domain and branch. | Lean `Geometry/PhaseCarry`, `Millennium/Farey`, `Objects/Ratio`; Rust `winding::{Odometer,LockAddress}`. These laws are present but dispersed. |
| `Generator::evaluate_with_remainder` | A series, recurrence or analytic source returns its exact/certified value **and its own tail or truncation defect**. This is not Euclidean remainder, although both refuse to erase what the finite reading omits. | η atlas and `RH/LogDerivativeRemainder` have source-specific realizations; a shared source/receiver port is owed where HNN or mathematical navigation consumes it. |
| `Geometry::transport`, `screw_pair`, `tube`, `restrict` | Carry frame, connection, incidence, phase and clock. A pair chart supplies two motions and their relative jet; a tube chart supplies longitudinal transfer and transverse restriction with an explicit gluing defect. | Rust `relational_geometry::screw`, `winding`, core `restriction::{tube,tower}`; Lean `PhaseCarry`, `PairResonance`, `ContinuingTube`, `ContinuingTower`. |
| `Holon::interconnect`, `contact`, `continue`, `receive` | Interconnect at ports with internal-power cancellation; bind pair geometry to contact material; carry one Holon through a tube. `receive` joins a source and receiving Holon and returns both changed participants, a typed face and its local receipt; receiver state/material/frame/clock are operands. | `Holon::interconnect` and `PortHolon::interconnect` exist. Full Rust joining of pumps, named ports, complexes and restrictions is still refused or omitted; Lean `Holon/{Dirac,Law}` proves scoped port joins. `Transport/ChangingReceiver` owns the moving-receiver term. |
| `Holon::restrict`, `depose`, `pullback` | Restrict across grain with a commuting square or typed defect; only arrived covectors change the constitution; the adjoint returns through the full producing operands. | Core restriction/deposition and HNN adjoints exist at distinct scopes; their unified consuming call is owed. |
| `Holon::interconnect -> Holarchy`; `Holarchy::whole`, `view`, `count`, `refine` | `interconnect` returns the Holarchy, which retains its constituents and gluing (§0.7); `whole()` is the joined Holon. `view(receiver,grain,clock)` returns situated constituent faces, interface flux and unresolved classes. `count` requires a finite discrete receiver partition; otherwise return a typed unresolved reading. | New proposed owner. Existing Holon composition, receiver atlas, tower and future-sufficient quotient provide its ingredients; no current Rust `Holarchy` type has this contract. |
| `Holon::fluid_flux`, `stress_energy`, `observer_current`, `entropy_balance`; wave `propagate`, `interfere` | A physical specialization carries mass/momentum/energy, stress traction, heat/entropy currents and the actual constitutive and metric/clock law. A spacetime receiver contracts the whole stress-energy tensor; waves join coherent amplitudes before an intensity face is read. | Fluid guide, `EinsteinFluidDynamics`, `ObserverBoundaryCurrent`, `PortEnergyHeat`, finite `FluidReceiverClosure`, `NavierStokesLambCurrentCell`, phase/scattering owners. Pair slip and pumps are only declared specializations; a general native fluid/wave/Einstein realization remains owed. |

The root exports the central `Holon` type and qualified operations, not a flat engine-wide
glob. Callers move in the same commit as the code they call (§0.2). The ratio and geometry operations are reusable by
Holon methods; they do not each create a rival Holon. HNN assembles those methods into its
continuing field and treats the complex parametron as a concrete storage/pump/lock chart.
Application codecs remain receiver boundaries. Exact module names and method signatures
follow the surviving consuming calls; this table states their required behavior.

A **Holarchy** is a Holon with a declared, continuing decomposition relation, not a `Vec<Holon>`
or an absolute atom count. Its constituent family and incidence may be implicit or recursively
generated. A constructor requires a plural participation witness at some declared context and
returns a gluing obstruction instead of asserting that every family closes. One receiver can
read the compound as one face; another can separate continents, islands or molecules at its
own grain. Quantities such as number, mass or category are methods of the receiving relation,
with units, partition/overlap conditions and clock; they are not immutable fields of the
Holarchy. A finite count requires a receiver-supplied finite partition witness establishing
coverage, disjointness and distinguishability at the requested grain; otherwise the count remains
unresolved. Refinement carries a fine-to-coarse port map and a commuting scale square. A nonzero
square defect or a receiver reading that separates a merged fibre remains an explicit refinement
result. The whole itself may receive, act, and compose with other Holarchies.

**Reception is a Holon interaction; ratio is its comparative reading.** The receiving Holon
has its own material, current, frame, clock and possible next state. At an admitted contact,
`I_C(|H_S⟩,|H_R⟩)=(|H'_S⟩,|H'_R⟩,f_R)`; `f_R` is the face, not the receiver object.
A `Receipt` carries the source and receiver identities, region/interface, transported frame,
clock/tick, typed face and unresolved fibre. `Ratio::between` compares two such faces after
their declared common transport, retaining both operands and any winding. A moving receiver
contributes its own variation (`D_Rρ·X_R` in addition to `D_Sρ·X_S` and explicit clock change).
The `receiver/` module (§0.6) holds these on one API surface without reducing a receiver to a
scalar ratio.

The notation must be derived from these same typed objects: `|H⟩_F` presents a Holon in a
frame; `⟨r|` is a participating receiving port; `⟨r|H⟩` is the returned face; `Ĝ_(F'←F)`
transports the complete source/receiver axes; contraction joins an upper ket port to a lower
bra port through the declared pairing. A diagram line is a port/current, a vertex its
constitutive interaction, and a loop a declared circuit with holonomy/trace. Rendering the
notation or diagram reads the operator graph; a glyph or projected crossing never creates
an interaction that the incidence and constitution do not contain.

The HNN execution port is defined at its surviving consuming call, including the forward
field, complete geometry/feature pullback, material return, source order, receiving phase and
receipt. The host/reference implementation and CUDA implementation must return the same typed
relation at their stated precision. The apparatus package now has its target owner. The resident
HNN cut remains: `holonic-engine` imports `holonics-cuda` and runs `nvcc`; resident field owners
remain in engine/HNA/life; exact rings belong to `holonics::ratio::ring`; and the HNN field has no
host reference (§0.3). M1 first establishes the backend-neutral section/receipt seam in
`holonics::hnn`, then moves the resident dependency closure into `holonics-cuda` with current
behavior while removing the engine-to-CUDA edge. K2 later develops the complete execution port and
host reference one method at a time against the CUDA return. A module with a distinct
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
The public root presents ratio/remainder, geometry, the Holon law and its pair/tube/contact,
deposition/retention and receiving operations, followed by the proposed Holarchy and HNN.
The complex parametron is an HNN physical instance of those operations. HNN theorems are a
dependent specialization **inside** `Holonics`; `HolonicsResearch` contains
independent mathematical instances and cannot become an alternate foundation.

Refine that root by **operator**, coupled to the Rust calls above:

| Lean target owner | Current checked sources and next obligation |
|---|---|
| `Holonics.Ratio` | `Objects/{Ratio,RatioPhase,RatioBlock}` already prove undivided presentations, nonunit/zero lift fibres, logarithmic derivative, matrix/projective ratio and jets. Bring the general quotient/remainder/carry and partial-inversion interface from `Geometry/PhaseCarry` and the Euclidean/Farey laws into one import surface; keep source-specific analytic remainders with their source. |
| `Holonics.Geometry` | Oriented complex, frame/connection, phase lift, screw pair, tube/tower charts. Reuse `Geometry/{PhaseCarry,PairResonance}`, `Transport/{HelicalPairInteraction,ContinuingTube}`, `Foundation/ContinuingTower` and Hodge/exterior owners. Keep geometric kinematics distinct from a Holon's material contact law. |
| `Holonics.Holon` | Join the occurrence/interface/receiver operations in `Foundation/Holon` with the port/material/interconnection law in `Holon/{Port,Dirac,Element,Generator,Restriction,Law}`. Prove the full joined complex, pumps, clocks and restrictions under stated hypotheses; the current port theorem and native method have narrower scope. |
| `Holonics.Receiver` (§0.6) | A receiver is a participating Holon, with its own state and clock. Reuse `Foundation/Receiver`, `Transport/ChangingReceiver`, `Objects/Pairing` and `Foundation/Holon.mapReceiver`; prove the joint received return and moving-receiver variation before deriving typed ratio/receipt readings. The receipt retains frame, interface and unresolved fibre. |
| `Holonics.Holarchy` (proposed) | Define a Holon with a witnessed plural decomposition and receiver/grain-indexed views. Prove interconnection closure where supplied, internal-port cancellation, compatible refinement and conditional count laws; exhibit two receivers with different counts of the same continuing whole. Retain overlap/gluing defects and preimage fibres. |
| `Holonics.Physics` (instances) | Fluid, wave, spacetime and thermal laws specialize Holon incidence, transport and element relations. Keep mass/momentum/energy and stress traction, pressure constraint/Hodge projection, complex-bilinear and conducting-fluid signs, heat/entropy flux and relaxation, phase superposition, propagation and boundary energy. Join `EinsteinFluidDynamics` and `ObserverBoundaryCurrent` under their stated field/Bianchi/metric hypotheses; preserve the abstract-versus-physical realization boundary. Use the finite checked owners and name continuum/discretization obligations. |
| `Holonics.HNN` | Formal specializations of the same Holon operators: coupled field, source moments, complete variation, deposition return and complex-parametron storage/pump/lock chart. It imports the object owners; the physical parametron is not a foundation import. |

`Framework/Physics.lean` is currently an import-only subject facade, not a declaration owner.
Curate its target `Holonics.Physics` by the finite constitutive and receiver laws actually owned by
its imports; keep source-specific Einstein/cosmology/Maxwell instances in `HolonicsResearch` and
place HNN specializations under `Holonics.HNN`. The source map and two small Physics import cuts
are recorded in [`LEAN_CORE_R3_EDGES.md`](census/LEAN_CORE_R3_EDGES.md#physics-facade-curation-audit).
Those cuts remove direct edges but do not by themselves make the full Physics closure research-free;
each remaining generic/source-specific mixed owner needs its declaration-level boundary audited.
The full operator-root map, measured source closures, and 25 Lean modules absent from the legacy
umbrella are recorded in the [M2 Lean root curation audit](census/M2_LEAN_ROOT_CURATION.md).

M2 moves paths and Lake roots only after that audit's generic/research declaration cuts are
complete. The current `Framework` source closure is not accepted as `Holonics`; its facades still
reach mixed Millennium owners. `HolonicsResearch` imports `Holonics` one-way, and the old broad
umbrella's extra source modules are retained or classified individually before it is replaced.

The September 23 Millennium work supplies concrete tests of this placement. `Computation/CertifiedWindingRoute`
has receiver-count additivity over zero-free shared cuts and a compatible shrinking route;
`Computation/IntersectionNavigation` returns an affine solution fibre or unreachable
obstruction; `RH/PrimePhasePartition` proves a finite common-denominator sign law on one
source-weighted phase population. A general checked operation belongs in the public Lean
owner when its hypotheses are sound; it then gives Rust a typed port and a concrete first
consumer, whether an HNN call or a mathematical application. The η/ξ source, off-line Weil sign and global
RH conclusion remain research instances or open claims. `Foundation/HodgeReceiver` shows a
harmonic class count can be stable while a preferred representative changes with its metric;
`Foundation/IwasawaTower` shows a quotient level's cardinality and retained kernel depend on
the selected restriction. A Holarchy's count therefore has receiver/grain hypotheses and may
still possess conditional invariants.
The September 22 exterior-current construction adds two direct controls:
`FractalPacking.sibling_total_width` is a receiver law induced by addressed children, while
`Millennium/NavierStokesLambCurrentCell.smoothSolutionOn_twoCell_sharedFace_gluing` cancels
the same physical flux on a joined face under its trace hypotheses. Holarchy composition
must preserve that shared-face law; its area, volume or number is a reading of the generated
and restricted geometry, never a fixed field in the collection struct.

Generate the import closures before classifying files. §0.10 lists the measured edges through
which research enters the present foundation. Cut those first. Keep `Holon/`, `Objects/` and the
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
- `research/records/`: apply §0.1. A record stays if a guide, plan, issue or owner cites it, or
  if it is the only statement of a result. Otherwise it is folded into its guide as one line with a
  revision link, or into `RETRACTIONS` if the attempt failed, and deleted. Brandon's direct
  messages stay where a kept record or guide cites them. `research/papers/rendered` and
  `experiments/` need an artifact/source census; generated copies may be regenerated from kept
  sources only when that regeneration has been checked.
- `archive/`: delete from the tree only after its live citations and executable source-data
  consumers move or receive immutable revision replacements. R0 found equation-atlas JSON
  fixtures consumed by Rust examples and a tooling script used as source data; Git history
  alone cannot satisfy those current calls. CLAUDE.md/AGENTS.md cite revisions after the move.
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

Before retiring an old package, verify a `holonics` build without CUDA, CUDA owner tests
(including the resident HNN suites) on the available card, an all-target
public/workbench check, both Lean library targets and the changed source-to-Lean citation/link
scan. Inspect a saved
session through the new public path when one is named as retained. Record the specific commands
and results in the census; a build of an intermediate move is not the completed boundary check.

### 3.5 Physical and receiving battle tests

The [fluid construction](../HOLONIC_FLUID_CONSTRUCTION.md) is the physics contract here. A pair
slip `J` measures relative kinematics at an admitted interface, and a pump supplies active
work; neither alone gives Euler advection, a pressure constraint, viscous stress, heat or a
continuum limit. A local pair-contact picture can realize two-sided face exchange, but a
universal reduction of every fluid interaction to toroidal/helical pairs is an open
reconstruction claim. It would need a decoder preserving bulk mass/momentum/energy balances,
stress/pressure, circulation, phase, unresolved modes and every admitted receiving face.

| Test | Required returned operation | Current scope / gap |
|---|---|---|
| Reflect a square and a cube, then join adjacent cells | Oriented boundaries and `∂²=0`; transported normals, signed area/volume from orientation plus a declared metric; Stokes pairing; common edge/face flux cancels once with opposite hands. | `CellComplex`, `Geometry/ExteriorBoundary`, material-polygon and two-cell Lamb-current theorems give pieces. The generic embedding-to-exterior-measure and full Holon join remain to be connected. |
| Interfere and propagate two waves | Combine complex amplitudes with connection/phase before the receiver reads intensity; `1+(-1)=0` must not become `|1|²+|-1|²=2`. Advance under a supplied wave operator, material, boundary condition and clock; return energy/flux and propagation defect. | Phase-carrier and finite scattering/heat owners are bounded examples. HNN wave sections do not by themselves establish a physical continuum wave solver. |
| Split a control volume for Euler/NS | Per oriented face return mass flux `ρu·n`, momentum transport `ρu(u·n)` and traction `σn`; cell storage plus outward flux equals source. Supply `σ=-pI+2μ Def u+λ(div u)I`, incompressibility/pressure solve where admitted, and viscous work to internal heat. Rejoin faces and compare the full-volume return. | `NavierStokesLambCurrentCell` checks scoped cell balance/gluing; `FluidReceiverClosure` retains hidden feedback. A native source-conforming fluid solver and its continuum/discretization scope remain open. |
| Complex fluid versus a real field's Fourier chart | For `U=a+ib`, retain `B(a,a)-B(b,b)` and both cross terms; distinguish that physical complex-bilinear law from conjugate Fourier coefficients of one real velocity and from MHD's different induction sign. | `Physics/ConductiveFluidReflection` and the fluid guide own the finite/sign distinction. An imaginary component is not a magnetic field by notation alone. |
| Move the receiver and change grain | Return both participants and local receipts; a moving reading includes the receiver-rate term. A Holarchy's count can change with a certified receiver/grain partition while shared physical flux and conditional invariants continue correctly. Render bra/ket, transport arrows and loop diagrams from the same typed operator graph. | `Transport/ChangingReceiver` and receiver-holarchy laws are starting owners. The joint native receiving return and Holarchy operator are owed. |

Passing finite topology and face tests licenses those stated operations, not a general fluid or
wave simulation. A simulation return additionally names its source equation, constitutive
law, boundary/initial conditions, time advance, numerical/exact remainder and measured
receiver. Preserve unresolved stress or hidden modes rather than replacing them with a
pairwise metaphor.

### 3.6 Spacetime, heat and plural-clock information return

The Einstein/fluid lift is an owner, not an analogy to append after the Newtonian tests.
`Millennium/NavierStokesCurvedTransport.EinsteinFluidDynamics` supplies `g`, `G`, a constituted
stress-energy `T`, covariant divergence, `G+Λg=κT`, contracted Bianchi and metric
compatibility; for `κ≠0` it proves `∇·T=0`, then every declared receiver reads that return.
`Physics/ObserverBoundaryCurrent` reads `j_U^μ=−T^{μν}U_ν` with divergence
`−(∇·T)·U−T:∇U`; the observer's acceleration/deformation is therefore a physical term in
the received energy current. `Physics/ReceiverStressEnergy` has finite observer/boosted
stress readings. The metric, curvature and fluid-plus-thermal constitution must be constructed
for a nontrivial native realization; the existing flat vacuum witness does not do that.
`HolonicCurvedArcEinstein.nonzeroCoupling_is_not_universalArcRatio` also rules out promoting
the depth-two arc/differential receiver ratio to a universal Einstein coupling.

A complete thermal port carries internal energy, heat flux `q`, entropy current `s`,
temperature/inverse-temperature and material relaxation beside mechanical stress. It returns
the first-law storage/boundary/work balance and a separately proved entropy-production law
`∂_τ s + div j_s = σ_s`, `σ_s≥0` under its constitutive hypotheses. Viscous/contact work
can enter internal heat without creating or destroying total stress-energy. The finite
`Physics/PortEnergyHeat` balance, exact Rust `DiffusionReceipt::energy_balance`,
`Physics/TwoCellEntropyTransport` and oriented current in
`Millennium/HolonicEntropyActionInduction` supply different pieces. The two-cell proof uses
dimensionless masses and a stipulated flux; it does not yet identify physical heat or force.
The heat cross-current in `Millennium/HolonicEntropyHeatCurrent` is an exterior current with
a sourced heat equation, not automatically Gibbs entropy. A relativistic diffusion instance
also states its relaxation/causality law rather than treating the parabolic limit as a
finite-speed signal.

Keep distinct addressed clock lines: source/generator phase, receiving proper time,
fluid/world-tube time, thermal relaxation and observation ticks. Their rate ratios require
unit and chart maps; a joint multi-parameter evolution needs compatible transport or a
retained commutator/holonomy defect. The four-axis exterior current in
`HolonicEntropyActionInduction` is a checked alternating two-current, not a proof of four
physical timelike dimensions. The time/entropy chain crossing remains open in the tube
contract. For a moving received probability population and reference, the cross-entropy
rate includes **both** `ṗ` and `q̇` and the moving aperture's normalization and boundary
flux: for `C(p,q)=−Σ p_i log q_i`, `dC/dλ=−Σ ṗ_i log q_i−Σ p_i q̇_i/q_i`
along a declared common parameter `λ`. Each dot includes its source/receiver clock-rate map;
moving support needs a one-sided/measure transport. Its local clock and support stratum belong
to the receipt.

Cross-entropy can have a **literal physical effect** when the compared population is an
actual physical ensemble and its returned covector enters a declared material/port law.
`Physics/InformationDifference` proves that for a canonical Gibbs reference on the same
energy state space, `F(p)−F(q)=k_B T·KL(p||q)` after the thermal unit is supplied; it also
proves equal scalar cross-entropy can conceal different later physical currents.
`Foundation/InformationReceiver.PhysicalCrossEntropyOccurrence` retains the addressed
crossing/current before its scalar projection. The implementation contract is to pull the
full ratio covector back to a constituted effort, account for its work/heat in stress-energy
and entropy production, and show the receiver's changed state. A bare cross-entropy number,
or bits multiplied by a temperature without that source/constitutive map, is only a face.

Three extra acceptance cases follow: (1) a moving/boosted observer reads the same transported
stress-energy and its deformation term; (2) two thermal cells exchange heat with total-energy
balance and source-qualified nonnegative entropy production; (3) two independent clock
parametrizations give the same transported cross-entropy/material return when the clock square
commutes, or an explicit defect when it does not. These checks do not assert that the present
Lean interfaces already solve coupled Einstein-fluid evolution.

### 3.7 Class and method cut for the main library

This is the proposed **type boundary** for consolidation, not a claim that these types already
exist at these paths. Keep a Holon law apart from a point on it. A receiver is a role played by
another Holon at a port; a receipt is the face returned by their actual interaction. The
source, receiver and clock belong to the method arguments/return, not to a global scalar.

```rust
// Shape of the API; concrete generic parameters and ownership follow the consuming call.
Holon { complex, ports, dirac, elements, pump_schedule, generators, restrictions }
HolonState { configuration, clock_states }           // no event tape
ReceiverRole { holon, state, port, frame, clock, aperture }
Holarchy { whole, constituents, incidence, typed_gluing, joint_clock_maps,
           generators, restrictions }
Receipt { source, receiver, locus, frame, clock, grain, face, unresolved }
Ratio<Left,Right> { left, right, comparison_transport, log_branch }
InteractionReturn { source_next, receiver_next, face, receipt,
                    boundary_currents, power_balance, unresolved }
```

`Holon::interconnect` takes identified constituents and an explicit gluing specification. A
`PortRef` resolves `(constituent id, local port name, kind)`; a `PortJoin` names its two endpoint
references and orientation. Endpoints must be external ports with compatible flow, effort and
power units, and may be joined only once. Free external ports retain constituent-qualified names
unless an explicit output alias is supplied. At a joined interface the bond convention is
`(f,e)` on one side and `(-f,e)` on the other, so the two port powers cancel. Internal storage,
resistive and active ports are not silently treated as external joins.

When either constituent carries a cell complex, the gluing specification supplies an interface
complex and cellular maps into both complexes. Each map must commute with boundary operators; the
induced pushout must satisfy `∂²=0`. Connection-valued incidence is joined only when edge
transports agree under the declared orientation (reversing an edge inverts its transport). Missing
maps, incompatible boundary/connection data or an invalid pushout return a typed `GluingDefect`;
matching dimensions alone do not establish a shared complex. If neither side has a complex, a
disjoint sum is available. If only one side has one, the operation must state its interface or
refuse rather than drop the complex.

A pump-bearing join supplies a joint clock and a child-to-joint clock passage map for each pumped
constituent. The maps preserve declared elapsed time and commute on the clock square; pump schedule
periods and phases must yield a well-defined storage form at every joint tick. Otherwise return
the exact clock or schedule defect. Independent generator clocks remain distinct unless a joint
passage is explicitly declared. Retain generators with constituent provenance. Retain each
restriction with its constituent scope; create a whole-to-coarse restriction only for a declared
common target whose diagrams commute. A failed diagram returns its matrix defect.

`Holarchy` retains the gluing maps, incidence, generator provenance and child-scoped restrictions,
not a history of events. `view(receiver, grain, clock)` returns situated region faces, interface
flux and unresolved fibres. `count` needs a finite partition witness for that receiver and grain,
including coverage, disjointness and distinguishability; absent such a witness it returns an
unresolved reading rather than a constituent-vector length. `refine` carries a fine-to-coarse
restriction and checks `π A_fine = A_coarse π`; otherwise it returns the square defect and any
receiver reading that separates a merged fibre. A typed gluing defect identifies at least the
unresolved constituent/port, unit, cellular boundary/connection, clock/schedule or restriction
square that prevented construction.

The current `holonic_core::Holon::interconnect` joins only the scoped port body/active law/generators;
it refuses pumps and omits the joined complex, named ports and restrictions. The existing
`HolonLaw::advance`/`ReferenceHolon` already return a state, bond and exact energy balance;
retain them as the host reference. The existing `HolonLaw::receive` is a passive linear
coholon reading. Add a joint `receive`/`interact`
operation that advances both participants at one declared contact and returns their states,
face, power and unresolved fibre; keep the passive reader as its zero-storage specialization.
`Ratio::between` consumes compatible receipts after transporting frames/clocks and never
replaces either participating Holon. `Receipt` is indexed by source, receiver, locus, frame,
clock and grain. `Holarchy::view(receiver, grain, clock)` derives a partition and its count
only when the receiver certifies one.

| Main-library instance (one Holon law) | State/material fields and methods | Current owner to migrate; Lean counterpart |
|---|---|---|
| `physics::fluid` | `FluidState`: extensive mass, momentum, total/internal energy and optional internal modes on oriented cells. `FluidMaterial`: equation of state, pressure/incompressibility constraint, stress, heat/entropy transport. `face_flux` returns mass/momentum/energy currents plus traction on one oriented face; `advance` joins those face returns with sources, pressure solve, viscous-to-heat return and a residual. Pair slip is an optional interface contact, not the bulk law. | `holonic-engine::diffusion`, contact/field material where applicable; Lean `NavierStokesLambCurrentCell`, `FluidReceiverClosure`, `PortEnergyHeat`, fluid guide. A general native fluid solver is owed. |
| `physics::wave` | `WaveState` carries complex amplitude/phase on a declared field section; `WaveMaterial` supplies propagation/dispersion, storage, damping/source and boundary relation. `propagate` returns transported section, energy/port flux and defect; `interfere` composes coherent sections before an amplitude/intensity receiver reads them. | Lean `PhaseCarrier`, `ScatteringWaveHeat` and wave/Maxwell owners; native coupled-wave sections are computational charts, not a general physical wave solver. |
| `physics::spacetime` | `SpacetimeRealization`: metric, connection/curvature, Einstein tensor, coupling/Λ and a **source map** from a constituted fluid/thermal state to `T`. `einstein_residual` and `conservation_return` check the coupled relation; `observer_current(receiver_worldline)` contracts the full `T` in that receiver's tetrad and returns flux plus deformation work. This adapter never inserts an arbitrary arc ratio as κ. | Lean `NavierStokesCurvedTransport.EinsteinFluidDynamics`, `HolonicCurvedArcEinstein`, `ObserverBoundaryCurrent`, `ReceiverStressEnergy`; no native coupled Einstein solver yet. |
| `physics::thermal` | `ThermalState`: internal energy, temperature/inverse-temperature, heat flux, entropy density/current and relaxation state with units. `exchange` returns boundary heat, stored-energy change and constitutive work; `entropy_production` returns a sign-certified local current under the stated material law; `diffuse` returns a timestep and exact/certified discretization defect. | Rust `DiffusionReceipt::energy_balance`; Lean `PortEnergyHeat`, `TwoCellEntropyTransport`, `HolonicEntropyActionInduction`. The latter two do not by themselves identify physical heat. |
| `physics::information` | `InformationCoupling` binds an actual ensemble, energy levels/Gibbs reference, temperature and a reached material port to the **full** ratio covector. `apply` returns effort, work, altered material/receiver state and energy/entropy receipts. It may use the Gibbs free-energy/KL identity; raw cross-entropy or a code-length face cannot be passed as a force. | Lean `InformationDifference.thermal_crossEntropy_identity`, `freeEnergy_difference_eq_thermalScale_mul_kl`, `InformationReceiver.PhysicalCrossEntropyOccurrence`; native HNN `incident_receiver/phase::compare` and measurement reader supply the comparison, not yet this physical port. |
| `geometry::clock` / `holon::generator` | `ClockAxis`/`ClockTransport` retain address, unit, phase+winding, rate map and the source/receiver/thermal axes. `transport_rate` composes declared maps; `join_axes` checks a commuting square or returns its defect. No extra physical timelike dimension is inferred from a parameter axis. | Rust core `generator::Clock` and interaction `Clock`; Lean `PhaseCarry`, `SituatedInformationRate`, `HolonicCausalFluxTime`, four-axis entropy-current owners. The time/entropy chain crossing remains open. |

These are physical **specializations of `Holon`**, not optional fields added to every Holon or
new primitive ontologies. `FluidState` and `SpacetimeRealization` remain distinct: a stress
section enters Einstein's equation only through an explicit source map with units and observer
transport. `InformationCoupling` produces physical effect only through its material port; the
same ratio may be read by an HNN loss receiver without acting as heat or gravity. The
thermodynamic and spacetime returns share the original interface/current and their complete
first-law balance.

The Lean package mirrors the method contracts, not every Rust struct: `Holonics.Holon` owns
law/state and complete interconnection; `Holonics.Receiver` owns the active receiver, receipt
and comparative reading over `Holonics.Ratio`; `Holonics.Holarchy` owns receiver/grain decomposition; and
`Holonics.Physics.{Fluid,Wave,Spacetime,Thermal,Information}` imports those owners. Move a generic
checked operator from `Millennium/` or `Physics/` when its hypotheses and target interface
are retained; keep source-specific NS, ξ and gravity claims in `HolonicsResearch`. Pair each
native `face_flux`, `observer_current`, `entropy_production` and `apply` return with its Lean
statement or a named #62 obligation. A diagram/notation renderer reads this typed operator
graph: ket = presented Holon, bra = active receiving role, bracket = receipt face, arrow =
frame/clock transport, loop = declared circuit. It never stores a second topology.

These classes are built by the construction campaigns K1–K4 in §4, after the restructure
lands. They are not steps of the move (§0.9). Each carries its actual caller and
source-qualified verification; no package rename substitutes for it.

## 4. Order of work

**Done (landed on main, September 24):**
- R0 census.
- R1–R2 retirement by reachability (§0.11).
- R3's Core, Ratio and MomentStorage edges.
- C phases 11, 12a and 12b.
- The first M1 moves: the Holon core, geometry, ratio, receiver, standing and release now sit in
  `holonics`, and the driver sits in `holonics-cuda`.

**Next, in order.** Each step is one PR and one issue. Retirement uses reachability from the
roots in §0.11.

1. **T: tests and gates (#144).** The suite was written beside each campaign for a
   1.3M-line monolith. It is 142k lines: 3,208 tests, 582 of them GPU-gated. Re-running it cost
   hours during the restructure. Audit it by owner and delete tests that:
   - assert old save/wire versions or decoding;
   - assert prose, paths, citations or repository contents;
   - encode retired semantics (tapes, frozen cuts, token sessions, circulation, protein fixtures);
   - are campaign measurements dressed as tests (long loops, printed summaries, fixture numbers
     without a stated law);
   - duplicate another test of the same law.

   Keep fast tests of a named law of the operation, plus one host/device parity check per
   kernel family. Retire the gates that serve only the old layout: source-scanning citation
   tests, per-check receipt logging and `mount-*` gate binaries.
2. **R4: compatibility debt.** Remove the positional/old-length rest decoders and the serde
   defaults for absent legacy fields (§0.2).
3. **M1: merge and prune (the Rust cut).** Measured on main at `307baad2`:
   - 8 engine modules touch CUDA directly: `native_ecology`, `front_passage`, `resident_section`,
     `cuda_refine`, `embedding_fiber`, `streamed_standing`, `cuda_aperture`, `cuda_relation`;
     together 149k lines.
   - 97 more modules (348k lines in all) reach one of those.
   - Only 31 modules (37k lines) are source-neutral.

   Untangling a backend-neutral seam module by module (§0.3's draft) would take weeks. Instead:
   1. Move the 31 source-neutral modules into `holonics`, at their operator homes.
   2. Merge the rest of `holonic-engine`, and `holonics-hna`, into `holonics-cuda`, with no
      behaviour change: engine modules become crate modules, and the HNN crate becomes
      `holonics_cuda::hnn`. This removes the engine→CUDA cycle and the `holonics-hna` name at
      once. The workbench depends on `holonics` and `holonics-cuda`.
   3. Prune at item level with the compiler. Make every module `pub(crate)` except the HNN
      machine's own session interface (the field session and the generator session) and the CUDA
      driver. Delete what `dead_code` reports, and repeat until it reports nothing. Tests of
      deleted items go with them.
   4. Afterwards, K2 extracts the backend-neutral HNN law into `holonics::hnn`, method by method.

   The result is two libraries: `holonics` and `holonics-cuda`.

   **No applications survive the cut** (Brandon, September 24). The workbench CLI, the JSONL
   stream protocol, the exposure source and the Athena example applications were prototypes, never
   functional or useful enough to keep. They retire with this step. What they taught is kept in
   the
   [lessons record](../../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md).
   Any workbench or Athena application is rebuilt on the restructured library.
4. **C: phase 14** (the cultivated body) on the moved tree.
5. **R3 remainder and M2 (Lean).** Remove the duplicate and wrapper theorems the audit found, cut
   the Physics research ingress, then move to `lean/` as `Holonics` + `HolonicsResearch`.
6. **R5: records and documents**, by citation from the kept guides and owners.
7. **D: docs and README**, per the closing acceptance below.

**Construction** (K1–K5, #72–#76) and the machine campaigns (#17, #16, #18, #61) run on the new
layout after M1.

**Closing acceptance (D).** Update everything below to the verified paths:
- **Operator contracts:** [ELEMENTARY_OBJECTS](../ELEMENTARY_OBJECTS.md), [HOLON](../HOLON.md),
  [THE_MACHINE](../THE_MACHINE.md), [HNN_FORMULA](../HNN_FORMULA.md),
  [RECEIVER_HOLARCHY](../RECEIVER_HOLARCHY.md), [FORMAL_FRAMEWORK](../FORMAL_FRAMEWORK.md),
  [RUST_FRAMEWORK](../RUST_FRAMEWORK.md), [ARCHITECTURE_MAP](../ARCHITECTURE_MAP.md), and the
  CLAUDE.md/AGENTS.md owner tables.
- **Guides naming retired owners:** update or delete them.
- **Last:** rewrite `README.md` in full to describe the repository as it now stands.

Build hygiene starts now: use one shared scratch target directory and
`CARGO_PROFILE_DEV_DEBUG=line-tables-only`; inspect each target/cache's owner before reclaiming
generated output. Remove a WIP branch's target only after its source is integrated or otherwise
preserved. The old engine graph's incremental output can be cleared after the split; do not use
`git clean`, blanket worktree deletion or a broad restore against the dirty research tree.
The current root `target/` measured **216 GiB** on September 23 (`du -sh target`); it is generated
build output, not a source-retention obligation. R0 records which active checks still need it
before a targeted or post-split `cargo clean` reclaims the space.

## 5. GitHub issues

- **Reset (done, September 23).** The open issues were triaged against §2:
  - **Closed as not planned**, since the protein/structure application was dropped: #53, #52,
    #51, #46, #44, #38, #11, #10, #9 and #29. The retired artifact owner's #6 is also closed.
  - **Folded:** #12–#15 and #50 into K5 (#76); #54, #34 and #33 into #62; #49 into #48; #39 into
    #27.
  - **Kept and relabelled by object:** #62, #61, #48, #40, #35, #32, #31, #30, #28, #27, #26,
    #24, #23, #22, #21, #20, #18, #17, #16 and #5.

  The labels now follow the objects (`holon`, `ratio`, `generator`, `pair-contact`, `tube`,
  `deposition`, `receiver`, `holarchy`, `physics`, `hnn`, `device`, `extraction`,
  `research-math`, `restructure`) beside the kind and evidence labels. The retired
  `interaction`/`realization`/`variation`/`codec`/`construction`/`join` labels and the GitHub
  defaults are deleted.
- **Tracking (created).** The parent is #63.
  - Restructure steps: R0 #64, R1–R2 #65, R3 #66, R4 #67, C #68, M1 #69, M2 #70, D #71.
  - Construction: K1 #72, K2 #73, K3 #74, K4 #75, K5 #76.
  - The machine resumes after M1: #17, #16, #18, #61.
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

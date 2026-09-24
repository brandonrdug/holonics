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
3. **The HNN is device-resident today, so its move and its backend-neutral port are separate
   steps.** Of 219 `native_ecology` files, 106 launch kernels or hold resident sections. So do 35 of
   93 `holonics-hna` files. No host reference implementation of the HNN field exists, and the engine's
   `build.rs` runs `nvcc`. The resident HNN therefore moves **as it is** into `holonics-cuda::hnn`.
   Main `holonics::hnn` owns the backend-neutral part: the field law, source moments, adjoint
   contracts, the execution-port trait and, over time, a host reference. The port and host
   reference are then built method by method (campaign K2 in §4). Neither blocks the restructure.
   `holonics-apple` implements the same port later.
4. **Crate count: `holonics` and `holonics-cuda` now, `holonics-apple` later.** `holonic-words` is
   a temporary host crate (it currently uses `std`): `holonic-core::PrimeChart` consumes
   `ModularWords`, while the Rust NVPTX `accelerators/cuda-kernel` depends directly on
   `soma-abi`, **not** on `holonic-words`. Both host words and the device kernel use
   `soma-abi::section_layout_cuda` arithmetic for parity. The kernel's committed PTX is
   embedded at compile time by `holonic-mount` library/tests/gates, loaded from those bytes by
   engine `section_layout_adoption` tests, and used by `holonic-life`'s Soma CUDA lineage; it is
   not a separate runtime file dependency. Its launch owners (`SOMA_PTX`, `register_launch`,
   `live_event_launch`) cannot be retired by removing `life` alone. The HNN uses the 83 C++
   kernels in `holonic-engine/kernels/`, generated through the engine's NVCC build script.
   After R2 resolves the Soma lineage and the surviving host and PTX callers, the word rings
   (`ExactRing`, `CheckedIntegers`, `ModularWords`) can fold into `holonics::ratio`, since residue
   arithmetic is ratio arithmetic. If a Rust device kernel still needs shared `no_std` source,
   retain only that small arithmetic carrier until the backend cut can consume it directly.
   Host/device parity for the `.cu` kernels remains tested against host arithmetic.
   `accelerators/rust-gpu` (Vulkan, already ruled out for production) retired with its unconsumed `holonic-surface` host crate and SPIR-V artifact in R2. The 2026-08-09 stale-artifact record is historical evidence; its then-current recommendation not to remove the path is superseded by this September 23 disposition.
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
   `Holon::interconnect(parts, joins) -> Result<Holarchy, GluingDefect>`. `Holarchy::whole()` is
   the joined Holon, and the constituents, incidence and gluing are retained. `view`, `count` and
   `refine` follow §3.1. A recursively generated family carries its constituent generator. This
   ties the new object to an existing operation rather than adding a parallel constructor.
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
| Holon `H=(K,∂_A;Π;𝒟;𝓔;G;π)` | the law and its ports, not its state; interconnection of Holons is a Holon; passivity proved | `Holon/{Law,Port,Dirac,Complex,Element,Generator,Restriction,Conformance}` | `holonic-core::{holon,law,port,dirac,complex,element,generator,restriction}` |
| Complex, holon/coholon pairing | `∂²=0`; `d=∂ᵀ`; Stokes; power is the pairing | `Objects/Pairing`, `Holon/Complex` | `holonic-core::complex` |
| Constitution (element relations) | storage `C`, `K`, resistive `D⪰0`, sources, active relations with power, pumps; modes `Kv=ω²Cv` | `Holon/Element`, `Holon/MomentStorage` | `holonic-core::element`; normal law `NormalConstitution`; moment storage |
| Generator | initial configuration (key), clock, phase lift; helix = circle + carry; fractal family = words, restrictions, scale square, first arrival | `Geometry/PhaseCarry`, `Holon/Generator`, `Foundation/FractalPacking` | `holonic-core::generator`; `relational-geometry::winding` |
| Helical pair contact | slip `J`, `Q=⟨Δ|Δ⟩`, `DQ=2J*Δ`, Farey lock address; contact material `ΣwJ*DJ` | `Transport/HelicalPairInteraction`, `Geometry/PairResonance`, `Millennium/Farey` | `holonic_interaction`, `holonic_chain`, `relational-geometry::screw` |
| Complex parametron (HNN physical instance) | LC storage↔flow at `ω=1/√(LC)`, pump, half-turn Ising lock; perceptron = locked-sheet face | `Objects/Parametron` | `cuda_refine::complex_parametron` (device); no host owner yet |
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
Holon law, exact geometry and algebra, elementary operations and the backend-neutral HNN law.
The resident HNN realization belongs to the backend (§0.3). A separate `holonics-hnn` package
is not needed: the law sits in main, and each realization sits in its backend.

The target is two maintained libraries on this branch, three when Brandon adds Apple, plus
`holonic-words` only under §0.4:

| Package | Internal ownership | Existing sources to sort at R0 |
|---|---|---|
| `holonic-words` (conditional, §0.4) | A `no_std` exact word ring and section ABI, compiled once for the host and once by a Rust device kernel. It exists only while such a kernel consumes it. Otherwise it folds into `holonics::ratio`. | `holonic-words` and the live part of `soma-abi::section_layout_cuda`. Its present dependency on `soma-abi`/`body` is reversed or retired with the Soma lineage. |
| `holonics` | Main library: typed ratio/remainder/inversion and jets; geometric frames, exterior cells, pair and tube/tower charts; the one Holon law with active receiving, composition, restriction and deposition; a proposed receiver-relative `Holarchy`; fluid, wave, spacetime and thermal constitutive instances; equation extraction as a Holon boundary; and the backend-neutral HNN: field law, source moments, adjoint contracts, execution-port trait and host reference, the last built in K2. The complex-parametron chart is an HNN physical chart. No CUDA dependency and no `nvcc`. | `holonic-core`, `relational-geometry`, live `holonic-structure`, the source-neutral parts of `holonic-engine` (extraction included), and the law/declaration parts of `holonics-hna` and live `holonic-life`. |
| `holonics-cuda` | CUDA realization: driver, allocation, transfer completion, section layout and partition, hardware cover, the `.cu` kernels and their `build.rs`, and `hnn/`, the resident HNN field moved as it is (§0.3). It depends on `holonics` and implements the HNN execution port as K2 defines it. It does not redefine the material or loss law. | `holonic-mount`, engine `cuda_refine`, `resident_section`, `kernels/`, `hardware_cover`, `section_partition`, the resident `native_ecology/**` and `embedding_fiber`, the resident `holonics-hna` `native/**`, and the device files of `holonic_intelligence`. |
| `holonics-apple` (later) | Apple silicon implementation behind the same typed execution port, with its own kernels and placement. Create it only on Brandon's Mac branch after its actual implementation is ready. | No Linux-branch move. |

The dependency direction is `(holonic-words →) holonics → holonics-cuda` (and later
`holonics-apple`); arrows mean *may be used by*. Applications select a backend and depend on
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
  holarchy/    Holarchy returned by interconnect: whole, constituents, gluing, view/count/refine
  physics/     fluid, wave, thermal, spacetime, information (each created with its first implementation)
  extraction/  foreign equations as Holon element/generator relations
  hnn/         field law, source moments, adjoint contracts, execution port, host reference (K2)

crates/holonics-cuda/src/
  driver/      context, module, stream, allocation, transfer completion (from holonic-mount)
  section/     resident sections, SLOT_WORDS, section partition, hardware cover
  hnn/         the resident HNN field and session, moved as it is
  extraction/  device parts of equation extraction, if kept
kernels/       .cu/.cuh sources and build.rs
```

There is **no public `exact` object/module**. Integer/rational/algebraic/matrix carriers live
privately beside the operators that use them; exact source descriptions and certified
remainders are the default mathematical contract. `holonic-words`, while it exists, is a small
implementation ABI that host and device compile from the same source. It is not a second
mathematical foundation. A dyadic `0.5` and `1/2` can have the same exact numerical face; the ratio object
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
Holarchy. Under a certified finite disjoint refinement, counts have a stated relation; with
overlap, changed receivers or non-finite fibres, that relation requires a correction or remains
unresolved. The whole itself may receive, act, and compose with other Holarchies.

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
relation at their stated precision. The present graph does **not** satisfy this cut: engine
imports `mount` and runs `nvcc`; HNA imports engine and life; `holonic-words` imports `soma-abi`;
and the HNN field has no host reference (§0.3). M1 therefore moves the resident HNN into
`holonics-cuda` with its current behavior. K2 then extracts the port and host reference one
method at a time, each against the CUDA return. A module with a distinct
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
Holon { complex, ports, dirac, elements, generators, restrictions }
HolonState { configuration, clock_states }           // no event tape
ReceiverRole { holon, state, port, frame, clock, aperture }
Holarchy { whole, constituent_generator, incidence, gluing, restrictions }
Receipt { source, receiver, locus, frame, clock, grain, face, unresolved }
Ratio<Left,Right> { left, right, comparison_transport, log_branch }
InteractionReturn { source_next, receiver_next, face, receipt,
                    boundary_currents, power_balance, unresolved }
```

`Holon::interconnect` must join the **complete** complex, named ports, material/pumps,
generators and restrictions or return a typed gluing/clock defect. The current
`holonic_core::Holon::interconnect` joins only the scoped port body/active law/generators;
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

**The restructure** moves and retires existing code with its current behavior, verified by the
existing suites (§0.9):

1. **R0 census (first; nothing retired before it).** Record the
   exact HEAD, dirty files, worktrees/branches, build outputs and saved artifacts. Commit or
   account for the uncommitted Lean/research work and the paused WIP branches. Produce
   `docs/plans/THE_REPOSITORY_CENSUS.md` with one table per area:
   - Rust owners and examples;
   - Lean files outside the foundation;
   - documents and records;
   - issues.

   Each table's columns are: path, lines, elementary object or application, consumers
   (build-confirmed), superseding owner, disposition (**keep** / **fold** / **retire**, applying
   §0.1), target (§3) and verification. **The census is Codex's working instrument, not a
   review for Brandon** (September 23): he has already stated what is kept (§0, §2), so dispositions
   follow those rules and proceed without a review step. A disposition that would delete one of
   §2's objects or a checked non-duplicate theorem is a mistake in the census, not a question to
   escalate.
2. **R1: Rust with no consumer.** Retire engine modules and examples first; their laws move to
   Lean or a guide first, as §0.1 requires.
3. **R2: the Soma/`life` lineage and unconsumed crates.** Covers `holonic-body`, `-membrane`,
   `-surface`, `-circulation-abi`, `-language`, `holonics-workspace`, the dead parts of
   `holonic-life`, and `accelerators/` per §0.4. The isolated Vulkan surface cut is complete;
   continue with the remaining consumers and decide `holonic-words` here. The
   [membrane owner audit](census/R2_MEMBRANE_EDGE.md) finds a live receive/standing runtime used by
   `life` and CUDA: its source moves with callers into main `holonics` during the Rust cut. The
   ERST `.holon` reader/deed adapter has been retired in R2 while retaining the runtime rest-image
   codec. The
   [workspace owner audit](census/R2_WORKSPACE_EDGE.md) finds a live workbench application edge:
   disposition its old persisted readers under §0.2, then move retained application operations
   into workbench or retire the command after the `life`/HNN owners move. Neither live crate is a
   safe delete-only R2 cut; #65 stays open across those caller moves.
4. **R3: the Lean foundation cut.** Cut the §0.10 edges, curate the `Holonics` root and retire
   duplicate or wrapper theorems. Build `ElementaryHolonics.Framework` and the affected research
   modules.
5. **R4: compatibility debt.** Remove every alias, forwarding path and legacy decoder (§0.2).
6. **C: finish the paused consolidation.** Rebase phases 11, 12a and 12b (WIP branches) onto the
   reduced tree, then do phase 14. The [Phase 12a integration map](census/C_PHASE12A_INTEGRATION.md)
   records its current operand-rest cut, writer-selected tags and remaining C acceptance.
7. **M1: the Rust cut.**
   - Create `holonics-cuda` and move the driver, sections, kernels and the resident HNN into it as
     they are (§0.3).
   - Merge `holonic-core`, `relational-geometry`, live `holonic-structure`, the source-neutral
     engine, the live membrane receive/standing runtime and extraction into substantive
     `holonics`. Move backend-specific membrane execution with the resident CUDA HNN.
   - Update every caller in the same commits (§0.2).
   - Verify: `holonics` builds without CUDA, `holonics-cuda` owner tests pass on the card, and
     the workbench/all-target check passes.
   - Clean the old `target/`.

   **M1 dependency prerequisite (landed in the facade cut):** `holonics` no longer depends on HNA, engine or life,
   and it no longer forwards their `hna`, `engine`, `soulkiller` or `interop` surfaces. The workbench
   selects the direct HNA and engine packages. `core`, `structure` and `geometry` remain re-export
   boundaries until their source owners move; they are not yet represented as internal Holonics code.
8. **M2: the Lean move.** Move paths to `lean/` (`Holonics` and `HolonicsResearch`) and build both
   targets. Rename `Soma.Holonics` to `Holonics` as a separate mechanical commit.
9. **D: documents (the restructure's closing acceptance).** All to the verified paths:
   - **Operator contracts:** [ELEMENTARY_OBJECTS](../ELEMENTARY_OBJECTS.md) owner map (current →
     verified), [HOLON](../HOLON.md) operator methods, [THE_MACHINE](../THE_MACHINE.md) and
     [HNN_FORMULA](../HNN_FORMULA.md) owner columns, [RECEIVER_HOLARCHY](../RECEIVER_HOLARCHY.md),
     [FORMAL_FRAMEWORK](../FORMAL_FRAMEWORK.md), [RUST_FRAMEWORK](../RUST_FRAMEWORK.md),
     [ARCHITECTURE_MAP](../ARCHITECTURE_MAP.md), and the CLAUDE.md/AGENTS.md owner tables.
   - Guides that name `holonics::hna` or retired owners (ATHENA, NATIVE_HNA, CONVERSATION_DATA,
     HARDWARE_AND_MODALITY_BOUNDARIES, the workbench guide) are updated or deleted.
   - `CONSTRUCTION_STATE.md`, the roadmap and `docs/REPOSITORY.md`.
   - **Last: rewrite `README.md` in full** to describe the repository as it now stands: the
     libraries and their operators, `lean/`, the HNN, the applications, docs and research. The
     restructure is complete only when the README matches the tree.

**Construction campaigns** run on the new layout, each with its own issue:

- **K1:** complete `interconnect -> Holarchy` (joined complex, named ports, pumps with a declared
  joint clock, restrictions, or a typed defect), and the joint `interact`/`receive` return (§3.7).
- **K2:** the HNN execution port and host reference, one method at a time against the resident
  CUDA return. This is the precondition for `holonics-apple`.
- **K3:** finite physics cells. §3.5's tests cover polygon/cube reflection and join, wave
  interference and propagation, the Euler/NS control volume and thermal exchange.
- **K4:** the stress-energy source map and moving observer, the information-to-material port, and
  independent clock axes (§3.6).
- **K5 (#76):** the device-realization debts in `holonics-cuda` (formerly #12–#15 and #50).
- **The machine** resumes after M1: GitHub #17, #16, #18 and #61, source-port growth of ring g0,
  and the model-versus-uniform gap.

Issue map: parent #63; R0 #64, R1–R2 #65, R3 #66, R4 #67, C #68, M1 #69, M2 #70, D #71;
K1 #72, K2 #73, K3 #74, K4 #75, K5 #76.

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

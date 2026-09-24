# Holonics

Holonics is Brandon's mathematical, physical and computational research programme, grounded
in the reality of difference. It develops a common language for how situated things interact,
change and become observable. Its working ambition is a constructive theory that connects
mathematics, physics, computation and living systems. Claims retain their hypotheses and
evidence; open constructions remain open.

The elementary object is a **Holon**: a law with incidence, ports, material relations,
generators and scale restrictions. Holons join at ports; a receiving face reads a situated
comparison. The [elementary objects](docs/ELEMENTARY_OBJECTS.md) and
[the machine](docs/THE_MACHINE.md) define the laws. **HNN** is neural machinery made from those
objects, **Athena** its first intended product, and **Eros** their collective formation and
composition. The intended generally useful Athena assistant is still under construction.

## Start here

| Need | Read |
|---|---|
| The mathematical object and its operative equations | [The machine](docs/THE_MACHINE.md), [Holon](docs/HOLON.md), [HNN formula](docs/HNN_FORMULA.md) |
| What is implemented and what remains open | [Construction state](CONSTRUCTION_STATE.md) |
| Construction order and current restructuring | [Roadmap](docs/plans/THE_ROADMAP.md), [repository restructure](docs/plans/THE_REPOSITORY_RESTRUCTURE.md) |
| Formal and native source owners | [Elementary objects](docs/ELEMENTARY_OBJECTS.md), [architecture map](docs/ARCHITECTURE_MAP.md) |
| Research derivations and scoped results | [Research routes](research/records/README.md), [research entry](research/README.md) |
| How Codex and Claude work in this tree | [AGENTS.md](AGENTS.md), [CLAUDE.md](CLAUDE.md), [development method](docs/DEVELOPMENT.md) |

## The checkout today

The root `Cargo.toml` currently declares **12 workspace packages** (9 libraries and three applications).
The restructuring work is in progress; these are the paths that exist now.

| Path | Current role |
|---|---|
| `crates/holonics/` | Main Holon law, structural carriers, receiver-relative geometry, live receiving/standing and exact operators |
| `crates/holonic-engine/`, `crates/holonics-hna/`, `crates/holonic-life/` | Native field, HNN sessions, equation extraction and inherited implementation layers |
| `crates/holonics-cuda/`, `crates/holonic-words/` | CUDA driver/launch boundary and exact word arithmetic |
| `formal/elementary-holonics/` | Current Lean/Lake project; the final `Holonics` and `HolonicsResearch` roots remain an M2 move |
| `applications/`, `accelerators/` | CLI, data/tools and device-specific targets |
| `docs/`, `research/` | Maintained contracts, plans, derivations, experiments and papers |

[Repository organization](docs/REPOSITORY.md) maps the remaining directories and historical
locations. Historical code and records retain their cited revisions; a source name does not
by itself certify current use.

## The intended libraries

The [restructure plan](docs/plans/THE_REPOSITORY_RESTRUCTURE.md) audits consumers and retires
superseded layers before moving code. The **main `holonics` crate will own the actual Holon
laws and HNN**, organized by elementary object rather than acting as a facade:

| Library | Responsibility |
|---|---|
| `holonics` | Ratio/remainder, geometric transport and pair/tube charts, the Holon law and its operators, receivers and receipts, the Holarchy returned by interconnection, equation extraction, and the backend-neutral HNN law and execution port |
| `holonics-cuda` | CUDA realization: driver, sections, kernels and the resident HNN field |
| `holonics-portable` | Shared `no_std` laws compiled by both the host and detached Rust CUDA kernel; the former body source has moved, while ABI/word consolidation remains pending |
| `holonics-apple` (later) | Apple silicon implementation on Brandon's separate branch |

That is three maintained Rust libraries on Linux after consolidation and four after Apple.
The portable leaf began by replacing the current `body` package; `soma-abi` and `holonic-words`
remain separate pending classification of their shared host/device laws. The main library
builds without CUDA; its HNN host reference is built after the move, one method at a time
against the CUDA return.
Its physical instances must carry fluid stress/pressure, wave propagation, spacetime
stress-energy, heat/entropy currents and the active receiver law with their stated hypotheses;
pair slip and pumps alone do not supply those equations.
The current workbench remains an application package while its deployment boundary is
inventoried. Lean will become one top-level `lean/` Lake package with a public `Holonics`
library and dependent `HolonicsResearch` library. Those names describe the **target**; the
current paths above remain authoritative until their moves are verified. Lean verifies laws at
its own scope and does not run inside HNN cultivation or inference.

## Working in this repository

Use the owner and consuming call in [AGENTS.md](AGENTS.md) or [CLAUDE.md](CLAUDE.md), then read
the relevant research route and source. A moved operator keeps its typed source and receiver,
forward law, variation, saved face and actual consumer. The current tree contains paused
consolidation branches and uncommitted mathematical work; the restructure census accounts for
them before retirement. Native build and Lean check commands live in
[DEVELOPMENT.md](docs/DEVELOPMENT.md) and [FORMAL_FRAMEWORK.md](docs/FORMAL_FRAMEWORK.md).

Holonics is dual-licensed under [MIT](LICENSE-MIT) or
[Apache-2.0](LICENSE-APACHE), at your option. Third-party material retains its own notices.

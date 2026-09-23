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

The root `Cargo.toml` currently declares **16 library packages and three application packages**.
The restructuring work is in progress; these are the paths that exist now.

| Path | Current role |
|---|---|
| `crates/holonic-core/`, `crates/relational-geometry/` | Holon facets, exact algebra and geometric source laws |
| `crates/holonic-engine/`, `crates/holonics-hna/`, `crates/holonic-life/` | Native field, HNN sessions, equation extraction and inherited implementation layers |
| `crates/holonic-mount/`, `crates/holonic-words/` | CUDA driver/launch boundary and exact word arithmetic |
| `crates/holonics/` | Current public Rust entry point; its default `native` feature still reaches the device stack |
| `formal/elementary-holonics/` | Current Lean/Lake project; `ElementaryHolonics.Framework` is the curated entry point |
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
| `holonic-words` | Small portable exact word and section ABI shared by host and device |
| `holonics` | Holon/port law, exact geometry, pair, parametron, tube, deposition, ratio, receipt, equation extraction and an internal backend-neutral `hnn` module |
| `holonics-cuda` | CUDA implementation of the HNN execution port |
| `holonics-apple` (later) | Apple silicon implementation on Brandon's separate branch |

That is three maintained Rust libraries now and four after Apple. The main library builds and
runs its host/reference HNN without CUDA; a caller supplies a device executor when needed.
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

# Repository organization and recovery

[definition] The repository separates live implementation, current design, scientific evidence
and frozen history. A file's age helps locate neglected work; it does not decide whether a
mathematical subject or a source dependency is obsolete.

## Maintained reading surfaces

| Question | Owner |
|---|---|
| What is being built, and why is its geometry the learning? | [`THE_MACHINE.md`](THE_MACHINE.md): read first |
| Where are the relevant derivations and experiments? | [Research routes](../research/records/README.md) connect subject, source law and consumer; [research entry](../research/README.md) distinguishes records, experiments, notebook and papers |
| What does the framework mean? | `docs/canon/`, with `FORMAL_FRAMEWORK.md` connecting formal subject owners |
| What machinery is being built? | `ARCHITECTURE.md`, `HNN_COMPOSITION.md`, and the HNN network contract in the linked blueprint |
| What must a changed operation preserve? | Its formal/native owner and the blueprint's mathematical implementation contract |
| In what dependency order do we work? | `docs/plans/THE_ROADMAP.md` only |
| What has returned and what is unfinished now? | `CONSTRUCTION_STATE.md` only; completed evidence is linked to dated records |
| How do agents construct, measure and audit? | `AGENTS.md` for Codex, `CLAUDE.md` for Claude, `DEVELOPMENT.md`, `AGENT_PROTOCOL.md` and the focused research skill |
| How does a caller use an existing interface? | The relevant interface guide, such as `NATIVE_HNA.md`; API/wire labels remain stable |

[project-postulate] Consolidation updates the owner of a statement and its current consumers.
Do not append a contradictory correction in another guide or copy current progress into every
architecture page. Preserve completed recipes and measurements in their existing records and
Git. Historical product names do not define current mechanisms; HNN is the machinery and Athena
its first product. This map supplies navigation, not another status index or scheduler.

## Directory map

| Root | Contents |
|---|---|
| `crates/` | All live Rust libraries: public framework/HNN APIs, native engine, lifecycle, geometry, substrate and apparatus. |
| `applications/` | The `holonics` CLI/workspace, private [conversation-data preparation](CONVERSATION_DATA.md), and standalone research/document tools. |
| `accelerators/` | Device-only Rust-GPU/CUDA targets with their independent toolchains and committed boundary artifacts. |
| `formal/` | Live project-owned Lean sources: elementary holonics, kernel-witness fixture and the independent RH source-transport project. |
| `docs/` | Current architecture, interfaces, developer guide, doctrine, references and active plans. |
| `research/` | Dated records and receipts, experiments, authored papers and personal notebook material. |
| `archive/` | Completed/superseded plans, frozen predecessor source and retired bodies. These do not schedule construction. |
| `tools/` | Optional helpers for relevant work; no blanket gate suite. |
| `.local/` | Ignored local artifacts, data, scratch, coordination archives and recovery backups. |
| `target/` | Conventional reproducible Cargo output; not source or a model artifact. |

[established-bounded; source-inspected] The Rust package graph is still one root Cargo workspace.
The old `soma/` parent no longer divides host Rust libraries, device targets, formal projects and
tools into a parallel tree. Package names for older substrate components remain stable; the
public HNN library is now `holonics-hna`, and `holonics` is the framework entry point.
Its [Rust API](RUST_FRAMEWORK.md) exposes the existing structural and geometric libraries
without default features; the default native implementation retains its device dependencies.

[project-postulate] The [September 23 restructure](plans/THE_REPOSITORY_RESTRUCTURE.md)
supersedes this layout as a **target**, while this page maps the present checkout. It reduces
the maintained Rust library graph to a substantive main `holonics` (Holon laws, geometry,
extraction and the backend-neutral HNN law and port) → `holonics-cuda` (driver, kernels and the
resident HNN). `holonic-words` survives only while a Rust device kernel consumes it. Brandon's
later `holonics-apple` package implements the same port on his separate branch. The Lean target is one top-level
`lean/` Lake package with `Holonics` and dependent `HolonicsResearch`. Until verified moves land,
`crates/` and `formal/` above are the correct source paths. The operator guides distinguish
current owner from target owner throughout the migration.

## Relocation guide

| Former location | Current location |
|---|---|
| `soma/{body,abi,membrane,surface,mount,life}` | Corresponding `crates/holonic-*` libraries |
| `applications/athena-alpha` | `crates/holonics-hna` |
| `applications/holonics-application` | `crates/holonics-workspace` |
| `soma/kernel`, device-only mount children | `accelerators/` |
| `soma/formal` | `formal/` |
| `soma/tools/{derivation-atlas,holon-plate}` | Optional applications under `applications/` |
| `soma/tools/record-index` | `archive/tooling/record-index/` |
| Remaining `soma/tools` experiments | `research/experiments/legacy-tools/` |
| `canon` | `docs/canon/` |
| Active `blueprint` documents | `docs/plans/` |
| Completed/superseded `blueprint` documents | `archive/plans/` |
| Earlier `archive/blueprints` | `archive/plans/legacy/` |
| `bibliography` | `docs/references/` |
| `reference` | `archive/reference/` |
| `analysis`, `notebook`, `papers` | `research/experiments/`, `research/notebook/`, `research/papers/` |
| `meta/SOURCE_SHAPE_BASELINE.tsv` | Retired under `archive/tooling/baselines/` |
| Root generated claim index | Retired snapshot under `archive/tooling/` |
| Universal conceptual crosswalk | [ARCHITECTURE_MAP.md](ARCHITECTURE_MAP.md) |
| `research/equation-atlas` | `archive/equation-atlas/`; retired historical graph |
| `output`, `data`, `runs`, `tmp` | `.local/artifacts`, `.local/data`, `.local/runs`, `.local/scratch/previous` |
| Untracked September 2 fleet files | `.local/archive/fleet-2026-09-02/` |

[definition] Dated records preserve their original measurements, quoted messages and historical
command/source-path testimony. Markdown navigation links are relocated; frozen predecessor
source is not rewritten into a claim about today's body. Use this map or the recorded Git revision
when following an old inline path. No compatibility symlink makes an old root look active.

## Finding material by subject and chronology

Start with [architecture](ARCHITECTURE.md), [Soulkiller](SOULKILLER.md), [Athena](ATHENA.md) and
[interop](INTEROPERABILITY.md). The [owner map](ARCHITECTURE_MAP.md) connects formal and executable
relations. Start with the [subject routes](../research/records/README.md), then the linked records
and actual source. Dated records remain in `research/records/`; the
[repository evidence protocol](AGENT_PROTOCOL.md) explains source and correction lineage. The
one-time imported testimony is local documentation; no database or connector is required.
The old generated claim index and equation atlas remain archived.
Completed contracts are grouped under `archive/plans/`, without becoming schedulers again.

```sh
git log --date=short --format='%h %ad %s' -- crates/holonic-engine
git log --follow -- formal/elementary-holonics/ElementaryHolonics/RH/CriticalChart.lean
rg 'Saturated|NativeConeRestrictedEcology' crates formal docs
git grep -n '20W' -- research docs archive
```

[established-bounded; source-inspected] The reorganization reviewed local modification times
and commit activity. The old root README dated to August 8 and still led into retired C++ plans;
it is superseded. Older foundational source remains live where current dependencies use it.
Notebooks and papers remain accessible research, rather than being deleted for inactivity.

## Recoverable backup

[established-bounded; process-audit] The pre-consolidation source is retained by Git reference
`backup/pre-hna-consolidation-2026-09-04` at `08965182`, and the verified full-history bundle
`.local/backups/pre-hna-consolidation-2026-09-04.bundle`. The pre-existing untracked fleet material
is separately retained in `.local/backups/pre-hna-consolidation-untracked-2026-09-04.tar`.
The private backup directory also holds the pre-move file-stat snapshot and relocation map.

[definition] Native artifacts, local data, Cargo caches and Lake caches were moved or retained,
not deleted. They are not included in the Git bundle; their existing local copies remain under
the locations above. Recovery should use a separate checkout or extraction directory so it does
not overwrite later work. The one-time relocation scripts remain private scratch, not maintained
repository governance.

## A checkout on another machine

[definition] Git supplies the native/formal source, guides, historical records and the
[imported research testimony](../research/records/2026-09-06_portable_evidence/README.md).
The retired side database and connector are not required. The
[hardware/modality guide](HARDWARE_AND_MODALITY_BOUNDARIES.md) states why the current engine/HNN
compile path is still Linux/CUDA-bound; Apple support is subsequent implementation work.

[definition] Ignored `.local/` datasets, checkpoints, weights and caches do not travel in a clone.
The [conversation-data guide](CONVERSATION_DATA.md#cultivation-and-machine-transfer) names the
private desktop material. Transfer such artifacts separately if needed, preserving their declared
source, codec and native-base dependencies; do not substitute an export receipt for the artifact.

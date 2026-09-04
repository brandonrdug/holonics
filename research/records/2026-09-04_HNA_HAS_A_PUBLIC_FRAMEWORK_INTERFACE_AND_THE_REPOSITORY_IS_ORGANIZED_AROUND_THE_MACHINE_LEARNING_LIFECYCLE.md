# HNA has a public framework interface and the repository is organized around the machine-learning lifecycle

**Date:** 2026-09-04.
**Authority:** Brandon's direct request for synthesis, unification, standardization and a
professional repository overhaul, with recoverable backup and Luna-only supporting work.
**Starting revision:** `08965182`.
**Scope:** current framework architecture and consumer intent, public native run interface,
repository organization, navigation, dependencies and verification.

## Product intent and capability

[project-postulate] The architecture guides make HNA's intended frontier-level usefulness on
consumer hardware explicit. The 20W ideology directs efficient continuous/local learning and
reuse, not a claimed twenty-watt measurement. Soulkiller is an independent dismantling apparatus;
Eros develops Athena through the native recurrent operation. Standard model recompilation is
part of the intended outward lifecycle, not synonymous with a container round-trip.

[established-bounded; source-inspected] `docs/ARCHITECTURE.md`, `SOULKILLER.md`, `ATHENA.md`
and `INTEROPERABILITY.md` reconcile the current implementation, the direct-message/research
chronology and the source owners. The existing Safetensors package bytes and custom-domain
ONNX package node are distinguished from a standard executable neural graph. Full cultivated
operator persistence and target graph/state/numeric lowering remain explicit implementation
bridges. No diffusion/SSM or arbitrary-Transformer execution claim is inferred from file parsing.

## Public implementation

[established-bounded; source-inspected] `crates/holonics` is the public Rust entry point.
`holonics::hna` exposes typed native requests and one continuing full session;
`holonics::soulkiller` exposes the admitted three-lane dismantling boundary;
`holonics::interop` exposes intake charts and its `packages` submodule exposes existing package
export/import. The implementation owners are reused, not duplicated.

[established-bounded; implemented-exact] The `holonics hna` CLI exposes `run`, `inspect`,
`infer` and `train`. Input validation refuses unsupported receivers and malformed sequences
before CUDA use. Declared histories participate in the actual native occurrence. Training's
text convenience adapter requires strict tokenized-prefix continuation and invokes the same
native operation; the source and tokenizer are application-side. The receipt names its source
kind, selected faces, predecessor/successor generations and ranks, changed populations and
census, with the full morphology trace optionally requested. It is explicitly a run receipt,
not a saved trained checkpoint.

[established-bounded; implemented-exact; measured] The actual CLI command
`target/debug/holonics --format json hna train /home/b/models/gemma-4-E4B-it .local/scratch/hna_training_sequence.json`
returned exit 0 on the consumer GPU. Three cumulative text occurrences completed three cycles
at generation 3,825 and overlay rank 5,504. The selected text faces were ` Explain`, ` the`,
and ` Hol`; they are inspected single-face results, not a qualitative answer claim. The actual
response is `2026-09-04_hna_framework_receipts/cli_training.json`.
The exact input file is preserved beside it as `training_sequence.json`; a clean checkout can
use that path in place of the original private scratch delivery path.

## Repository relocation

[established-bounded; process-audit] The backup reference
`backup/pre-hna-consolidation-2026-09-04` and verified full-history Git bundle preserve the
starting revision. A separate private tar preserves the original untracked fleet files. A
pre-move file-stat snapshot records local age/size; Git chronology and actual dependencies,
rather than age alone, determined placement.

[established-bounded; source-inspected] Rust libraries now share `crates/`; executable clients
share `applications/`; independent device targets use `accelerators/`; live Lean uses `formal/`;
current doctrine/design uses `docs/`; records, experiments, papers and notebooks share `research/`.
Completed plans and frozen source use `archive/`, and local generated artifacts/coordination
material are retained under ignored `.local/`. The `soma/` parent is gone. Cargo members,
relative dependencies, compile-time includes, current tools and document navigation were repaired.
Existing package wire schemas and frozen source were preserved.

[established-bounded; source-inspected] The public HNA package is `holonics-hna`, and the
specialized snapshot/workspace package is `holonics-workspace`. Other historical Cargo package
names remain where renaming would add no interface clarity. The framework facade is consumed
by the CLI. All 17 live host packages remain in one Cargo workspace; independent device targets
retain their own toolchains. The obsolete record-index application is no longer a workspace member.

[established-bounded; source-inspected] Root README now introduces the ML framework and its
actual commands. AGENTS.md is reduced to the operative contract, linking the relocated
retraction/evidence protocol instead of embedding it. Its previous form is preserved under
`archive/operations/`. The document law and workbench entry points now agree with that organization
and with the current native interface; their prior contracts are also preserved there.

## Workflow retirement and chronology

[historical; source-inspected] Initial consolidation work attempted to relocate and repair the
old index/validation tools. Brandon corrected that direction: the equation atlas had already been
superseded by Provenance, and untouched papers and obsolete navigation machinery were not the
work. The repair effort was stopped and the obsolete tools archived, not replaced.

[established-bounded; source-inspected] `archive/equation-atlas/` preserves the original chart
data. `archive/tooling/` retains the generated claim index/snapshot, record-index, blanket gate
suite, document/epistemic/authority/equation validators and source-shape baseline. The local
equation validator last changed August 21; record-index's substantive history ends at the August 7
import. The August 19 profiling scripts now live with research experiments. Recently touched
orchestration files were not presumed relevant merely because previous agents had repaired them.

[definition] Current navigation uses the actual directory organization, subject guides, manual
owner map and Provenance. `tools/` contains an optional Lean build helper and its README, with
no blanket validation policy. Derivation-atlas remains an optional elaborated proof-DAG application,
not a general navigation gate. Typst sources are retained as research and are compiled when used or
edited, not as a prerequisite to unrelated Rust work. Private relocation scripts are one-time
scratch, not a maintained census or replacement suite.

## Verification

[established-bounded; process-audit] Direct verification returned:

- `cargo test --workspace --lib --bins --tests --no-fail-fast -j4` exercised the active workspace
  with GPU access. Every target except the plate-mouth test passed; its one stale default-root
  assertion was corrected to `.local/artifacts`, and `cargo test -p holon-plate --test plate_mouth`
  then passed all 12 tests. Successful targets were retained, not rerun as a ritual. The engine
  library passed 2,030 tests and the life library 492; the public HNA and CLI tests are included.
- `cargo check --workspace --examples -j4` passed after repairing relocation-sensitive includes.
- The actual three-cycle native CLI training run returned the receipt described above.
- The relocated RH CriticalChart target built all 8,835 jobs successfully, with existing linter
  warnings retained. Formal changes are relocation/comment paths, not proof-body changes.
- One-time inspection of the new/current entry-point links found no missing targets;
  `git diff --check` passed. No link-checking tool was added.

[definition] The earlier metadata/Typst checks attempted before Brandon's steering are not the
current completion policy and are not counted as justification for retaining the retired suite.

[definition] No model weights, historical source, native artifacts or build caches were deleted.
The backup/recovery and old-to-new path guide is `docs/REPOSITORY.md`. The completed mathematical
and bounded runtime results retain their prior scopes; the consolidation neither claims frontier
quality nor treats it as an irrelevant or impossible goal.

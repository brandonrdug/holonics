# Worker brief, receipts and wave protocol

[definition] This is the part of the [operating contract](../AGENTS.md) a delegated worker needs.
The primary agent inlines the relevant sections into each worker prompt, so a worker does not read
AGENTS.md, the roadmap, DEVELOPMENT.md or CONSTRUCTION_STATE. It schedules nothing and gates
nothing. The strongest validation in this project is execution against reality — the program
running, predicting real structures accurately, at a usable cost. Everything here exists to stop
repeating work that has already been answered, so that effort goes there.

## Wave shape

[project-postulate] Brandon's September 19 workflow ruling, from the
[September 17–19 audit](../research/records/2026-09-19_THE_WAVES_REPEATED_READING_AND_UNCOORDINATED_BUILDS_NOT_DISTRUST.md):

- At most **three** constructing workers in parallel, on **disjoint owner path sets** written into
  their prompts; then **one** reviewer that spawns nothing. If the work does not split into disjoint
  sets, use two workers or one. A join that consumes two workers' returns is a sequential worker.
  Claude sessions use Opus 5 workers and a Sonnet 5 reviewer; Codex sessions use Luna.
- All workers share one working tree and one `target/`. Cargo's build lock serializes them, so a
  worker builds and tests **only its own module scope**. Crate-wide, workspace and device runs are
  the primary's, once, on the integrated tree.
- A worker's **judgement** is testimony: the primary inspects the changed owner and its consuming
  call. A worker's **measurement** — a test count, a build exit, an axiom audit — is a receipt.
  Nobody re-runs a receipt whose tree is unchanged.

| Actor | Runs | Does not run |
|---|---|---|
| Worker | `cargo test -p <crate> --lib <module>::` · `cargo check -p <crate> --lib` · `lake build <its target>` with `#print axioms` on new theorems | unfiltered crate tests · `--workspace` / `--all-targets` · crate-wide clippy · any `--ignored` / `--include-ignored` device suite · anything under another worker's paths |
| Primary | one integrated broad run · one serial device run (`--test-threads=1`, no other GPU process) when native conduct changed · full `lake build` when Lean changed · the commit | a module scope whose receipt names the current tree |
| Reviewer | reading · at most one distinguishing probe per confirmed suspicion | spawning · device suites · any receipted scope · repository edits |

## Receipts

[definition] [`VERIFICATION_RECEIPTS.tsv`](VERIFICATION_RECEIPTS.tsv) is an appended log of checks
that already ran: `when, tree, dirty, scope, command, result, secs, who, log`. `tree` is the commit
the check ran on; `dirty` lists the uncommitted paths in the scope, or `-`. A receipt records an
answer so the question is not asked again. It runs nothing, grades nothing and blocks nothing; a
missing receipt only means the check runs. Workers return receipt lines in their final message and
the primary appends them. At each wave commit, drop lines superseded by a newer pass of the same
scope; history lives in Git.

[definition] A recorded pass is relied on when nothing under the scope's paths changed since:

```sh
git diff --quiet <receipt-tree> -- <crate>/src <path-dependency>/src   # exit 0: trusted
```

and the `#toolchain` line is unchanged. **One run is owed regardless:** the first run of a scope
on the integrated tree after two or more workers' edits are combined. That is the primary's
closing run and the only place a `workspace` or `device:*` receipt is written.

## Before writing that something is absent, and before founding anything

[project-postulate] Run the cross-language search and paste its receipt beside the sentence:

```sh
.agents/bin/prior-art 'prose name|LeanCamelCase|rust_snake_case|adjacent concept'
```

Zero hits license "the repository has no X" under the existing `source-audit` tag. Any hit
licenses only "this owner has not composed X, whose owner is `<file>::<decl>`" — write that, and
name the owner. Research records are titled as full sentences, so the title search the script
prints is the cheapest index the repository has; read the matching records before founding a
unit. Two September failures were each one such command away: a source comment said the repository
had no Lorentzian metric while 259 files mention one and `HolonicCurvedArcEinstein.minkowskiMetric`
existed; and the neck/junction/jet plans were written without the already typed Holonic
Interaction. A test may assert that a statement names the object still owed; it may not assert a
sentence about what the tree lacks.

## Decisions

[project-postulate] Resolve a choice from the mathematics and the context, proceed, and mark the
sentence `[agent-inferred]` with one line saying what it was inferred from. Brandon corrects these
retroactively. There is no state for waiting on a ruling; an unresolved question is not a return.

## Standing invariants and their commands

| Invariant | Command |
|---|---|
| No float on a carrying or deciding path | `rg -n '\bf32\b\|\bf64\b' <your files>` and account for every hit |
| New Lean theorems are axiom-clean | `#print axioms <name>` in the target; no `sorryAx` |
| Every Lean name cited from Rust exists | `cargo test -p holonic-engine --lib lean_citations::` |
| A value enters only through its constructor; wires and remounts re-validate | inspect `pub` fields and `Deserialize` impls in your files |
| Declared sizes are bounded before the work they size | `rg -n 'with_capacity\|vec!\[' <your files>` against the owner's ceiling convention |
| Plan tags (T6, B7, D3 …) | `rg -n '\*\*T6\b' docs/plans` |
| Owner lookup | `rg -n '<term>' docs/ARCHITECTURE_MAP.md` — search it, do not read it through |

## Vocabulary

[definition] The general object is the **tube**. A **tower** is what one instantaneous frame of
it shows. A **staircase** is its passage between grains or difference orders. A **Holonic
Interaction** is `|source⟩`, a standing medium `H_int`, a dynamic `H_pert` and `⟨perspective|`;
a **neck** is the pinhole station where flux converges and then diverges into the next medium.
Products and plan documents are names; organize work by the machinery.

## Worker prompt skeleton

```text
# Wave <N> worker <k>/<n> — <owner>
Issues you advance: #<n>, #<m> (read them with `gh issue view <n>`; do not edit them).
Your paths (edit nothing outside; if you must, stop and report):  <paths>
Shell is fish: use `bash -c` for pipelines. CUDA: PATH=/opt/cuda/bin:$PATH.
Run only: <module-scoped commands>.  Forbidden: crate-wide/workspace/device runs.
Sections of docs/WORKER_BRIEF.md inlined: receipts, prior-art, decisions, invariants, vocabulary.
Contract: <plan document and anchor>.  Existing owners to compose: <files/declarations>.
Task: <operands, law, consumer, completion evidence>.
```

## Worker return

```text
CHANGED FILES            path  +lines
OUTSIDE MY PATHS         path — why it was required
RECEIPTS                 tab-separated lines for VERIFICATION_RECEIPTS.tsv
PRIOR-ART RECEIPTS       the [source-audit …] lines run, and which records were read
CLAIMS                   [grade; tags] statement — owner. Include every [agent-inferred] decision.
ISSUES                   #n discharged / #m narrowed to <what remains> / NEW: title — labels
OPEN OBLIGATIONS         the concrete absent object, with the existing owners it would compose
NOT RUN                  crate-wide, workspace, device — primary owns these
```

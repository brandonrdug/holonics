# The gate is a release receiver, not an inner loop, and repeated validation became the bottleneck

**Date:** 2026-08-18  
**Kind:** Claude Code conversation-log, test/gate, build-artifact and workflow audit.  
**Truth status:** `established-bounded` for commands, timestamps, counts and filesystem measurements;
`counterexample` for completion reports assembled from incompatible validation scopes; `open` for
test retirement until each candidate has an ownership and consequence audit.  
**Authority:** [`AGENTS.md`](../../AGENTS.md), [`CLAUDE.md`](../../CLAUDE.md), the live roadmap, and
the Phoenix/Gemma blueprints.  
**Primary logs:** Claude sessions `80057f5f-c4fd-4ef5-95cd-b6630a86f537`,
`8433552c-db93-488a-aa68-16b4ea64b0bf`, and `013aea94-513b-462b-9c56-96068441a9d3` under
`/home/b/.claude/projects/-home-b-Workspaces-holonics/`.

---

## 0. Verdict

**Truth status: established-bounded.**

Implementation is the primary bottleneck, but validation policy amplifies it. Claude repeatedly
runs workspace tests, all-target release builds and all gates during ordinary edits; recompiles an
evidence corpus of hundreds of examples; reruns expensive reference faces; regenerates ledgers
during construction; and spends further work explaining dirty-tree failures known in advance.

The first correction is not deleting two thousand tests. It is dependency-aware validation and one
complete release reading.

## 1. The latest Phoenix session

**Truth status: established-bounded, measured from session `80057f5f…`.**

The turn from `2026-08-19T03:28:10Z` to approximately `05:23Z` contains `189` tool-use blocks and
`35` Bash calls whose command text contains `cargo`; a broader command classification identifies
`38` Cargo-related invocations. Five calls mention `tools/gates.sh`.

| epoch | measured wall |
|---|---:|
| complete preflight gate, `03:36:22Z` to `03:38:35Z` | about `2m13s` |
| release all-target builds beginning `04:56:44Z`, `04:58:50Z`, `05:04:34Z` | three invocations |
| final all-target release build plus engine tests, `05:04:34Z` to `05:13:37Z` | about `9m04s` |
| engine test execution inside that epoch | `1,689` passed in `55.66s` |
| complete final gate, `05:13:57Z` to `05:21:18Z` | about `7m21s` |

The complete final gate repeated broad testing after the full engine validation. It returned `8/12`
first: authored levels, driver catalog, closure manifest and architecture lint red. Claude fixed or
regenerated selected cheap inputs and ran selected gates, then wrote an `11/12` complete-gate table
without rerunning the complete sequence. A later independent complete audit did reproduce `11/12`;
the current measurement is real, but the session report spliced two validation scopes.

## 2. The preceding session repeated the workspace suite

**Truth status: established-bounded, measured from session `8433552c…`.**

That session contains twenty-two `cargo test --workspace` invocations. Four overlapping runs during
one repair sequence consumed about `33.4` minutes:

```text
02:21:49Z   391.8 s
03:26:53Z   566.0 s
03:41:36Z   584.8 s
03:52:58Z   463.5 s
```

At JSONL line 3232 one shell command runs `cargo test --workspace` twice sequentially: once to print
failures and again to calculate totals. The gate script already totals one run.

The same session left the active Phoenix line for codec ladders, face quotients, filesystem-path
incidence, supersession controls, Lean/language atlases and an agentic-conversation driver. Claude's
own handoff says five things were built without being requested and were not on the user's
token/emission subject. Those detours enlarged the changed closure and validation burden without
closing the resident Gemma deed.

## 3. Two-day command census

**Truth status: established-bounded.**

Selecting top-level assistant tool-use blocks by local-day UTC bounds and classifying Bash command
text returned:

| local date | tool uses | commands containing `cargo` | commands containing `tools/gates` | workspace-test commands |
|---|---:|---:|---:|---:|
| 2026-08-17 | 1,364 | 289 | 22 | 35 |
| 2026-08-18 | 763 | 286 | 9 | 2 |

These are invocation counts, not cold-build counts: some commands inspect or combine Cargo work.
They establish that Cargo/gate activity has become the session heartbeat.

## 4. Why all-target validation is expensive here

**Truth status: established-bounded, measured 2026-08-18.**

`cargo metadata --no-deps` reports fourteen library test targets, twelve binary test targets, three
integration-test targets, and `244` examples marked `test=false`. The examples are an evidence
corpus, not the unit-test population. Release `--all-targets` nevertheless compiles and links them
under a profile with `lto = true`.

The accumulated apparatus state is:

```text
target/debug              447 GB
target/debug/examples     319 GB; 24,585 files; 1,210 executables
target/debug/incremental   87 GB; 2,141 top-level directories
target/debug/deps          40 GB
target/release             4.8 GB
```

These are rebuildable artifacts, but this audit deletes nothing. Cleanup is destructive, may impose
a cold rebuild, and requires Brandon's separate authorization. The immediate correction is to stop
creating unnecessary target variants.

## 5. The suite is not yet convicted

**Truth status: open for deletion; established-bounded for classification.**

`2,498` tests is not evidence of redundancy. Exact arithmetic guards, controls which deliberately
fire, GPU tests, codec/property tests, persisted-artifact readers, and historical examples can carry
different receiver consequences.

Classify an expensive entry before retirement:

1. owner-local invariant guard;
2. real device/world deed;
3. persisted-artifact or closure consumer;
4. serial/exterior comparison control;
5. redundant replay of another entry's complete consequence; or
6. superseded/dead path.

Only species 5 and 6 are candidates, and each owes a named consequence audit. Current evidence
convicts repeated execution, not the test population.

## 6. Waste taxonomy

**Truth status: established-bounded.**

1. Owner edits trigger workspace tests and all-target builds.
2. The complete gate runs while dirty-tree ledger failure is expected.
3. Package tests precede a full gate which runs the workspace suite again.
4. Hundreds of evidence examples are linked under release LTO for one changed driver.
5. Expensive serial/source comparisons are replayed without a new closure or falsifier.
6. Catalogs/manifests are regenerated before implementation stabilizes.
7. Thousands of lines implement a renamed host interpreter, then tests harden the wrong center.
8. Unrelated codec/filesystem/Lean/conversation work enlarges the active closure.
9. Documents and atlases promote a return while architecture lint remains red.
10. Selected gates plus an earlier complete run are reported as a fresh complete result.

## 7. Binding validation cadence

**Truth status: construction contract.**

### Owner iteration

```text
cargo check -p <affected-package> --lib
cargo test -p <affected-package> --lib <changed-owner-or-module>
bash tools/gates.sh <only named cheap gates whose inputs changed>
```

Compile a changed CUDA kernel and run its focused owner tests. Do not compile every example or run a
workspace suite for a local arithmetic repair.

### Changed-cone verification

```text
cargo test -p <affected-package> --lib
cargo build --release -p <package> --example <one real deed>
<execute that deed once and inspect its artifact>
```

Add dependent packages only when the dependency cone crosses them.

### Receipt reuse

Every expensive deed records command, code/source/configuration/input hashes, apparatus mode,
elapsed time, exit status, artifact address, and falsifier answered. If those identities are
unchanged, inspect the existing receipt. A second execution requires a new falsifier.

### Release reading

After implementation, deed, documents and ledgers agree:

1. regenerate claim/driver/output/closure/authored-level ledgers once;
2. run `bash tools/gates.sh` once;
3. do not run `cargo test --workspace` immediately before it; and
4. if a cheap gate alone fails and no code/kernel/driver/artifact changes, rerun only that named gate
   and report the split scope rather than claiming a new complete reading.

A red architecture gate means rederive or refactor; it is not a documentation task.

## 8. Immediate disposition

**Truth status: open construction requirement.**

For the resident repair: keep focused CUDA/owner tests; do not begin the tower, native rest,
cultivation, export or unrelated codec work; never run release `--all-targets`; build and execute
only the corrected complete-layer deed; run its expensive serial/source comparison once after the
GPU-owned passage is stable; update ledgers once; and take one final complete gate reading.

Validation must illuminate the implementation rather than become a competing workload.

## 9. Gate repairs made with this audit

**Truth status: established-bounded; final timing remains to be measured at the next release
reading.**

- `resolve_line_citations.py` now indexes live files once and prunes `target`, `.git`, `archive` and
  `reference` before traversal. The prior resolver entered the 447-GB target tree once per uncached
  basename and discarded candidates only afterward.
- `closure_manifest.py` now memoizes each file digest and each crate's shared closure population.
  Its rendered digest is unchanged, while fifty-four return rows no longer reread and rehash the
  same crate sources independently.
- the `tests` release gate now runs workspace library/bin/integration tests and type-checks the
  example-driver population with `cargo check --workspace --examples`; it no longer links every
  `test=false` example into the test profile. The real phase deed is still built and executed
  explicitly.
- the operator contracts and `tools/gates.sh` now state that the complete gate is a release receiver
  and forbid full-suite/all-target iteration, scope splicing, and silent build-cache cleaning.

These repairs preserve final acceptance coverage. They do not declare any test deprecated and do
not authorize deletion of the build cache.

# R0 repository census

**Issue:** [#64](https://github.com/brandonrdug/holonics/issues/64). **Baseline:** `925b94b8`
(`main`, September 23, 2026). **Status:** working census; dispositions marked unresolved below
are not deletion authorization. The [restructure plan](THE_REPOSITORY_RESTRUCTURE.md#0-final-decisions)
governs keep, fold and retirement decisions. Its object/operation consumers, including a
standalone checked Lean theorem, take precedence over a static reference count.

## Snapshot before retirement

| Area | Baseline observation | Treatment |
|---|---|---|
| Root Cargo workspace | 16 library-directory members and three application packages | Rust owner/consumer census before R1–R2 |
| Lean | `ElementaryHolonics.Framework` is the curated entry; §0.10 identifies the research-import edges | Import closure and theorem/consumer census before R3 |
| Documents and records | At baseline: 99 tracked `docs/` files, 1,600 tracked `research/records/` files and 2,260 tracked `archive/` files; five captured records bring the middle count to 1,605 | [Document/record table](census/DOCS_R0.tsv); incoming links are leads, not a uniqueness test |
| Main working tree | Eight modified tracked files and 56 untracked status entries at baseline: 18 `formal/`, 44 `research/`, `.opencode/`, `.vscode/` | Commit or account for the authored Lean/research work before retirement. The two editor/session directories remain local and are excluded from source commits. |
| Worktrees | [Exact inventory](census/WORKTREES_R0.tsv): 19 worktrees including this checkout. The three paused WIP branches (`-11` `72eac4a5`, `-12a` `0ee4ea6d`, `-12b` `eda4ed3b`) report clean. Eight other detached evidence/baseline worktrees report 227 dirty tracked entries at their own HEADs; 19 untracked status entries appear across all worktrees, including this checkout. | Preserve every worktree. The detached diffs and untracked paths require a source/landed-change audit before any cleanup; the WIP branches rebase and complete in campaign C after R1–R4. |
| Generated/local storage | Root `target/` 216 GiB; `.local/` 221 GiB (including local datasets, artifacts, campaign checkpoints and WIP worktrees) | Neither is tracked source. Preserve local evidence and WIP; inspect target ownership before reclaiming build output. |

The dirty-source set was the September 22–23 Lean/RH/Millennium/Computation and research work
identified in the restructure plan. It is now captured in four explicit-path commits on
`codex/restructure-r0`: `4700a7c9` (zero navigation), `9921adfa` (Weil/reflected-zero),
`b3bae071` (exterior/Hodge-fluid) and `d17910d3` (figures and indexes). Focused Lean owners
and both experiment receipt verifiers passed; all 17 SVG plates reproduced byte-for-byte
from the four Typst sources. The 17 PNG renditions match the plates, but their exact
rasterizer settings are undocumented. They are documented supplementary figures, not pages
of the categorical paper's current `main.typ`. `.opencode/` contains local session state;
`.vscode/` is local editor configuration. Neither was staged as research source.

## Area tables

| Area | Working table | Current limit |
|---|---|---|
| Rust owners, examples, applications and accelerators | [Rust R0](census/RUST_R0.tsv): 1,825 tracked Rust/CUDA source paths; [Soma/R2 owner audit](census/SOMA_R0.tsv) | Current static caller signals and historical cohorts are leads. Module references and in-repo callers must be checked through re-exports and target builds. |
| Lean modules and foundation import closure | [Lean R0](census/LEAN_R0.tsv): 1,399 package modules plus three top-level roots | Import count cannot retire a distinct theorem or source-specific research result. Focused Core, Ratio and MomentStorage targets pass at the captured worktree. |
| Documents, records and archive | [Docs R0](census/DOCS_R0.tsv), [Archive R0](census/ARCHIVE_R0.tsv), [archived plans](census/ARCHIVE_PLANS_R0.tsv), [small archive trees](census/ARCHIVE_SMALL_R0.tsv) | Static live inbound links only. An uncited record may be the sole statement of a result; an archive citation needs a revision replacement before removal. |
| Issues | [Issue R0 table](census/ISSUES_R0.tsv): 76 issues (34 open, 42 closed) | Claude completed the issue reset at `925b94b8`; §5 of the restructure plan lists the object/retirement dispositions and #63–#76 tracking. Historical closed issues outside that map keep their issue-body context. |

The first claim-level record audit is [RECORDS_EARLY_R0.tsv](census/RECORDS_EARLY_R0.tsv):
the oldest 60 zero-inbound Markdown records (July 10–16) were read against their own regrades
and later owners. It classifies 40 **keep** (distinct result/provenance), 16 **fold** (named
superseding guide/record, still requiring the actual transfer before removal), and four
**unresolved** (authority or claim provenance insufficient). No record was deleted from this
classification. Static inbound count selected the cohort; content and source status decided it.
The [next 60](census/RECORDS_NEXT_R0.tsv) (July 16–20) add 38 **keep** and 22 **fold**;
the first safe folds still require source-specific guide transfers. Cited archived measured
receipts caused two provisional fold decisions to become keep decisions. Across both cohorts,
78 distinct records are kept, 38 have a named fold target, and four remain unresolved.
The [third cohort](census/RECORDS_THIRD_R0.tsv) (July 21–27) adds 52 **keep** and eight
**fold**, after checking two cited archived experiment receipts. Across the 180 audited
zero-inbound records: 130 keep, 46 fold only after their named owner transfer, four unresolved.
The [fourth cohort](census/RECORDS_FOURTH_R0.tsv) (July 28–August 14) adds 53 **keep**,
five **fold** and two **unresolved**. One fold explicitly retains a July 28 falsification:
the five-image and 200-image prediction outputs were byte-identical. Across 240 audited
zero-inbound records: 183 keep, 51 fold only after their named owner transfer, six unresolved.

The document table records paths, line counts, live incoming source count and a conservative
working disposition. Its scan recognizes Markdown links and explicit path strings in common
source/doc text; it does not cover every JSON manifest or free-form relative citation. The
archive audit found both kinds of false negative. Its `unresolved_*` entries require content
and owner review. At the
captured `d17910d3` scan, 575 of 1,248 Markdown research records had no live incoming link;
this is a **review queue**, not a retirement verdict. The Rust table covers every tracked
source path, but its per-file static mentions are not build confirmation. Historical 41/40
engine-module cohorts at `c9012f17` are marked as stale candidates rather than current
decisions. The Lean table records current direct imports/reverse consumers; the captured
`Framework` closure is 543 modules / 191,153 lines, including 294 Millennium and 64 RH
modules. It is larger than the §0.10 snapshot because the captured September 23 work adds
imports.

The [archive audit](census/ARCHIVE_R0.tsv) groups all 2,260 tracked archive files by
top-level subtree. `archive/cpp-engine` has 1,652 files and holds measured observation
receipts still cited by live guides/records. A July 16 current-contact receipt was a textual
relative reference that the mechanical inbound-link count missed. Keep those receipts until
their results and immutable Git coordinates replace the live citations. A narrower CMake
harness candidate (77 files / 6,167 lines) may retire after the one live `HolonicDeposit.cmake`
source-coordinate citation in `holonic-life/driver-sources/.../SOURCE.json` is rewritten to
its immutable revision. This is not a license to delete the archive subtree wholesale.
The 73 archived plans have 208 live inbound sources across 45 linked paths. Their
[per-plan audit](census/ARCHIVE_PLANS_R0.tsv) identifies two possible unique live-definition
contracts, eight duplicate historical schedules and 63 unresolved plans pending context.
The first fold candidate, `legacy/REALIZATION_AND_HARDWARE.md`, requires its decoded parity,
boundary/lineage, resource and rest/remount admission clauses in the current device and
hardware guides before its historical citation is replaced. No archived plan was removed.
The [five smaller archive-tree audit](census/ARCHIVE_SMALL_R0.tsv) covers 68 files and
33 inbound sources. It found live equation-atlas JSON fixtures consumed by Rust examples,
a tooling script used as source data, and unique measured/experiment receipts. None of those
can be removed merely because they live under `archive/`. The first narrow fold candidate is
`archive/tooling/README.md`: replace its one `tools/README.md` link with the current repository
guide and an immutable revision coordinate, then retire only that README.

The first eight historical “zero-reference” engine modules were inspected at current source:
`mode`, `observation_ecology`, `prime_ecology`, `local_star`, `field_atlas`,
`causal_state_grammar`, `organizational_grammar`, `divisor_reconstruction`. All have actual
Rust consumers or a distinct unported law; the Rust table marks them **keep** candidates with
their callers/target owners. The old module-token metric missed type-level and re-exported
API use. No deletion follows from the historical zero count.
The next eight have seven **keep** decisions for the same source-backed reason
(`receiver_phase_atlas`, `coupled_informant`, `wave_propagation`, `atmospheric_inverse`,
`causal_traversal`, `holonic_complex`, `physical`). `generative_transport` is a **fold**
candidate with only a standalone prediction example as executable consumer, but its exact
enrichment/prediction/return law must first be stated in `HNN_FORMULA` or assigned a formal
obligation. Its module and example cannot yet be deleted.
The third eight add four **keep** (`graph_receiver`, `dimensional_receiver`,
`arithmetic_dimensional`, `receiver_ecology`), two **unresolved** (`arithmetic_phase` has an
uncopied prime-square/affine-orbit law; `returned_conduct` still has a `life` runtime caller),
and two proposed **retire** (`acoustic_receiver`, `artifact_release`). An independent review
confirmed no external Rust caller/example and a checked Lean counterpart for each.
`acoustic_receiver` is ready for a coordinated R1 source, re-export, citation and guide cut.
`artifact_release` also has Rust-only `EnclosedFamily` representation and work-ceiling policy:
classify these as implementation-specific retirement or preserve a distinct law in a guide/
#62 before removing it. Both cuts still need focused Rust/Lean checks after the edit.

The [R2 owner audit](census/SOMA_R0.tsv) changes two earlier assumptions. `holonics-workspace`
has a live workbench application caller, and `holonic-language`'s generic reflective
continuation law lacks a clearly equivalent Lean owner; move that law before retiring its
Rust crate. `accelerators/cuda-kernel`'s PTX is embedded by `holonic-mount` library/tests/gates
and loaded by an engine section-layout test as well as by `life`; removing `life` alone cannot
retire the Rust device kernel or `holonic-words`. The plan §0.4 now names those consumers.

## First source-backed cuts to verify

| Step | Candidate and source evidence | Required check before retirement |
|---|---|---|
| R1 | `crates/holonic-engine/src/platform_x11.rs`: `x11rb` implementation use is confined there and `lib.rs` gates its export behind default `desktop-x11`. **Type-level callers exist:** `examples/arithmetic_dimensional_receiver.rs` and `examples/desktop_receiver.rs` construct `X11Platform`. The governing plan §0.5 retires the feature, but the first static module-token scan missed these callers. | Decide each example's mathematical/saved-output disposition, then remove or rechart its X11 use in the same cut as the module, feature and dependency. Run targeted engine and all-target checks. The cut is not yet licensed by an absence-of-consumers claim. |
| R1 | `generative_transport.rs` has one standalone prediction example; current source carries an exact `A(τ)=M+τ(S+K+R)` enrichment and prediction/grade-before-return law without an exact Lean counterpart. | Preserve that law in `HNN_FORMULA` or a named #62 proposition, verify its source/receiver scope, then retire the module and example together if no other caller remains. An isolated zero-token census is insufficient. |
| R1 | `acoustic_receiver.rs` has no external Rust caller/example and maps its resonator/Cayley/causality/energy laws to checked `Foundation/AcousticReceiver.lean`; its WAV/export and ceilings are unconsumed boundary behavior. `artifact_release.rs` is similarly unconsumed and maps its release/tube laws to `Transport/ArtifactRelease.lean`, with a Rust-only coordinate-product representation and work ceilings. | Acoustic: retire Rust module/tests and public declaration, update `lean_citations`, architecture map, Lean comments and receiver guide; preserve the theorem and historical measurements. Artifact: first classify or preserve `EnclosedFamily` and ceiling policy, then make the same coordinated source/citation/guide cut including `edit_rigidity` comments/tests. Verify focused engine and Lean targets plus all-target callers. |
| R3 | `Framework.Core` reaches five historically filed Millennium owners **transitively** through Standing/RelationLadder/ContinuingTower and CausalRelevance/JointReceiverDescent. `Objects.Ratio → HolonicGaugeCovariance → HolonicConnectionVariation` and `Holon.MomentStorage → HolonicQuadraticMomentCondensation → HolonicGranularBoundaryRadiation` are the other large ingress paths. | Extract only the declarations the foundation consumes, retain unique research theorems and update their source importers in the same cut. Focused Core, Ratio and MomentStorage builds pass before the edit; build the affected targets again afterward. |

The candidate rows do not authorize the next cut before the remaining area dispositions and
their consumers are accounted for. R1–R3 issue closure needs changed-source checks and a
verification receipt, not only this census.

The detached-worktree audit is in [WORKTREE_DIRTY_R0.tsv](census/WORKTREE_DIRTY_R0.tsv).
Its grouped source/hash comparison found no uncaptured Rust source: p13/p15/p16 and verify
snapshots match the current source or landed phase commits; reaction/p8a are earlier drafts
of the current Cayley law. Seven unique untracked Rust paths across those worktrees likewise
match current source or an earlier landed draft. **One evidence difference survives:** three
detailed phase-8a verification rows in `.local/p8a-wt` contained test breakdown, exact balance/
residual and performance/checkpoint readings not fully preserved in the main receipt. Those
three rows have now been transferred verbatim to `docs/VERIFICATION_RECEIPTS.tsv`. No local
worktree was cleaned. The large `.local/` size includes these source worktrees and private
data, so a clean status in the three paused branches alone was never a cleanup license.
The two additional untracked examples in detached review worktrees are also accounted for:
`normal_geometry_review.rs` is a strict subset of current tracked source and
`four_torus_current.rs` is byte-identical to current source. Thus the 19 registered worktrees
contain no known unique uncaptured source or receipt after this audit, while their local
checkouts remain preserved.

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
| Documents, records and archive | [Docs R0](census/DOCS_R0.tsv), [Archive R0](census/ARCHIVE_R0.tsv), [archived plans](census/ARCHIVE_PLANS_R0.tsv), [small archive trees](census/ARCHIVE_SMALL_R0.tsv), [reference snapshots](census/ARCHIVE_REFERENCE_R0.tsv) | Static live inbound links only. An uncited record may be the sole statement of a result; an archive citation needs a revision replacement before removal. |
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
The [fifth cohort](census/RECORDS_FIFTH_R0.tsv) (August 14–21) adds 58 **keep** and two
**fold**: unexecuted Lean-audit and pre-restructure rebase plans whose current owners are
the R3 census and restructure/roadmap. Across 300 audited records: 241 keep, 53 fold only
after owner transfer, six unresolved. Corrected interpretations did not erase unique
checked theorems, experiments or their falsifiers.
The [sixth cohort](census/RECORDS_SIXTH_R0.tsv) (August 21–23) adds 57 **keep**
and three **fold** candidates: two superseded research schedules and one umbrella
inference definition. Across 360 audited records: 298 keep, 56 fold only after
owner transfer, six unresolved. The GeneralHalving theorem and distinct formal
owners cited by those schedules remain in their Lean sources.
The [seventh cohort](census/RECORDS_SEVENTH_R0.tsv) (August 23–26) adds 60 **keep**:
the records retain distinct formal returns, admission stages, measured failures and corrections,
or L3–L6 receipts. Across 420 audited records: 358 keep, 56 fold only after owner transfer,
six unresolved. Row 370's Athena admission interpretation was withdrawn by its own
counterexample, but its measured source and apparatus receipts remain evidence; retain the
record and transfer only that corrected interpretation.
The [eighth cohort](census/RECORDS_EIGHTH_R0.tsv) (August 26–September 1) adds 58 **keep**,
one **fold** candidate and one **unresolved**. Across 480 audited records: 416 keep, 57 fold
only after owner transfer, seven unresolved. The fold is an architecture comparison whose Lean
theorem owners stay; its exact theorem names and hypotheses must reach `HNN_FORMULA` before the
narrative is retired. The unresolved intrinsic-profile proposal needs a field-by-field map to
the finalized Holon, Receiver and Holarchy contracts.
The [ninth cohort](census/RECORDS_NINTH_R0.tsv) (September 1–3) adds 60 **keep**.
Across 540 audited records: 476 keep, 57 fold only after owner transfer, seven unresolved.
The cohort includes distinct shell/analysis proofs, HNA negative controls and staged releases;
DB0 retains its unique de Bruijn source and owner map even though later records prove some steps.
The [tenth and final cohort](census/RECORDS_TENTH_R0.tsv) (September 3–20) adds 33 **keep**
and two **fold** candidates. All 575 zero-inbound Markdown records in the captured R0 scan
now have a source-reviewed claim disposition: 509 keep, 59 fold only after named owner transfer,
seven unresolved. The final two folds are HNP receipt README summaries; their measured JSON
receipts remain. This completes the record review queue, not the archive/document or Rust/Lean
census gates.

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
The [reference-snapshot audit](census/ARCHIVE_REFERENCE_R0.tsv) covers 345 tracked files,
26 inbound sources across 13 linked paths, and dynamic corpus readers missed by the link
scan. Holobrochos and pureholonics source trees remain live fixtures; 132 engine-snapshot
files lack a current byte match and remain unresolved. `archive/reference/README.md` is a
narrow fold candidate only after its source map reaches `docs/REPOSITORY.md` and the two
`THE_HOLOBROCHOS_SPINE.md` citations are replaced with current guide and immutable-source
coordinates. Four ignored local transcript files were observed and left untouched.

The first eight historical “zero-reference” engine modules were inspected at current source:
`mode`, `observation_ecology`, `prime_ecology`, `local_star`, `field_atlas`,
`causal_state_grammar`, `organizational_grammar`, `divisor_reconstruction`. All have actual
Rust consumers or a distinct unported law; the Rust table marks them **keep** candidates with
their callers/target owners. The old module-token metric missed type-level and re-exported
API use. No deletion follows from the historical zero count.
The next eight have seven **keep** decisions for the same source-backed reason
(`receiver_phase_atlas`, `coupled_informant`, `wave_propagation`, `atmospheric_inverse`,
`causal_traversal`, `holonic_complex`, `physical`). `generative_transport` has since been
retired in R1 with its sole standalone prediction example and public re-export. Its bounded
time-affine family law now has a concise entry in `HNN_FORMULA`, a formal kernel theorem in
`Transport/GenerativeTransport.lean`, and source evidence in the July 27 research record. No
general algorithm theorem was added.
The third eight add four **keep** (`graph_receiver`, `dimensional_receiver`,
`arithmetic_dimensional`, `receiver_ecology`), two **unresolved** (`arithmetic_phase` has an
uncopied prime-square/affine-orbit law; `returned_conduct` still has a `life` runtime caller),
and two proposed **retire** (`acoustic_receiver`, `artifact_release`). An independent review
confirmed no external Rust caller/example and a checked Lean counterpart for each. The acoustic
mirror and the T3 artifact Rust mirror have both been retired in isolated R1 cuts (#65). The
acoustic Cayley/receiver law and dated measurements remain with its checked Lean owner; the
distinct native Athena acoustic chart remains live. The T3 product-family law and receiver
release criterion now have checked Lean owners, while Rust work ceilings remain historical
implementation evidence; the distinct live `edit_rigidity` chart remains. Focused engine,
Lean-owner, workspace all-target and Lean-citation checks passed for both cuts.

The independent R1 live-presentation review found no crate, example, or test caller for
`live_presentation.rs`; its root module/re-export and inline reachability test were its only Rust
references. The `LiveCpuPresenter` checked generation freshness only when dequeuing a tile, then
could return a stale completion after a newer generation arrived. It exposed each tile completion
directly and had no complete-face assembly or publication barrier, despite its atomic-face module
comment. The transferable tile scheduling constraint is now in the hardware guide, explicitly as
implementation policy. The prototype and inline test are retired; this does not claim an atomic
whole-face implementation or a missing Lean theorem.

The [R2 owner audit](census/SOMA_R0.tsv) changes two earlier assumptions. `holonics-workspace`
has a live workbench application caller. `holonic-language`'s source-neutral reflection and
continuation law now has checked `Transport/ReflectiveContinuation.lean`; its Rust crate remains
live through `holonic-life` and needs the caller disposition before retirement. The
[device and exact-word audit](census/R2_DEVICE_WORDS.md) establishes that
`holonic-core::PrimeChart` consumes `holonic-words`, while the Rust NVPTX kernel consumes
`soma-abi` directly; the latter owns the shared `no_std` arithmetic. The Soma PTX is embedded at
compile time by `holonic-mount` library/tests/gates and loaded as bytes by the engine's
section-layout test and `life` callers. Removing `life` alone cannot retire the kernel, mount
consumer or host words. The plan §0.4 now names those distinct edges.

The R2 provenance check retired `holonics-circulation-abi`: it is `publish = false`, has no
configured install/build consumer, C header or foreign-language caller in tracked source, and no
`libholonics_circulation_abi*` artifact or exported-symbol/schema reference was found in the
filename-level `.local` artifact scan. The HNA `alpha_matrix` had one ABI-specific equality check:
`Open` + `Conduct` returned the same complete boundary as direct
`NativeCirculationSession::conduct` for the same package, configuration and request, then `Close`
released the process handle. The HNA integration also directly tests the lifecycle, remount,
commit, decline and diffusion paths; those laws and tests remain with `life`, `holonic-engine` and
Lean. The adapter's JSON schema, opaque handle registry, refusal mapping and C buffer ownership
were transport apparatus, not a distinct mathematical law. No positive external consumer evidence
was found in the repository, local artifacts, or GitHub releases/packages; unrecorded user-local
dynamic loading cannot be ruled out. The surviving HNA `alpha_matrix` integration test and the
locked workspace all-target check passed after the ABI edge was removed.

The unconsumed wgpu `holonic-surface` crate and its orphan rust-gpu SPIR-V source, builder and
artifact have been retired in R2 after a source/manifest scan found no external caller. The
M4/M5 measured claims remain in dated research records; old SLEEP readers and fixtures do not
carry forward under §0.2. Cargo pruned the lockfile to 182 packages after the earlier X11 cut;
the workspace all-target and locked-lockfile checks passed. The live CUDA PTX path remains.
The [membrane caller map](census/R2_MEMBRANE_EDGE.md) keeps the live receive/standing runtime
with its `life` and CUDA consumers until the main-library move; the ERST plate reader and its
deed adapter have now been retired, with the runtime rest-image codec retained. The direct
live-current carrier test, complete plate suite and locked workspace target gate passed.
Two test-only ranked/sparse felt-surface wrappers also retired; their opposed-arm, narrowing and
ranked/sparse parity witnesses now run against `SparseOwnState` and `GrowingRankedOwn` in the live
body/membrane owners. The surviving 56 membrane tests and locked workspace gate passed; live
`SparseStandingSurface` and `live_current` remain untouched.
The redundant `soma-membrane::CausalMembrane` re-export also retired; `AgenticLanguageEcology`
now names the existing `holonic-structure` trait owner directly. The 17 focused agentic-language
tests and locked workspace target check passed without moving the live membrane runtime.
The [workspace caller map](census/R2_WORKSPACE_EDGE.md) places the
live variant-workspace operation at the workbench boundary and names its v1 persisted readers;
those readers cannot become compatibility paths in the new library. Both are migration
obligations, not evidence that the crates are currently unconsumed.
The [native-intelligence caller map](census/R2_LIFE_NATIVE_EDGE.md) identifies a first M1 law
slice: `holonic-engine::diffusion::ExactDiffusionLaw` moves to main
`holonics::physics::diffusion`, while Soma incidence/session adapters remain at the HNA boundary.
Situated actual-successor inference belongs to core HNN and resident addressed-junction conduct
to `holonics-cuda`; snapshot/artifact reader formats remain unresolved until their current
producers and consumers are classified. No `life::native_intelligence` module moves merely
because it is re-exported by that facade.

## First source-backed cuts to verify

| Step | Candidate and source evidence | Required check before retirement |
|---|---|---|
| R1 complete (#65) | `platform_x11.rs` was the only x11rb implementation and `lib.rs` cfg-gated its export. Both type-level callers are retained and recharted: `arithmetic_dimensional_receiver` uses `MemoryPlatform` after its existing headless snapshot path; `desktop_receiver` uses `MemoryPlatform` for one scripted local-star traversal and retains its TSV trace schema. | Retired the X11 source/module/re-export, default feature and x11rb dependency with both example edits. The no-default engine and workspace all-target checks, platform/display tests, and headless/scripted example receipts passed. The source compositions remain; only the X11 input/display adapter retired. |
| R1 complete (#65) | `generative_transport.rs` had one standalone prediction example and no other Rust consumer. Its bounded exact family/prediction law was transferred to `HNN_FORMULA`, a kernel theorem to `Transport/GenerativeTransport.lean`, and its single implicit receiver scope to the July 27 research record. | Retired the module, example and root exports together. Focused engine, Lean and workspace all-target gates passed; no general algorithm theorem is claimed. |
| R1 complete (#65) | `acoustic_receiver.rs` had no external Rust caller/example and maps its resonator/Cayley/causality/energy laws to checked `Foundation/AcousticReceiver.lean`; its WAV/export and ceilings are historical boundary behavior. | Retired its Rust module/tests, root declaration and citation row; retained the formal law, dated measurements and distinct native Athena acoustic chart. Focused engine, Lean, all-target and citation gates passed. |
| R1 complete (#65) | `artifact_release.rs` had no external Rust caller/example; its checked T3 mathematics, including the formerly Rust-only product enclosure specialization and numeric policy distinction, now resides in `Transport/ArtifactRelease.lean` and the T3 guide. | Retired the Rust module/tests, root export and `lean_citations` row. Focused engine, Lean, all-target and citation gates passed; the distinct live `edit_rigidity` chart remains. |
| R1 complete (#65) | `bridge.rs` had no Rust caller beyond its own tests and root export. `Foundation/Bridge.lean` owns status entailment/meet, passage composition, promotion blockers and the protein embedding counterexample; the C7 guide retains their scope. | Retired the Rust mirror/tests, root declaration and citation row. Focused engine, Lean, all-target and citation gates passed; no bridge law or counterexample was removed. |
| R1 complete (#65) | `device.rs` had no Rust caller beyond its inline tests and root exports. Its generic CPU-only three-task parity experiment had no resident HNN consumer or distinct Lean law. | Retired the module and exports. The hardware guide retains its exact ordered-result/cardinality admission criterion and explicitly limits that evidence; focused engine and combined all-target gates passed. |
| R1 complete (#65) | `parameter.rs` had no exact-symbol Rust consumer beyond inline tests and root exports. Its copy, retention, departure and return-at-event-closure conditions are now stated in the elementary-object contract as conditions on Holon relations, with `StandingLaw` owning future sufficiency. | Retired the standalone carrier and exports; ID/schema/map/error policy remains historical implementation evidence. The workspace all-target gate passed. |
| R1 complete (#65) | `model_surface.rs` had no Rust consumer beyond its own tests; `holonic-body::arrow` carried only an explanatory comment. Its rational reading and Arrow relation are retained in [the realizer guide](../canon/TABLET_THE_REALIZER.md#143-the-holomorphic-half-is-owned-and-it-is-aperture-complete-by-a-theorem), with the prototype's finite-decade and asymmetric-crossing limits named. | Retired the module/tests and root export; Arrow computes its classification directly. No current Rust API or Lean theorem is claimed; the workspace all-target gate passed. |
| R1 complete (#65) | `live_presentation.rs` had no crate/example/test caller beyond its root module/re-export and inline reachability test. Its tile worker checked freshness only at dequeue, returned individual completions, and never assembled/committed a complete face; `ReceiverCouplingSet` was unused directed-graph reachability. | Retired the Rust module, inline test and root exports. The hardware guide retains tile partition and whole-face publication as an implementation policy that the prototype did not enforce; the workspace all-target gate passed. |
| R3 | `Framework.Core` reaches five historically filed Millennium owners **transitively** through Standing/RelationLadder/ContinuingTower and CausalRelevance/JointReceiverDescent. The [declaration-level edge audit](census/LEAN_CORE_R3_EDGES.md) names each consumer and research remainder. `Objects.Ratio → HolonicGaugeCovariance → HolonicConnectionVariation` and `Holon.MomentStorage → HolonicQuadraticMomentCondensation → HolonicGranularBoundaryRadiation` are the other large ingress paths. | Extract only the declarations the foundation consumes, retain unique research theorems and update their source importers in the same cut. Focused Core, Ratio and MomentStorage builds pass before the edit; build the affected targets again afterward. |

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

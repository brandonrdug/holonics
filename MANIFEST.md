# Leftovers archive — 2026-09-24

One orphan branch holding everything from the September restructure's agent worktrees and branches that was **not already in `main`'s history**, so the worktrees and branches could be removed. Workers: Brandon, Claude, Codex.

- Reference: `origin/main` = `bb73054a7e1be943f8d7987c4979448e643ce4b3` ("Reset the repository to what functions"); `13f8c734` is the last pre-reset tree and is in that history.
- A worktree or branch marked `in main` had a HEAD that is an ancestor of `origin/main` (`git merge-base --is-ancestor`) and no uncommitted or untracked files.
- "Not in main" below means the exact file content (blob id) occurs nowhere in `origin/main`'s history, at any path.

## Layout and restoring

| Path | Contents | Restore |
|---|---|---|
| `worktrees/<name>/diff.patch` | `git diff HEAD --binary` of a dirty worktree (staged + unstaged) | `git switch --detach <HEAD>` then `git apply --index diff.patch` |
| `worktrees/<name>/untracked/` | untracked, non-ignored files (build outputs and files > 5 MB skipped) | copy back |
| `worktrees/<name>/status.txt` | path, branch, HEAD, porcelain status, untracked list | — |
| `branches/<branch>/*.patch` | `git format-patch origin/main..<branch>` (merge commits omitted) | `git am` |
| `branches/<branch>/branch.bundle` | exact commits, including merges | `git fetch branch.bundle '<ref>:refs/heads/<name>'` (ref in README.txt) |
| `stashes/stashes.bundle` | the five `refs/stash` entries as exact commits | see `stashes/README.txt` |

Every `diff.patch` was checked with `git apply --cached --check` against its HEAD, and every bundle with `git bundle verify`, before the worktrees were removed.

## Content that never landed in main

No uncommitted or unmerged **Lean** file exists in any worktree or branch. The substantive never-landed material is:

1. **`branches/codex/apple-silicon/`** — Brandon's Apple-silicon/Metal port (27 commits, 9 merges, Sep 6–7; merge-base `e577d9b3`): 265 of 266 changed files are not in main, including `accelerators/metal/` (17 files), `docs/plans/HOLONICS_ON_APPLE_SILICON.md`, `docs/ACOUSTIC_EXPERIMENTS.md`, and 23 research records with their data directories:
   - `research/records/2026-09-06_ACOUSTIC_HOLONS_ARE_NOT_PCM_SAMPLE_STEPS.md`
   - `research/records/2026-09-06_APPLE_ACOUSTIC_FIELDS_AND_HOLONIC_PROFILING.md`
   - `research/records/2026-09-06_APPLE_NATIVE_PHASE_AND_ACOUSTIC_COMPOSITION.md`
   - `research/records/2026-09-06_APPLE_SILICON_SPECIFICATION_AND_MAC_SETUP.md`
   - `research/records/2026-09-06_AS4_AS5_CORPUS_CONTINUATION_AND_RESIDENT_PACKETS.md`
   - `research/records/2026-09-06_AUDIO_APPLICATION_PROBES_DO_NOT_COMPLETE_CONVERSATIONAL_AUDIO.md`
   - `research/records/2026-09-07_ACOUSTIC_SECTIONS_ENTER_THE_SHARED_RESIDENT_CURRENT_PORT.md`
   - `research/records/2026-09-07_APPLE_CONDUCTS_COMPLETE_RECORDINGS_AND_RETURNS_TIMED_AUDIO.md`
   - `research/records/2026-09-07_APPLE_CONDUCTS_THE_SHARED_CONDITION_FAMILY.md`
   - `research/records/2026-09-07_APPLE_CONTINUES_GENERATED_CURRENTS_THROUGH_THE_COMPLETE_JUNCTION.md`
   - `research/records/2026-09-07_APPLE_INTEGRATES_THE_SHARED_CONDITIONAL_GENERATOR_HANDOFF.md`
   - `research/records/2026-09-07_APPLE_LEARNS_THE_SHARED_CONDITIONAL_PHASE_ACTION.md`
   - `research/records/2026-09-07_APPLE_RETAINS_CONDITION_CURRENT_THROUGH_RECORDED_CONTACT.md`
   - `research/records/2026-09-07_APPLE_RETURNS_COMPLETE_MATERIAL_CURRENT_TO_THE_TEMPORAL_RECEIVER.md`
   - `research/records/2026-09-07_APPLE_RETURNS_THE_INTERNAL_CURRENT_AND_SHARED_DRIVE_MODE.md`
   - `research/records/2026-09-07_APPLE_RETURNS_THE_SHARED_CONDITION_PREIMAGE_FIBRE.md`
   - `research/records/2026-09-07_MEASURED_ACOUSTIC_RETURNS_KEEP_THEIR_ORIENTED_DIFFERENCE.md`
   - `research/records/2026-09-07_RECORDED_RESPONSE_POINTERS_RETAIN_THEIR_ACOUSTIC_INTERVALS.md`
   - `research/records/2026-09-07_THE_NATIVE_TEMPORAL_ACTION_RETAINS_ITS_CAUSAL_TAIL.md`
   - `research/records/2026-09-07_THE_RECORDED_CONDITIONAL_ACTION_CONTINUES_AFTER_RESTART.md`
   - `research/records/2026-09-07_THE_RECORDED_PREIMAGE_FIBRE_CHANGES_THE_CONTINUING_TEMPORAL_RESPONSE.md`
   - `research/records/2026-09-07_THE_RECORDED_RETURN_USES_ITS_PRODUCING_TEMPORAL_ADJOINT.md`
   - `research/records/2026-09-07_THE_TEMPORAL_RESPONSE_RESTARTS_AND_RETURNS_ENCLOSED_SOUND.md`

2. **`branches/quarantine/station-e-predecessor/`** — pre-single-card Station E material (`native_law.rs`, `native_occurrence.rs`, athena_walk/athena_future kernels), quarantined 2026-08-19.
3. **`branches/wip/consolidation-phase-{11,12a,12b}/`** — paused, unverified WIP snapshots. Nearly all of their files later landed; not in main: the phase-11 plan-doc text, `holonics-hna/src/native/field_session.rs` and `field_session/native_source.rs` (12a), and three `direct/wave/{coupled,coupled/comparison/constitutive,rest}.rs` variants (12b).
4. **Census edits**: `branches/codex/restructure-r3-origin-dim/` (`docs/plans/census/LEAN_CORE_R3_EDGES.md`), `branches/codex/c-phase12a-integration/` plus `worktrees/c-phase12a-integration/diff.patch` (`docs/plans/census/C_PHASE12A_INTEGRATION.md`).
5. **Uncommitted worktree text**: `worktrees/p15-head/diff.patch` (plan-doc section "Phase 15 disposition: the extracted operator is one Holon"), `worktrees/p8a-wt/diff.patch` (a `field.rs` variant and three phase-8a Cayley reaction receipts for `docs/VERIFICATION_RECEIPTS.tsv`), `worktrees/p15-base/` (earlier `holonic_intelligence.rs` and `extraction_equality_tests.rs`). All other dirty worktree content already exists in main by exact content.
6. **`stashes/stashes.bundle`** — five stashes from Aug 30–Sep 1 made on the old `soma/` layout. They contain 165 Lean files not in main by content; 146 of their file names never appear in main's history, and 144 of those are `soma/formal/elementary-holonics/Scratch/*.lean` probes (the others: `Main.lean`, `ScratchFaceInjective.lean`). Stash 4 also holds 11 `research/records/2026-08-26_curl_filter/` scripts. The `refs/stash` entries themselves were left in the repository untouched.

## Worktrees (97, all removed; main checkout excluded)

| Worktree (`.local/…`) | Branch | HEAD | Ancestor | Dirty / untracked | What it was | Disposition |
|---|---|---|---|---|---|---|
| `audit-bisect` | detached | `3b2acef7` | yes | — | Audit checkout: Pin facade dependency receipts after Geometry rebase | in main |
| `audit-main` | detached | `925b94b8` | yes | — | Audit checkout: Record the GitHub issue reset and the restructure tracking issues | in main |
| `c-phase12a-current` | `codex/c-phase12a-current-cut` | `939fe650` | yes | — | Consolidation phase 12a: Pin phase 12a current-format verification receipts | in main |
| `c-phase12a-integration` | `codex/c-phase12a-integration` | `75d357d6` | **no** | 1 / 0 | Census map of phase-12a integration onto phase 11 (#68); uncommitted 9-line edit to the census doc | archived: worktrees/c-phase12a-integration/; archived: branches/codex/c-phase12a-integration/ |
| `c-phase12b-archive` | `codex/consolidation-phase12b-archive` | `68d3183f` | yes | — | Consolidation phase 12b: Correct final Phase12b all-target receipt | in main |
| `c-phase12b-grammar-rest` | `codex/consolidation-phase12b-grammar-rest` | `45d13d64` | yes | — | Consolidation phase 12b: Record organizational rest refusal gate | in main |
| `c-phase12b-session` | `codex/consolidation-phase12b-session` | `a1cfbfca` | yes | — | Consolidation phase 12b: Record coupled session format retirement gates (Refs #68) | in main |
| `claude-audit-tip` | detached | `9580479e` | yes | — | Audit checkout: Move affine swing laws into Geometry (Refs #70) | in main |
| `k1-holarchy-contract` | `codex/restructure-k1-holarchy-contract` | `e64688bc` | yes | — | K1 construction campaign: Clarify K1 Holarchy contract | in main |
| `lessons` | `restructure/lessons` | `1b8588ec` | yes | — | Record lessons from the workbench and Athena prototypes before retirement | in main |
| `m1-abi-retire` | `codex/restructure-m1-abi-retire` | `49537dad` | yes | — | M1 restructure packet: Record ABI retirement workspace gate | in main |
| `m1-action` | `codex/restructure-m1-action` | `de1502b6` | yes | — | M1 restructure packet: Record action owner verification gates | in main |
| `m1-causal-chord` | `codex/restructure-m1-causal-chord` | `c2afa9f5` | yes | — | M1 restructure packet: Record causal chord receiver verification | in main |
| `m1-core` | `codex/restructure-m1-core` | `cc5e50fa` | yes | — | M1 restructure packet: Pin main Holon core move verification receipts | in main |
| `m1-core-map` | `codex/m1-core-move-map` | `3b2acef7` | yes | — | M1 restructure packet: Pin facade dependency receipts after Geometry rebase | in main |
| `m1-cuda-mount` | `codex/restructure-m1-cuda-mount` | `858098d8` | yes | — | M1 restructure packet: Correct CUDA move scope notes | in main |
| `m1-geometry` | `codex/restructure-m1-geometry` | `d9776ea7` | yes | — | M1 restructure packet: Pin M1 geometry verification receipts | in main |
| `m1-hnn-seam-contract` | `codex/restructure-m1-hnn-seam-contract` | `1547889e` | yes | 0 / 2 | M1 resident-HNN dependency seam (#69); only two 92 MB test temp saves (.tmpBwvfBQ/*.hna) untracked, not copied | archived: worktrees/m1-hnn-seam-contract/ |
| `m1-membrane` | `codex/restructure-m1-membrane` | `29e001c3` | yes | — | M1 restructure packet: Record M1 membrane verification | in main |
| `m1-native-carriers` | `codex/restructure-m1-native-carriers` | `2a4251c2` | yes | — | M1 restructure packet: Record receiver carrier workspace gate | in main |
| `m1-native-rest` | `codex/restructure-m1-native-rest-preexisting` | `225129e8` | yes | — | M1 restructure packet: Record stacked receiver release workspace gate | in main |
| `m1-native-rest-cut` | `codex/restructure-m1-native-rest` | `5f31a87f` | yes | — | M1 restructure packet: Record main native rest workspace gate | in main |
| `m1-portable` | `codex/restructure-m1-portable` | `40f71c41` | yes | — | M1 restructure packet: Pin portable workspace caller verification | in main |
| `m1-portable-section` | `codex/restructure-m1-portable-section` | `558db631` | yes | — | M1 restructure packet: Correct portable section cut base in audit | in main |
| `m1-portable-wire` | `codex/restructure-m1-portable-wire` | `71ab435c` | yes | — | M1 restructure packet: Verify portable wire PTX and device gates | in main |
| `m1-ratio` | `codex/restructure-m1-ratio` | `cfcf6789` | yes | — | M1 restructure packet: Record M1 ratio owner verification | in main |
| `m1-receiver-release` | `codex/restructure-m1-receiver-release` | `225129e8` | yes | — | M1 restructure packet: Record stacked receiver release workspace gate | in main |
| `m1-reflection` | `codex/restructure-m1-reflection` | `d21d4564` | yes | — | M1 restructure packet: Record verified reflective generator move | in main |
| `m1-ring` | `codex/restructure-m1-ring` | `2ec7bd34` | yes | — | M1 restructure packet: Record M1 ring and CUDA admission verification | in main |
| `m1-standing` | `codex/restructure-m1-standing` | `c776fcea` | yes | — | M1 restructure packet: Record stacked standing workspace gate | in main |
| `m1-structure` | `codex/restructure-m1-structure` | `b611bd4a` | yes | — | M1 restructure packet: Pin structural carrier move verification receipts | in main |
| `m1-winding` | `codex/restructure-m1-winding` | `48d6f770` | yes | — | M1 restructure packet: Pin M1 winding verification receipts | in main |
| `m2-addressed-passage` | `codex/restructure-m2-addressed-passage` | `ac2ef96f` | yes | — | M2 restructure packet: Record M2 addressed adjoint verification | in main |
| `m2-exp-kernel` | `codex/restructure-m2-exp-kernel` | `42eb1693` | yes | — | M2 restructure packet: Record M2 Ratio kernel verification | in main |
| `m2-geometry-carry` | `codex/restructure-m2-geometry-carry` | `765123cd` | yes | — | M2 restructure packet: Record M2 geometry carry verification | in main |
| `m2-geometry-facade-next` | `codex/restructure-m2-geometry-facade-next` | `9580479e` | yes | — | M2 restructure packet: Move affine swing laws into Geometry (Refs #70) | in main |
| `m2-lineage` | `codex/restructure-m2-lineage` | `f87db7ba` | yes | — | M2 restructure packet: Extract generic connection lineage owner (Refs #70) | in main |
| `m2-pair-lock` | `codex/restructure-m2-pair-lock` | `eb0f76b7` | yes | — | M2 restructure packet: Record M2 pair-lock owner verification | in main |
| `m2-receiver-rigidity` | `codex/restructure-m2-receiver-rigidity` | `c512d37f` | yes | — | M2 restructure packet: Record M2 shared receiver verification | in main |
| `m2-root-audit` | `codex/m2-root-audit` | `a986933c` | yes | — | M2 restructure packet: docs: route unreferenced theorems through research root | in main |
| `m2-transport-word` | `codex/restructure-m2-transport-word` | `1237c8e3` | yes | — | M2 restructure packet: Record verified TransportWord owner move (Refs #70) | in main |
| `p11-base` | detached | `5b7c89ab` | yes | — | Consolidation phase 11: Carry the device quadratic moment as one storage element | in main |
| `p11-continuation` | `codex/consolidation-phase-11` | `3587c382` | yes | — | Consolidation phase 11: Record phase 11 acceptance receipts Refs #68 | in main |
| `p11-wt` | `wip/consolidation-phase-11` | `72eac4a5` | **no** | — | Paused WIP of consolidation phase 11 (commit on wip/consolidation-phase-11) | archived: branches/wip/consolidation-phase-11/ |
| `p12a-base` | detached | `5b7c89ab` | yes | — | Consolidation phase 12a: Carry the device quadratic moment as one storage element | in main |
| `p12a-wt` | `wip/consolidation-phase-12a` | `0ee4ea6d` | **no** | — | Paused WIP of consolidation phase 12a (commit on wip/consolidation-phase-12a) | archived: branches/wip/consolidation-phase-12a/ |
| `p12b-base` | detached | `7e204283` | yes | — | Consolidation phase 12b: Consolidate equation extraction as one operator Holon | in main |
| `p12b-continuation` | `codex/consolidation-phase-12b` | `d633b7d4` | yes | — | Consolidation phase 12b: Update paused-phase handoff to current C source cuts | in main |
| `p12b-wt` | `wip/consolidation-phase-12b` | `eda4ed3b` | **no** | — | Paused WIP of consolidation phase 12b (commit on wip/consolidation-phase-12b) | archived: branches/wip/consolidation-phase-12b/ |
| `p13-base` | detached | `883f33d4` | yes | — | Consolidation phase 13: Record that Soulkiller is a label and its subject is equation extraction | in main |
| `p13-wt` | detached | `883f33d4` | yes | 18 / 1 | Consolidation phase 13: factored-moment storage element; edits all already in main by content | archived: worktrees/p13-wt/ |
| `p15/base` | detached | `4dff57c8` | yes | 1 / 1 | Phase 15 base for extraction-equality tests; earlier draft of holonic_intelligence.rs + extraction_equality_tests.rs (not in main) | archived: worktrees/p15-base/ |
| `p15/head` | detached | `5b7c89ab` | yes | 48 / 4 | Phase 15 (equation extraction as one operator Holon) on phase-16 head; plan-doc 'Phase 15 disposition' section not in main | archived: worktrees/p15-head/ |
| `p15/work` | detached | `883f33d4` | yes | 43 / 4 | Phase 15 working copy on 883f33d4; all edits already in main by content | archived: worktrees/p15-work/ |
| `p16-base-tree` | detached | `4dff57c8` | yes | — | Consolidation phase 16: Carry reconstruction fibres and separators as core descent types | in main |
| `p16-verify` | detached | `5b7c89ab` | yes | 41 / 1 | Phase 16 verification tree (core-complex/world scaffold edits); all edits already in main by content | archived: worktrees/p16-verify/ |
| `p8a-wt` | detached | `7c4063b5` | yes | 16 / 0 | Phase 8a power-neutral Cayley reaction step + deposition probe; field.rs variant and 3 VERIFICATION_RECEIPTS rows not in main | archived: worktrees/p8a-wt/ |
| `r1-acoustic` | `codex/restructure-r1-acoustic` | `4afa31fe` | yes | — | R1 restructure step: Mark acoustic caller gates complete in census | in main |
| `r1-artifact` | `codex/restructure-r1-artifact` | `7310937c` | yes | — | R1 restructure step: Keep T3 census test row tabular | in main |
| `r1-bridge` | `codex/restructure-r1-bridge` | `a5b3732e` | yes | — | R1 restructure step: Record verified bridge retirement gates | in main |
| `r1-device` | `codex/restructure-r1-device` | `7711864b` | yes | — | R1 restructure step: Record combined R1 surviving suite and baseline exception | in main |
| `r1-generative` | `codex/restructure-r1-generative` | `fced65ce` | yes | — | R1 restructure step: Retire unconsumed generative transport Rust experiment | in main |
| `r1-live-presentation` | `codex/restructure-r1-live-presentation` | `07391ec9` | yes | — | R1 restructure step: Record verified CPU tile presenter retirement | in main |
| `r1-model-surface` | `codex/restructure-r1-model-surface` | `108529f9` | yes | — | R1 restructure step: Record model surface retirement gate | in main |
| `r1-parameter` | `codex/restructure-r1-parameter` | `0b851efa` | yes | — | R1 restructure step: Record verified parameter retirement | in main |
| `r1-x11` | `codex/restructure-r1-x11` | `dc380ab9` | yes | — | R1 restructure step: Record X11-free example and workspace gates | in main |
| `r2-circulation-abi` | `codex/restructure-r2-circulation-abi` | `77765cea` | yes | — | R2 restructure step: Record ABI-free HNA and locked workspace gates | in main |
| `r2-erst` | `codex/restructure-r2-erst` | `c89b7aa3` | yes | — | R2 restructure step: Verify ERST-free plate and retain runtime regression gate | in main |
| `r2-language` | `codex/restructure-r2-language` | `ff10d28a` | yes | — | R2 restructure step: Record checked reflective continuation import | in main |
| `r2-life-map` | `codex/restructure-r2-life-map` | `de6a5300` | yes | — | R2 restructure step: Link native intelligence migration slice from R2 census | in main |
| `r2-membrane-surfaces` | `codex/restructure-r2-membrane-surfaces` | `5b1cb5f7` | yes | — | R2 restructure step: Verify live OWN witnesses after replay-wrapper retirement | in main |
| `r2-membrane-trait` | `codex/restructure-r2-membrane-trait` | `79b87e9d` | yes | — | R2 restructure step: Record direct membrane trait owner gates | in main |
| `r2-owner-map` | `codex/restructure-r2-owner-map` | `08f521c8` | yes | — | R2 restructure step: Map live R2 membrane and workbench caller moves | in main |
| `r2-surface` | `codex/restructure-r2-surface` | `117c1725` | yes | — | R2 restructure step: Verify R2 surface retirement and regenerate lockfile | in main |
| `r3-directed-passage` | `codex/restructure-r3-directed-passage` | `511d49ce` | yes | — | R3 restructure step: Record combined R3 Foundation root build | in main |
| `r3-dynamics-curation` | `codex/restructure-r3-dynamics-curation` | `ff0c84e1` | yes | — | R3 restructure step: Pin Dynamics research-root curation receipt | in main |
| `r3-geometry` | `codex/restructure-r3-geometry` | `b8a03688` | yes | — | R3 restructure step: Pin Geometry curation verification receipts | in main |
| `r3-gluing` | `codex/restructure-r3-gluing` | `e8fd8fa6` | yes | — | R3 restructure step: Pin gluing extraction verification coordinate | in main |
| `r3-moment` | `codex/restructure-r3-moment` | `287b48f3` | yes | — | R3 restructure step: Record quadratic moment owner and measured Lean gates | in main |
| `r3-origin-dim` | `codex/restructure-r3-origin-dim` | `5a147e79` | **no** | — | R3 typed-origin Physics edge audit (#66); one census commit not in main | archived: branches/codex/restructure-r3-origin-dim/ |
| `r3-physics` | `codex/restructure-r3-physics` | `41206ad3` | yes | — | R3 restructure step: Record stacked Physics and Dynamics Lean closure | in main |
| `r3-ratio` | `codex/restructure-r3-ratio` | `4b69c548` | yes | — | R3 restructure step: Reconcile R3 ratio receipts with stacked foundation cuts | in main |
| `r3-receiver` | `codex/restructure-r3-receiver` | `1d32ecd2` | yes | — | R3 restructure step: Reconcile R3 receiver and gluing verification rows | in main |
| `r3-receiver-history` | `codex/restructure-r3-receiver-history` | `2981afa8` | yes | — | R3 restructure step: Move complete receiver history into Lean foundation | in main |
| `r3-separation` | `codex/restructure-r3-separation` | `5e881064` | yes | — | R3 restructure step: Extract receiver-family collapse from Lean research owner | in main |
| `r4-legacy-wave` | `codex/restructure-r4-legacy-wave` | `914a0204` | yes | — | R4 restructure step: Pin legacy wave receipt after Geometry rebase | in main |
| `r4-m1-facade` | `codex/restructure-m1-facade` | `3b2acef7` | yes | — | R4 restructure step: Pin facade dependency receipts after Geometry rebase | in main |
| `r4-zonotope-alias` | `codex/restructure-r4-zonotope-alias` | `25cf6e80` | yes | — | R4 restructure step: Pin zonotope alias receipt after Geometry rebase | in main |
| `reaction-wt` | detached | `c58f8c7d` | yes | 17 / 3 | Reaction law/deposition probe consolidation; all edits already in main by content | archived: worktrees/reaction-wt/ |
| `reset` | `reset` | `bb73054a` | yes | — | The September 24 reset commit itself (same as origin/main) | in main |
| `retire` | `restructure/retire` | `13f8c734` | yes | — | September 24 retirement / M1 prune line (tip 13f8c734, last pre-reset tree) | in main |
| `t-engine` | `restructure/t-engine` | `5835ff91` | yes | — | Restructure test-rebuild line: T: retire campaign, legacy-format and prose tests in the engine | in main |
| `t-hnn` | `restructure/t-hnn` | `a47cc70a` | yes | — | Restructure test-rebuild line: T: retire campaign, legacy-format and prose tests in the HNN area | in main |
| `t-main` | `restructure/t-main` | `56b9ce8a` | yes | — | Restructure test-rebuild line: T: reduce the verification ladder to four gates | in main |
| `verify-wt` | detached | `7e204283` | yes | 43 / 1 | Phase 16 verification tree on 7e204283; all edits already in main by content | archived: worktrees/verify-wt/ |
| `worktrees/athena-math-review-2026-09-09` | detached | `5167e325` | yes | 0 / 1 | Athena math review; untracked normal_geometry_review.rs example (already in main by content) | archived: worktrees/worktrees-athena-math-review-2026-09-09/ |
| `worktrees/tube-current` | detached | `04064e78` | yes | 0 / 1 | Tube-current study; untracked four_torus_current.rs example (already in main by content) | archived: worktrees/worktrees-tube-current/ |

Skipped untracked files (not copied): `m1-hnn-seam-contract/crates/holonics-hna/.tmpBwvfBQ/pn39.hna` (92 MB > 5 MB); `m1-hnn-seam-contract/crates/holonics-hna/.tmpBwvfBQ/pn47.hna` (92 MB > 5 MB) — leftover test temp saves under a `.tmp*` directory.

Ignored non-build content: `.local/r1-x11/.local/artifacts/` (5 MB of receiver-slice run artifacts, private) was moved to the main checkout's `.local/archive/worktree-leftovers-2026-09-24/r1-x11/artifacts/` rather than published.

## Local branches (89)

| Branch | HEAD | Ancestor | Ahead | What it was | Disposition |
|---|---|---|---|---|---|
| `backup/pre-hna-consolidation-2026-09-04` | `08965182` | yes | 0 | Backup pointer before the Sep 4 HNA consolidation | in main |
| `codex/c-phase12a-current-cut` | `939fe650` | yes | 0 | Consolidation phase 12a: Pin phase 12a current-format verification receipts | in main |
| `codex/c-phase12a-integration` | `75d357d6` | **no** | 1 | Census map of phase-12a integration onto phase 11 (#68), C_PHASE12A_INTEGRATION.md | archived: branches/codex/c-phase12a-integration/ |
| `codex/consolidation-phase-11` | `3587c382` | yes | 0 | Consolidation phase 11: Record phase 11 acceptance receipts Refs #68 | in main |
| `codex/consolidation-phase-12b` | `d633b7d4` | yes | 0 | Consolidation phase 12b: Update paused-phase handoff to current C source cuts | in main |
| `codex/consolidation-phase12b-archive` | `68d3183f` | yes | 0 | Consolidation phase 12b: Correct final Phase12b all-target receipt | in main |
| `codex/consolidation-phase12b-grammar-rest` | `45d13d64` | yes | 0 | Consolidation phase 12b: Record organizational rest refusal gate | in main |
| `codex/consolidation-phase12b-session` | `a1cfbfca` | yes | 0 | Consolidation phase 12b: Record coupled session format retirement gates (Refs #68) | in main |
| `codex/m1-core-move-map` | `3b2acef7` | yes | 0 | M1 restructure packet: Pin facade dependency receipts after Geometry rebase | in main |
| `codex/m2-root-audit` | `a986933c` | yes | 0 | M2 restructure packet: docs: route unreferenced theorems through research root | in main |
| `codex/repository-restructure-design` | `925b94b8` | yes | 0 | Repository restructure design (plan THE_REPOSITORY_RESTRUCTURE) | in main |
| `codex/restructure-k1-holarchy-contract` | `e64688bc` | yes | 0 | K1 construction campaign: Clarify K1 Holarchy contract | in main |
| `codex/restructure-m1-abi-retire` | `49537dad` | yes | 0 | M1 restructure packet: Record ABI retirement workspace gate | in main |
| `codex/restructure-m1-action` | `de1502b6` | yes | 0 | M1 restructure packet: Record action owner verification gates | in main |
| `codex/restructure-m1-causal-chord` | `c2afa9f5` | yes | 0 | M1 restructure packet: Record causal chord receiver verification | in main |
| `codex/restructure-m1-core` | `cc5e50fa` | yes | 0 | M1 restructure packet: Pin main Holon core move verification receipts | in main |
| `codex/restructure-m1-cuda-mount` | `858098d8` | yes | 0 | M1 restructure packet: Correct CUDA move scope notes | in main |
| `codex/restructure-m1-facade` | `3b2acef7` | yes | 0 | M1 restructure packet: Pin facade dependency receipts after Geometry rebase | in main |
| `codex/restructure-m1-geometry` | `d9776ea7` | yes | 0 | M1 restructure packet: Pin M1 geometry verification receipts | in main |
| `codex/restructure-m1-hnn-seam-contract` | `1547889e` | yes | 0 | M1 restructure packet: Clarify M1 resident HNN dependency seam (Refs #69) | in main |
| `codex/restructure-m1-membrane` | `29e001c3` | yes | 0 | M1 restructure packet: Record M1 membrane verification | in main |
| `codex/restructure-m1-native-carriers` | `2a4251c2` | yes | 0 | M1 restructure packet: Record receiver carrier workspace gate | in main |
| `codex/restructure-m1-native-rest` | `5f31a87f` | yes | 0 | M1 restructure packet: Record main native rest workspace gate | in main |
| `codex/restructure-m1-native-rest-preexisting` | `225129e8` | yes | 0 | M1 restructure packet: Record stacked receiver release workspace gate | in main |
| `codex/restructure-m1-portable` | `40f71c41` | yes | 0 | M1 restructure packet: Pin portable workspace caller verification | in main |
| `codex/restructure-m1-portable-section` | `558db631` | yes | 0 | M1 restructure packet: Correct portable section cut base in audit | in main |
| `codex/restructure-m1-portable-wire` | `71ab435c` | yes | 0 | M1 restructure packet: Verify portable wire PTX and device gates | in main |
| `codex/restructure-m1-ratio` | `cfcf6789` | yes | 0 | M1 restructure packet: Record M1 ratio owner verification | in main |
| `codex/restructure-m1-receiver-release` | `225129e8` | yes | 0 | M1 restructure packet: Record stacked receiver release workspace gate | in main |
| `codex/restructure-m1-reflection` | `d21d4564` | yes | 0 | M1 restructure packet: Record verified reflective generator move | in main |
| `codex/restructure-m1-ring` | `2ec7bd34` | yes | 0 | M1 restructure packet: Record M1 ring and CUDA admission verification | in main |
| `codex/restructure-m1-standing` | `c776fcea` | yes | 0 | M1 restructure packet: Record stacked standing workspace gate | in main |
| `codex/restructure-m1-structure` | `b611bd4a` | yes | 0 | M1 restructure packet: Pin structural carrier move verification receipts | in main |
| `codex/restructure-m1-winding` | `48d6f770` | yes | 0 | M1 restructure packet: Pin M1 winding verification receipts | in main |
| `codex/restructure-m2-addressed-passage` | `ac2ef96f` | yes | 0 | M2 restructure packet: Record M2 addressed adjoint verification | in main |
| `codex/restructure-m2-exp-kernel` | `42eb1693` | yes | 0 | M2 restructure packet: Record M2 Ratio kernel verification | in main |
| `codex/restructure-m2-geometry-carry` | `765123cd` | yes | 0 | M2 restructure packet: Record M2 geometry carry verification | in main |
| `codex/restructure-m2-geometry-facade-next` | `9580479e` | yes | 0 | M2 restructure packet: Move affine swing laws into Geometry (Refs #70) | in main |
| `codex/restructure-m2-lineage` | `f87db7ba` | yes | 0 | M2 restructure packet: Extract generic connection lineage owner (Refs #70) | in main |
| `codex/restructure-m2-pair-lock` | `eb0f76b7` | yes | 0 | M2 restructure packet: Record M2 pair-lock owner verification | in main |
| `codex/restructure-m2-receiver-rigidity` | `c512d37f` | yes | 0 | M2 restructure packet: Record M2 shared receiver verification | in main |
| `codex/restructure-m2-transport-word` | `1237c8e3` | yes | 0 | M2 restructure packet: Record verified TransportWord owner move (Refs #70) | in main |
| `codex/restructure-r0` | `1a6299e4` | yes | 0 | R0 restructure inventory/census line; was checked out in the main checkout | in main |
| `codex/restructure-r1-acoustic` | `4afa31fe` | yes | 0 | R1 restructure step: Mark acoustic caller gates complete in census | in main |
| `codex/restructure-r1-artifact` | `7310937c` | yes | 0 | R1 restructure step: Keep T3 census test row tabular | in main |
| `codex/restructure-r1-bridge` | `a5b3732e` | yes | 0 | R1 restructure step: Record verified bridge retirement gates | in main |
| `codex/restructure-r1-device` | `7711864b` | yes | 0 | R1 restructure step: Record combined R1 surviving suite and baseline exception | in main |
| `codex/restructure-r1-generative` | `fced65ce` | yes | 0 | R1 restructure step: Retire unconsumed generative transport Rust experiment | in main |
| `codex/restructure-r1-live-presentation` | `07391ec9` | yes | 0 | R1 restructure step: Record verified CPU tile presenter retirement | in main |
| `codex/restructure-r1-model-surface` | `108529f9` | yes | 0 | R1 restructure step: Record model surface retirement gate | in main |
| `codex/restructure-r1-parameter` | `0b851efa` | yes | 0 | R1 restructure step: Record verified parameter retirement | in main |
| `codex/restructure-r1-x11` | `dc380ab9` | yes | 0 | R1 restructure step: Record X11-free example and workspace gates | in main |
| `codex/restructure-r2-circulation-abi` | `77765cea` | yes | 0 | R2 restructure step: Record ABI-free HNA and locked workspace gates | in main |
| `codex/restructure-r2-erst` | `c89b7aa3` | yes | 0 | R2 restructure step: Verify ERST-free plate and retain runtime regression gate | in main |
| `codex/restructure-r2-language` | `ff10d28a` | yes | 0 | R2 restructure step: Record checked reflective continuation import | in main |
| `codex/restructure-r2-life-map` | `de6a5300` | yes | 0 | R2 restructure step: Link native intelligence migration slice from R2 census | in main |
| `codex/restructure-r2-membrane-surfaces` | `5b1cb5f7` | yes | 0 | R2 restructure step: Verify live OWN witnesses after replay-wrapper retirement | in main |
| `codex/restructure-r2-membrane-trait` | `79b87e9d` | yes | 0 | R2 restructure step: Record direct membrane trait owner gates | in main |
| `codex/restructure-r2-owner-map` | `08f521c8` | yes | 0 | R2 restructure step: Map live R2 membrane and workbench caller moves | in main |
| `codex/restructure-r2-surface` | `117c1725` | yes | 0 | R2 restructure step: Verify R2 surface retirement and regenerate lockfile | in main |
| `codex/restructure-r3-directed-passage` | `511d49ce` | yes | 0 | R3 restructure step: Record combined R3 Foundation root build | in main |
| `codex/restructure-r3-dynamics-curation` | `ff0c84e1` | yes | 0 | R3 restructure step: Pin Dynamics research-root curation receipt | in main |
| `codex/restructure-r3-geometry` | `b8a03688` | yes | 0 | R3 restructure step: Pin Geometry curation verification receipts | in main |
| `codex/restructure-r3-gluing` | `e8fd8fa6` | yes | 0 | R3 restructure step: Pin gluing extraction verification coordinate | in main |
| `codex/restructure-r3-moment` | `287b48f3` | yes | 0 | R3 restructure step: Record quadratic moment owner and measured Lean gates | in main |
| `codex/restructure-r3-origin-dim` | `5a147e79` | **no** | 1 | R3 audit of the typed-origin Physics edge (#66): LEAN_CORE_R3_EDGES.md census update | archived: branches/codex/restructure-r3-origin-dim/ |
| `codex/restructure-r3-physics` | `41206ad3` | yes | 0 | R3 restructure step: Record stacked Physics and Dynamics Lean closure | in main |
| `codex/restructure-r3-ratio` | `4b69c548` | yes | 0 | R3 restructure step: Reconcile R3 ratio receipts with stacked foundation cuts | in main |
| `codex/restructure-r3-receiver` | `1d32ecd2` | yes | 0 | R3 restructure step: Reconcile R3 receiver and gluing verification rows | in main |
| `codex/restructure-r3-receiver-history` | `2981afa8` | yes | 0 | R3 restructure step: Move complete receiver history into Lean foundation | in main |
| `codex/restructure-r3-separation` | `5e881064` | yes | 0 | R3 restructure step: Extract receiver-family collapse from Lean research owner | in main |
| `codex/restructure-r4-legacy-wave` | `914a0204` | yes | 0 | R4 restructure step: Pin legacy wave receipt after Geometry rebase | in main |
| `codex/restructure-r4-zonotope-alias` | `25cf6e80` | yes | 0 | R4 restructure step: Pin zonotope alias receipt after Geometry rebase | in main |
| `main` | `925b94b8` | yes | 0 | Local main (stale at 925b94b8 before this cleanup; fast-forwarded to origin/main) | kept |
| `quarantine/station-e-predecessor` | `06347e10` | **no** | 1 | Pre-2026-08-19 Station E native occurrence/native law material, quarantined (not admitted, not deleted) | archived: branches/quarantine/station-e-predecessor/ |
| `reset` | `bb73054a` | yes | 0 | The September 24 reset commit (bb73054a = origin/main) | in main |
| `restructure/lessons` | `1b8588ec` | yes | 0 | Record lessons from the workbench and Athena prototypes before retirement | in main |
| `restructure/retire` | `13f8c734` | yes | 0 | M1 prune: delete the dead holonic_complex and local_star modules | in main |
| `restructure/t-engine` | `5835ff91` | yes | 0 | Restructure test-rebuild line: T: retire campaign, legacy-format and prose tests in the engine | in main |
| `restructure/t-hnn` | `a47cc70a` | yes | 0 | Restructure test-rebuild line: T: retire campaign, legacy-format and prose tests in the HNN area | in main |
| `restructure/t-main` | `56b9ce8a` | yes | 0 | Restructure test-rebuild line: T: reduce the verification ladder to four gates | in main |
| `wip/consolidation-phase-11` | `72eac4a5` | **no** | 1 | Paused, unverified WIP snapshot of consolidation phase 11 (33 files; nearly all later landed via codex/consolidation-phase-11) | archived: branches/wip/consolidation-phase-11/ |
| `wip/consolidation-phase-12a` | `0ee4ea6d` | **no** | 1 | Paused, unverified WIP snapshot of phase 12a (20 files; field_session.rs/native_source.rs variants not in main) | archived: branches/wip/consolidation-phase-12a/ |
| `wip/consolidation-phase-12b` | `eda4ed3b` | **no** | 1 | Paused, unverified WIP snapshot of phase 12b (13 files; coupled-wave comparison/rest variants not in main) | archived: branches/wip/consolidation-phase-12b/ |
| `worktree-agent-a19944b6cca013c53` | `d6091343` | yes | 0 | Claude subagent isolation branch: Correct the docs that named the departed construction and its two commands | in main |
| `worktree-agent-a44f0ed9db44c5cb6` | `46392518` | yes | 0 | Claude subagent isolation branch: Admit the RIDE the law ratified, and name why the machine returns 14,018 answers to one... | in main |
| `worktree-agent-abd40f244bb7bb27f` | `46392518` | yes | 0 | Claude subagent isolation branch: Admit the RIDE the law ratified, and name why the machine returns 14,018 answers to one... | in main |
| `worktree-agent-abe258622bb41beb4` | `46392518` | yes | 0 | Claude subagent isolation branch: Admit the RIDE the law ratified, and name why the machine returns 14,018 answers to one... | in main |
| `worktree-agent-af930e6b1a4245b5f` | `46392518` | yes | 0 | Claude subagent isolation branch: Admit the RIDE the law ratified, and name why the machine returns 14,018 answers to one... | in main |

## Remote branches (origin) (71)

| Branch | HEAD | Ancestor | Ahead | What it was | Disposition |
|---|---|---|---|---|---|
| `codex/apple-silicon` | `9b7b4b63` | **no** | 27 | Brandon's Apple-silicon/Metal port (Sep 6-7): acoustic fields, Metal kernels, 23 research records, HOLONICS_ON_APPLE_SILICON plan; never merged | archived: branches/codex/apple-silicon/ |
| `codex/c-phase12a-current-cut` | `939fe650` | yes | 0 | Consolidation phase 12a: Pin phase 12a current-format verification receipts | in main |
| `codex/consolidation-phase-11` | `3587c382` | yes | 0 | Consolidation phase 11: Record phase 11 acceptance receipts Refs #68 | in main |
| `codex/consolidation-phase-12b` | `d633b7d4` | yes | 0 | Consolidation phase 12b: Update paused-phase handoff to current C source cuts | in main |
| `codex/consolidation-phase12b-archive` | `68d3183f` | yes | 0 | Consolidation phase 12b: Correct final Phase12b all-target receipt | in main |
| `codex/consolidation-phase12b-grammar-rest` | `45d13d64` | yes | 0 | Consolidation phase 12b: Record organizational rest refusal gate | in main |
| `codex/consolidation-phase12b-session` | `a1cfbfca` | yes | 0 | Consolidation phase 12b: Record coupled session format retirement gates (Refs #68) | in main |
| `codex/m2-root-audit` | `a986933c` | yes | 0 | M2 restructure packet: docs: route unreferenced theorems through research root | in main |
| `codex/repository-restructure-design` | `925b94b8` | yes | 0 | Repository restructure design (plan THE_REPOSITORY_RESTRUCTURE) | in main |
| `codex/restructure-k1-holarchy-contract` | `e64688bc` | yes | 0 | K1 construction campaign: Clarify K1 Holarchy contract | in main |
| `codex/restructure-m1-abi-retire` | `49537dad` | yes | 0 | M1 restructure packet: Record ABI retirement workspace gate | in main |
| `codex/restructure-m1-action` | `de1502b6` | yes | 0 | M1 restructure packet: Record action owner verification gates | in main |
| `codex/restructure-m1-causal-chord` | `c2afa9f5` | yes | 0 | M1 restructure packet: Record causal chord receiver verification | in main |
| `codex/restructure-m1-core` | `cc5e50fa` | yes | 0 | M1 restructure packet: Pin main Holon core move verification receipts | in main |
| `codex/restructure-m1-cuda-mount` | `858098d8` | yes | 0 | M1 restructure packet: Correct CUDA move scope notes | in main |
| `codex/restructure-m1-facade` | `3b2acef7` | yes | 0 | M1 restructure packet: Pin facade dependency receipts after Geometry rebase | in main |
| `codex/restructure-m1-geometry` | `d9776ea7` | yes | 0 | M1 restructure packet: Pin M1 geometry verification receipts | in main |
| `codex/restructure-m1-hnn-seam-contract` | `1547889e` | yes | 0 | M1 restructure packet: Clarify M1 resident HNN dependency seam (Refs #69) | in main |
| `codex/restructure-m1-membrane` | `29e001c3` | yes | 0 | M1 restructure packet: Record M1 membrane verification | in main |
| `codex/restructure-m1-native-carriers` | `2a4251c2` | yes | 0 | M1 restructure packet: Record receiver carrier workspace gate | in main |
| `codex/restructure-m1-native-rest` | `5f31a87f` | yes | 0 | M1 restructure packet: Record main native rest workspace gate | in main |
| `codex/restructure-m1-portable` | `40f71c41` | yes | 0 | M1 restructure packet: Pin portable workspace caller verification | in main |
| `codex/restructure-m1-portable-section` | `558db631` | yes | 0 | M1 restructure packet: Correct portable section cut base in audit | in main |
| `codex/restructure-m1-portable-wire` | `71ab435c` | yes | 0 | M1 restructure packet: Verify portable wire PTX and device gates | in main |
| `codex/restructure-m1-ratio` | `cfcf6789` | yes | 0 | M1 restructure packet: Record M1 ratio owner verification | in main |
| `codex/restructure-m1-receiver-release` | `225129e8` | yes | 0 | M1 restructure packet: Record stacked receiver release workspace gate | in main |
| `codex/restructure-m1-reflection` | `d21d4564` | yes | 0 | M1 restructure packet: Record verified reflective generator move | in main |
| `codex/restructure-m1-ring` | `2ec7bd34` | yes | 0 | M1 restructure packet: Record M1 ring and CUDA admission verification | in main |
| `codex/restructure-m1-standing` | `c776fcea` | yes | 0 | M1 restructure packet: Record stacked standing workspace gate | in main |
| `codex/restructure-m1-structure` | `b611bd4a` | yes | 0 | M1 restructure packet: Pin structural carrier move verification receipts | in main |
| `codex/restructure-m1-winding` | `48d6f770` | yes | 0 | M1 restructure packet: Pin M1 winding verification receipts | in main |
| `codex/restructure-m2-addressed-passage` | `ac2ef96f` | yes | 0 | M2 restructure packet: Record M2 addressed adjoint verification | in main |
| `codex/restructure-m2-exp-kernel` | `42eb1693` | yes | 0 | M2 restructure packet: Record M2 Ratio kernel verification | in main |
| `codex/restructure-m2-geometry-carry` | `765123cd` | yes | 0 | M2 restructure packet: Record M2 geometry carry verification | in main |
| `codex/restructure-m2-geometry-facade-next` | `9580479e` | yes | 0 | M2 restructure packet: Move affine swing laws into Geometry (Refs #70) | in main |
| `codex/restructure-m2-lineage` | `f87db7ba` | yes | 0 | M2 restructure packet: Extract generic connection lineage owner (Refs #70) | in main |
| `codex/restructure-m2-pair-lock` | `eb0f76b7` | yes | 0 | M2 restructure packet: Record M2 pair-lock owner verification | in main |
| `codex/restructure-m2-receiver-rigidity` | `c512d37f` | yes | 0 | M2 restructure packet: Record M2 shared receiver verification | in main |
| `codex/restructure-m2-transport-word` | `1237c8e3` | yes | 0 | M2 restructure packet: Record verified TransportWord owner move (Refs #70) | in main |
| `codex/restructure-r0` | `1a6299e4` | yes | 0 | R0 restructure inventory/census line; was checked out in the main checkout | in main |
| `codex/restructure-r1-acoustic` | `4afa31fe` | yes | 0 | R1 restructure step: Mark acoustic caller gates complete in census | in main |
| `codex/restructure-r1-artifact` | `7310937c` | yes | 0 | R1 restructure step: Keep T3 census test row tabular | in main |
| `codex/restructure-r1-bridge` | `a5b3732e` | yes | 0 | R1 restructure step: Record verified bridge retirement gates | in main |
| `codex/restructure-r1-device` | `7711864b` | yes | 0 | R1 restructure step: Record combined R1 surviving suite and baseline exception | in main |
| `codex/restructure-r1-generative` | `fced65ce` | yes | 0 | R1 restructure step: Retire unconsumed generative transport Rust experiment | in main |
| `codex/restructure-r1-live-presentation` | `07391ec9` | yes | 0 | R1 restructure step: Record verified CPU tile presenter retirement | in main |
| `codex/restructure-r1-model-surface` | `108529f9` | yes | 0 | R1 restructure step: Record model surface retirement gate | in main |
| `codex/restructure-r1-parameter` | `0b851efa` | yes | 0 | R1 restructure step: Record verified parameter retirement | in main |
| `codex/restructure-r1-x11` | `dc380ab9` | yes | 0 | R1 restructure step: Record X11-free example and workspace gates | in main |
| `codex/restructure-r2-circulation-abi` | `77765cea` | yes | 0 | R2 restructure step: Record ABI-free HNA and locked workspace gates | in main |
| `codex/restructure-r2-erst` | `c89b7aa3` | yes | 0 | R2 restructure step: Verify ERST-free plate and retain runtime regression gate | in main |
| `codex/restructure-r2-language` | `ff10d28a` | yes | 0 | R2 restructure step: Record checked reflective continuation import | in main |
| `codex/restructure-r2-life-map` | `de6a5300` | yes | 0 | R2 restructure step: Link native intelligence migration slice from R2 census | in main |
| `codex/restructure-r2-membrane-surfaces` | `5b1cb5f7` | yes | 0 | R2 restructure step: Verify live OWN witnesses after replay-wrapper retirement | in main |
| `codex/restructure-r2-membrane-trait` | `79b87e9d` | yes | 0 | R2 restructure step: Record direct membrane trait owner gates | in main |
| `codex/restructure-r2-owner-map` | `08f521c8` | yes | 0 | R2 restructure step: Map live R2 membrane and workbench caller moves | in main |
| `codex/restructure-r2-surface` | `117c1725` | yes | 0 | R2 restructure step: Verify R2 surface retirement and regenerate lockfile | in main |
| `codex/restructure-r3-directed-passage` | `511d49ce` | yes | 0 | R3 restructure step: Record combined R3 Foundation root build | in main |
| `codex/restructure-r3-dynamics-curation` | `ff0c84e1` | yes | 0 | R3 restructure step: Pin Dynamics research-root curation receipt | in main |
| `codex/restructure-r3-geometry` | `b8a03688` | yes | 0 | R3 restructure step: Pin Geometry curation verification receipts | in main |
| `codex/restructure-r3-gluing` | `e8fd8fa6` | yes | 0 | R3 restructure step: Pin gluing extraction verification coordinate | in main |
| `codex/restructure-r3-moment` | `287b48f3` | yes | 0 | R3 restructure step: Record quadratic moment owner and measured Lean gates | in main |
| `codex/restructure-r3-physics` | `41206ad3` | yes | 0 | R3 restructure step: Record stacked Physics and Dynamics Lean closure | in main |
| `codex/restructure-r3-ratio` | `4b69c548` | yes | 0 | R3 restructure step: Reconcile R3 ratio receipts with stacked foundation cuts | in main |
| `codex/restructure-r3-receiver` | `1d32ecd2` | yes | 0 | R3 restructure step: Reconcile R3 receiver and gluing verification rows | in main |
| `codex/restructure-r3-receiver-history` | `2981afa8` | yes | 0 | R3 restructure step: Move complete receiver history into Lean foundation | in main |
| `codex/restructure-r3-separation` | `5e881064` | yes | 0 | R3 restructure step: Extract receiver-family collapse from Lean research owner | in main |
| `codex/restructure-r4-legacy-wave` | `914a0204` | yes | 0 | R4 restructure step: Pin legacy wave receipt after Geometry rebase | in main |
| `codex/restructure-r4-zonotope-alias` | `25cf6e80` | yes | 0 | R4 restructure step: Pin zonotope alias receipt after Geometry rebase | in main |
| `main` | `bb73054a` | yes | 0 | Local main (stale at 925b94b8 before this cleanup; fast-forwarded to origin/main) | kept |
| `restructure/retire` | `ac84b070` | yes | 0 | Point the archive permalinks at the rewritten last commit that holds archive/ | in main |

## Other refs (left in place)

| Ref | Status | Disposition |
|---|---|---|
| `stash@{0}` `f0a603e6` (2026-09-01) | On main: non-MVF formal work preserved again before terminal MVF authority return; tracked: 2 files changed, 13 insertions(+), 4 deletions(-); untracked: 9 files changed, 2321 insertions(+) | archived: stashes/stashes.bundle (ref kept) |
| `stash@{1}` `7e6f4fed` (2026-09-01) | On main: non-MVF formal work preserved outside active MVF goal before release; tracked: 3 files changed, 15 insertions(+), 5 deletions(-); untracked: 9 files changed, 2321 insertions(+) | archived: stashes/stashes.bundle (ref kept) |
| `stash@{2}` `9a078840` (2026-09-01) | On main: additional non-SCF formal work preserved during SCF release; tracked: no tracked changes; untracked: 1 file changed, 412 insertions(+) | archived: stashes/stashes.bundle (ref kept) |
| `stash@{3}` `64572588` (2026-09-01) | On main: pre-existing non-SCF formal work preserved before SCF release; tracked: 3 files changed, 11 insertions(+), 5 deletions(-); untracked: 3 files changed, 983 insertions(+) | archived: stashes/stashes.bundle (ref kept) |
| `stash@{4}` `1c73eaed` (2026-08-30) | On main: pre-consolidation-2026-08-30-uar-housekeeping; tracked: 225 files changed, 59444 insertions(+), 7709 deletions(-); untracked: 841 files changed, 283874 insertions(+) | archived: stashes/stashes.bundle (ref kept) |
| `refs/original/refs/heads/restructure/retire` `542f1dfa` | pre-rewrite copy of `restructure/retire`; tree identical to main's `bc61a318` | in main (by tree); ref kept |
| `refs/codex/turn-diffs/checkpoints/*` (6) | Codex harness checkpoint trees | harness-owned; ref kept |


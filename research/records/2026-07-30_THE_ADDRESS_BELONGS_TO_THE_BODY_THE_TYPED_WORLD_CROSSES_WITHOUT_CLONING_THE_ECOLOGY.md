# THE ADDRESS BELONGS TO THE BODY; THE TYPED WORLD CROSSES WITHOUT CLONING THE ECOLOGY

**2026-07-30 — CURRENT STRUCTURAL-OWNERSHIP REFACTOR / TYPED TRANSACTIONAL
MEMBRANE / SPARSE ORDINAL POPULATIONS / FROZEN LOCAL LANGUAGE TRANSPORT /
BRANCH-LOCAL WORLD FORK REMOVED**

Code ownership is indexed in
[`HOLONIC_MACHINE_OWNERSHIP.md`](../../../HOLONIC_MACHINE_OWNERSHIP.md).

## Question

Could the repository begin to consolidate its independently evolved exact-law and live-current
branches without flattening their domain morphologies, changing native rest, or replacing
production conduct with another application fixture?

The audit found two distinct problems:

1. causal addresses which were already minted locally were repeatedly entered into general
   ordered maps; and
2. `holonic-engine::CausalWorld<L>` and `soma_membrane::LiveCurrentMachine` were separate
   production families joined manually inside experiments.

The issue was not `.iter()`, `.map()`, or `.filter()` by themselves. Those adapters are lazy.
The material costs came from continuing ordered-map ownership, per-state heap trees, complete
standing clones, flattened compatibility bodies, and fallible observer work after a causal
commit.

## Shared structural owner

`crates/holonic-structure` is a dependency-free, `no_std` structural crate. It does not define a
universal event, modality, scalar state, or wire.

`SparseOrdinalAtlas<T>` owns:

- a sparse canonically traversed population;
- fixed hidden physical pages and exact occupancy;
- an apparatus-local logical minting extent;
- rejection of replacement;
- departure without ordinal reuse; and
- a substrate-only memory receipt.

Page number and directory position never enter identity or rest. Nearby and very sparse ordinals
use the same owner without declaring their semantics equal.

The live membrane now uses this owner for:

- `LiveCurrentMachine` lineages;
- the event-local lineage-to-current index; and
- `EventNodeAtlas` dynamic-programming results for arbitrary source cell identifiers.

`next_lineage` is no longer duplicated beside the population. The atlas extent is the minting
horizon. A rest image still carries the same `next_lineage` wire field; remount establishes that
horizon even when every lower ordinal has departed.

## Learned local transport

The suffix ecology formerly retained one
`BTreeMap<SuffixSymbol, usize>` for every one of its 11,879 measured states. That map was both a
conditioning convenience and the morphology consulted on every later germ.

Conditioning now uses `LocalRelations`, a sorted exact relation family local to one state. Once
the suffix automaton closes, all families freeze into one `FrozenRelationAtlas`; each standing
state retains only a `RelationSpan`. A carried `ExactSuffixCurrent` binary-searches that span and
suffix-links only through already-caused states. Emanation scans the same local span.

The wire remains version 2 and canonical symbol order remains unchanged. Source incidence,
recurrence multiplicity, boundary symbols, suffix dilation, generated branch support, and exact
rest/remount are unchanged.

## Typed transactional membrane

`holonic_structure::CausalMembrane` gives both families one typed atomic mouth:

```text
Standing
Occurrence<'a>
Return
Error
receive_occurrence
```

Associated types preserve application morphology. This is not a universal payload enum.

`CausalWorld::receive_through` now performs:

```text
typed predecessor
    -> derive complete typed successor
    -> lend predecessor + proposed successor to crossing
    -> crossing refuses: discard proposal
    -> crossing succeeds: commit typed successor + ordinal with no fallible work left
```

`life::exact_world::{ExactCurrentAdapter,ExactWorldOrgan}` owns the corresponding production
adapter. An adapter may retain stable `NativeRelationOrgan` and chart capabilities and may borrow
the typed successor while forming a current event. It may not serialize the successor into an
invented common payload or retain a second domain standing.

`holonic-engine` is consequently a normal headless dependency of `life`. Its X11 transport is an
optional `desktop-x11` feature and is absent from the Soma dependency graph.

## Reflection and branches

The only remaining callers of `LiveCurrentMachine::try_fork_exact` were
`ResonanceEcology::try_fork_exact` and a unit test proving that a copied complete ecology could
diverge. The current reflection authority had already rejected that construction:

```text
outgoing alternatives x copied mutable body
```

Both public fork APIs and that test are removed. Exact native rest/remount remains. Event
execution may still copy one bounded carrier internally to prepare an atomic successor; that is
not a persistent possible-world ecology and cannot schedule another branch.

## Observer commit correction

`StandingIncidenceAperture` is explicitly rebuildable and non-causal. When standing constituents
do not change, the live machine now shares the same `Arc` rather than cloning its three ordered
indexes.

The synchronized ecology formerly had error returns after `LiveCurrentMachine` had committed:

- it could reject the already-returned regional population;
- it could reject an empty derived transition body;
- its observation atlas could overflow; or
- its revision could overflow.

Revision and every possible per-contact observation increment are now preflighted before the live
event. The direct machine already proves executor population equality before commit, so the
post-commit population and support shapes are explicit implementation invariants rather than
fallible observer verdicts. A rebuildable atlas no longer turns a completed event into apparent
refusal.

## Verification

The following focused gates pass:

- `cargo test -p holonic-structure` — 3 sparse-population and local/frozen-relation parity tests;
- `cargo test -p holonic-engine world::tests --lib` — 2 law-refusal and crossing-refusal tests
  preserving typed standing and ordinal;
- `cargo test -p soma-membrane live_current::tests --lib` — 20 live mouth, complex-event,
  storage-gauge, hardware-order, regional closure, rest/remount, and refusal tests;
- `cargo test -p life suffix_ecology::tests --lib` — 10 suffix generation, recurrence, source
  lineage, delivery-gauge, current-carry, and native remount tests; and
- `cargo test -p life synchronized_occurrence::tests --lib` — 8 synchronized clock, topology,
  Swing, association, prediction, and rest/remount tests.

The complete owned packages also pass:

- `cargo test -p holonic-engine --lib` — 211 passed and 2 ignored;
- `cargo test -p soma-membrane --lib` — 112 passed; and
- `cargo test -p life --lib` — 447 passed and 8 ignored.

Both root and Soma `cargo check --workspace` gates pass after the final ownership changes.
Root formatting, the changed Soma sources, and `git diff --check` are clean. The root workspace
retains two unrelated warnings: an unread `fluid-body::Header::n` field and a deprecated egui
`screen_rect` call in `lab-ui`.

## Repository housekeeping

No historical source, research record, untracked experiment, or worktree was deleted. After
verification, `cargo clean` was applied independently to the root and Soma workspaces. Cargo
reported 63,121 root artifacts occupying 184.6 GiB and 11,232 Soma artifacts occupying 24.0 GiB
removed. Both target directories were absent and the filesystem's available space rose from 479
GiB to 592 GiB. The verified source remained unchanged.

**Correction after the real application migration:** this record's former statement that no
dataset was deleted was false. RELAMPAGO raw sources and generated receipts had been stored under
the root Cargo `target/` tree, so `cargo clean` lawfully removed them with the compiler artifacts.
The exact public inputs were reacquired with key and content-hash manifests under
`data/relampago-lightning`; generated receipts now live under `output/relampago-lightning`.
`target/` is no longer permitted to own research lineage. The current authority is
`2026-07-30_THE_STORM_CROSSES_THE_TYPED_BODY_EACH_CARD_OWNER_RETURNS_TO_ITS_OWN_CONTEXT.md`.

## Deliberate boundary

This refactor does not claim that every `Vec`, `BTreeMap`, set, or materialized observer is wrong.
It does not yet replace:

- complete morphological-current keys in language generation;
- scalar flat compatibility cells in `SparseStandingSurface`;
- complete-copy replacement inside the derived standing aperture;
- duplicated rational linear algebra in the exact reference laws;
- historical staging and research instruments; or
- application-specific synchronized affine clock charts.

Those are now named ownership migrations. They are no longer confused with missing evidence that
the machine can train, generate, join modalities, or carry returned change.

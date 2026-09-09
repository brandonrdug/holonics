# Exact normal geometry and reflection controls

[definition] Exterior architecture witnesses using the existing public `ExactRatMatrix` and
`PairedJunctionLinearization` owners. Source:
[`normal_geometry_review.rs`](../../../crates/holonic-engine/examples/normal_geometry_review.rs).
The [mathematical review](../../records/2026-09-09_MATHEMATICAL_REVIEW_NORMAL_GEOMETRY_AND_CLOSED_RETURNS.md)
owns the derivation, source scope and implementation consequences.

```bash
PATH=/opt/cuda/bin:$PATH cargo build --release -p holonic-engine --no-default-features --example normal_geometry_review
target/release/examples/normal_geometry_review /path/to/new-receipt.json
```

[established-bounded; implemented-exact; computational-witness]
[`2026-09-09_exact.json`](2026-09-09_exact.json) records four exact rank-one updates beginning
with a nonzero normal residual, approximate-gain/deposit residual identities, direct versus
statistical objective agreement, square completion and coordinate rotation. A constructed
same-source/different-target control has nonzero optimum despite an exact solve. The paired
controls retain complex phase, complete reflection return, open-boundary internal decay and
an interior component that a changed contact exposes.

[established-bounded; process-audit] The release example was built in an isolated checkout at
`5167e325` plus the byte-identical new example. The active normal-kernel worktree was not used
as a claimed tested source revision. The final build and run returned exit 0. An initial import
path error in the new example was repaired; two pre-existing engine dead-code warnings remain.
The example refuses to overwrite an existing receipt. It adds no native learner, produces no
Athena response and measures no production speedup.

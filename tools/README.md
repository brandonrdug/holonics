# Optional development helpers

[definition] Use a tool when it answers the actual work. There is no blanket repository gate
requiring document regexes, source-size ledgers, generated indexes or untouched paper builds.

`lean_check.sh [TARGET]` is retained for current Lean work: it invokes the pinned project,
shows progress and refuses a `sorry` warning. It is opt-in, not an inference dependency or an
automatic requirement for a Rust edit. Cargo owns Rust build/test discovery.

The superseded suite is in [archive/tooling](../archive/tooling/README.md). Prior Nsight scripts
are [research instruments](../research/experiments/profiling/README.md). Provenance owns the
equation-atlas/navigation role; ordinary navigation starts with the
[architecture](../docs/ARCHITECTURE.md) and [directory map](../docs/REPOSITORY.md).

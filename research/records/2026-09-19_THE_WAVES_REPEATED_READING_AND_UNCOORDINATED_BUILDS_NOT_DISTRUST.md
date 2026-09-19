# The waves repeated reading and uncoordinated builds, not distrust

**Date:** September 19, 2026. **Kind:** conversation-log and workflow audit of the September 17–19
Claude waves (`19964c20..4bd15f43`), requested by Brandon before the next wave. **Scope:** the
primary session and its 110 subagent transcripts, the September 19 review logs, Git history and the
policy text. One Opus 5 agent extracted the tables read-only; the primary checked the policy
quotations, the two searches below and the disk figures first-hand. The full tables and log
coordinates are private under `.local/workflow-review-2026-09-19/REPORT.md`. It schedules nothing.

## Findings

[established-bounded; process-audit] The session ran 40.2 hours of wall clock, 110 agents, 8,990
shell calls and 1,691 cargo/lake runs. Builds and tests took 31.2 agent-hours inside 14.3 wall
hours.

| Category | Agent-hours | Share | Reading |
|---|---|---|---|
| A worker repeating its own scope while editing | 14.43 | 46 % | ordinary edit–test cycles |
| Cargo build-lock waiting | 4.98 | 16 % | waste: up to eight workers on one `target/` |
| Different agents running the same scope | 4.37 | 14 % | waste: crate-wide clippy by 43 agents, unfiltered engine tests by 15 |
| Reviewers re-running worker scopes | 3.02 | 10 % | waste: reviewers were handed no receipts |
| Primary re-running worker scopes | 1.25 | 4 % | mostly removable; 0.75 h more was the one earned integrated run |

[established-bounded; process-audit] Brandon's complaint of redundant execution is confirmed, with
a different main cause than first-hand distrust by the primary: the primary twice declined to
re-run worker measurements. The cost came from too many workers on one tree, from workers running
crate-wide scopes, and from reviewers with no record of what had run. The two waves that exceeded
the roadmap's four-worker cap (seven and eight workers) carry 85 of the 108 lock waits, and one
reviewer spawned 27 descendants over ten topics. Concurrent GPU runs were negligible (three
overlaps, 160 seconds); the serial-device rule held. The September 19 review's three full engine
runs each caught a distinct new failure and were earned.

[established-bounded; process-audit] Execution redundancy cost machine time and latency, not
context. The token cost was **rediscovery**: 47 % of all tool calls were reads or searches,
returning about 4.4 M tokens — 7.5 times what every build printed. 77 of 110 agents read AGENTS.md
in full; 79 symbol patterns were each searched by four or more agents.

[established-bounded; source-audit] No tracked file recorded what was validated, against which
tree, by which command. Position documents carried bare counts.

[counterexample; source-audit] Two failures were each one search away, and in neither was any
search run. `junction_law.rs` at `4bd15f43` said the repository carried no Lorentzian metric;
`.agents/bin/prior-art 'lorentz|minkowski|spacetime'` returns 259 files, and
`HolonicCurvedArcEinstein.minkowskiMetric` dates from August 24. The worker had run about fifty
searches on the junction chain and none for the object it declared absent; a test then pinned the
false sentence. And the neck, junction and jet plans were written with no reference to the
Holonic Interaction typed on August 14, 20 and 24, whose Lean owners include a finite interface
chain. The existing clause "follow the current source chain" left no artefact, so compliance was
unfalsifiable. `ARCHITECTURE_MAP` names 19 % of Lean files, and 27 % of research records are cited
from `docs/`; but record titles are full sentences, and nobody searched them.

[established-bounded; measured] `target/` held 626 GB (284 GB of examples, 185 GB incremental) with
28 GB free on the volume; an 8.8 GB SKE4 rest was stored inside it. The rest moved to
`.local/artifacts/ske4/rest.bin` and `cargo clean` removed 164,087 files. Per-worker target
directories were therefore rejected; workers share one `target/` and build module scopes only.

[historical] The [August 18 audit](2026-08-18_THE_GATE_IS_A_RELEASE_RECEIVER_NOT_AN_INNER_LOOP_AND_REPEATED_VALIDATION_BECAME_THE_BOTTLENECK.md)
reached the same verdict for a different apparatus. Its gates were archived; nothing was put in
their place to record what had already been answered, so repetition returned through agents.

## Repairs made with this record

[definition] [`docs/WORKER_BRIEF.md`](../../docs/WORKER_BRIEF.md) carries the wave shape, who runs
what, the prior-art rule, the decision marker, the standing invariant commands and the prompt and
return templates. [`docs/VERIFICATION_RECEIPTS.tsv`](../../docs/VERIFICATION_RECEIPTS.tsv) is an
appended receipt log, seeded from the September 19 review at `d31b9afa`; it is not a gate.
`.agents/bin/prior-art` is the cross-language and record-title search. AGENTS.md, roadmap rules
9–11, DEVELOPMENT and AGENT_PROTOCOL now separate a worker's judgement (testimony) from its
measurement (receipt), cap a wave at three disjoint workers and one non-spawning reviewer, and
record Brandon's rulings that execution against real targets is the strongest validation and that
an agent decides from the mathematics, marks the choice `[agent-inferred]` and proceeds. The owner
map gains the Holonic Interaction row. Estimated saving against this run: about 12 of 31 agent-hours.

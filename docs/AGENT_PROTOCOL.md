# Repository evidence protocol

[definition] Shared operating support for [AGENTS.md](../AGENTS.md). Consult the relevant section;
do not treat historical testimony or the exterior memory apparatus as construction authority.
Paths in code spans are repository-relative.

## Evidence sources and apparatus atlas

[definition] Everything here is evidence or apparatus testimony and never a scheduler.

- `research/records/` retains dated evidence; [RETRACTIONS.md](RETRACTIONS.md) records capability
  corrections, and the subject guides link the relevant current returns.
- `/home/b/Workspaces/laboratory` is the frozen predecessor (1,658 commits, 2026-05-10 to
  2026-08-03). Enter through `LABORATORY_REVIEW.md`, `HOLONIC_MACHINE_OWNERSHIP.md`,
  `src/soma/README.md`, `src/soma/RESEARCH/`, `src/soma/FORMULA.md`, and
  `src/holobrochos/CANON/05_EROS_OUTPUT_CAUSALITY.md`, which carries the best text outputs ever
  returned with verbatim samples and their caveats. Pinned snapshots live under `archive/reference/`.
- `archive/cpp-engine/evidence/observations/eros-*` holds the July Rust laboratory's observations,
  each with `RESULTS.md`; `archive/cpp-engine/CONSTRUCTION_STATE.md` records why the C++ body was
  retired.
- Conversation logs are standing evidence for design intent and are to be consulted on any
  Eros/Athena task. Codex: `~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl`, one file per thread or
  sub-thread; a line with `type == "response_item"`, `payload.type == "message"`, and
  `payload.role` in `user`/`assistant` is a message; `session_meta.payload.thread_source ==
  "subagent"` marks child-agent origin, not model identity; user text beginning `<codex_internal_context`,
  `<environment_context`, `<user_instructions`, `<user_shell_command`, or `# AGENTS.md` is harness
  text. Keep repeated captured views by declared occurrence ID; equal text never identifies an
  occurrence. Preserve first container origin when a child log copies parent metadata. Claude:
  `~/.claude/history.jsonl` and `~/.claude/projects/<workspace>/*.jsonl`; user-role tool returns,
  task notifications and generated compaction summaries are not human messages. The
  [conversation-data guide](CONVERSATION_DATA.md) and `applications/conversation-data/providers.py`
  carry the detailed exterior codec and separate comparison/trace relations. Private logs and
  prepared datasets are optional local evidence; they are not included in a Git checkout.
  For focused inspection, select the message occurrence first and print only its text blocks;
  do not serialize base64 attachments or whole mixed-content records into tool output. Inspect
  a required image through the image-reading tools instead of expanding its encoded bytes.
- Apparatus, measured 2026-09-02: one NVIDIA GeForce RTX 4080 SUPER with 16 GiB, a Ryzen 9 7900X,
  30 GiB of system memory. The foreign realization is `/home/b/models/gemma-4-E4B-it` (15 GiB
  BF16, 2,130 tensors). Python apparatus for world and observer use only:
  `/home/b/scratch/huggingface/.venv` (torch 2.12 cu130, transformers 5.8.1 with Gemma4 classes).
  The complete excitation receipt producer lives outside this repository. [2026-09-03: the in-repo
  consumer `crates/holonic-engine/src/holonic_intelligence/scaffold_excitation_receipt.rs` and the
  SCF2 example departed without alias under SKE4 with the per-event generator construction; no
  in-repo reader of that receipt remains.] Lean 4.33 with Mathlib
  through `lake`; the kernel world port is `crates/holonic-life/src/lean_mathematics/kernel_returns.rs`.
  The Rust body is `crates/holonic-engine` and `crates/holonic-life`; `life::native_intelligence` wraps the
  engine's `NativeTransportScaffold` rather than competing with it.

## Repository-local evidence and handoff

[definition] A conduct audit distinguishes four sources: the direct instruction, the assistant's
subsequent decision/tool action, the plan at that revision, and the resulting source or output.
Retain their coordinates and chronology. A later confession, copied parent message or current
summary is not evidence of the original decision. If a link cannot be recovered, report that
boundary instead of filling it with an inferred story. Logs can establish scope substitution
and procedural conduct; they do not expose a unique hidden psychological or prompting cause.

[project-postulate] After compaction, distinguish a newly delivered human occurrence from a
retained view of an earlier request. Carry that request's disposition and the unresolved
consuming operation through the handoff. A completed paper, audit or experiment remains completed
when its initiating message is still visible. Check the recorded occurrence and completed return
when this is ambiguous; do not restart the subject from its URL or wording. A paused continuation
control does not become active because old user text survives compaction. The
[September 14 audit](../research/records/2026-09-14_DIRECT_MESSAGES_AND_THE_PAUSED_HNN_RUN.md)
records the concrete failure and its original coordinates.

[project-postulate] A context handoff carries the current construction's reason as well as its
mechanics: the human objective and breadth, governing corrections, active unknown, available
relations, actual source/receiver, consuming implementation, failed alternatives that matter,
and the next discriminating result. Use the existing position and dated record for continuity;
do not create another scheduler or raw-history requirement. The
[development method](DEVELOPMENT.md#mathematical-implementation-and-continuation) gives the
working form. An agent's judgement is testimony until the primary inspects the changed source.
Its recorded checks are [receipts](VERIFICATION_RECEIPTS.tsv): re-run only a scope whose paths
changed since the receipt's tree, plus the one integrated run a combined tree owes.

[definition] The plan's presence in a tool read proves it was accessed, not followed. Check the
chosen edit and its consumer against the governing mathematical contract. An implementation
assumption copied into a goal or current-position note remains an agent choice until its scope
is established by the direct instruction and source. Preserve that distinction in summaries.

[project-postulate] Brandon's September 6 consolidation retires the external memory database and
connector from Holonics operation. Do not query or deposit into it, start cursors, send graph
messages, require schema consensus, or make a Mac checkout depend on its installation. The
[one-time import and synthesis](../research/records/2026-09-06_REPOSITORY_SYNTHESIS_AND_PORTABLE_EVIDENCE.md)
preserves the needed testimony and its historical relationships here. Older connector instructions
and messages are archived evidence, never pickup directions. The original database is retained
untouched; retirement does not authorize deleting it.

[definition] A material research or implementation return belongs with its source and dated
record. Record the exact statement, one truth-status grade, evidence tags, source symbols and
revision, hypotheses, receiver/domain, retained difference or open fibre, and the actual checks.
Link corrections to the earlier claim and state which part remains standing. A copied statement
is testimony about that source, not a second independent measurement or a fresh theorem.

[definition] Direct user messages govern at their stated scope and chronological position.
Quote only text actually read; otherwise label a paraphrase. Retain a source coordinate and the
necessary context in the repository record, without committing private raw logs. Agent reports,
search rankings, former claim grades and equal wording cannot replace that authority.

[definition] Mathematical derivations retain their source/target constructions, ordered operation,
receiver, hypotheses, orientation, boundary and Preimage Fibre in the actual formal source
and its explanatory record. Notation and serialized diagrams remain presentations. Lean verifies
research separately; no Lean parser, kernel call, theorem emitter or verdict enters HNN cultivation
or inference pipelines. Lean text already present in conversation logs remains ordinary material.

[definition] Use the subject guides, maintained [owner map](ARCHITECTURE_MAP.md), dated records,
`rg` and Git history for navigation. Update the current position while work is active and put the
substantial completed return in its existing record. The roadmap alone orders construction.
No generated claim census, equation registry, database replica service or blanket validation gate
replaces the retired apparatus.

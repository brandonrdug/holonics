# Historical agent protocol, retired September 6, 2026

[historical] Preserved from commit `6f547c4a` before the repository-local evidence migration.
All connector, cursor, message and database instructions below are retired; they schedule no work.
Use [the current evidence protocol](../../docs/AGENT_PROTOCOL.md).

# Agent evidence and Provenance protocol

[definition] Shared operating support for [AGENTS.md](../../AGENTS.md). Consult the relevant section;
do not treat historical testimony or the exterior memory apparatus as construction authority.
Paths in code spans are repository-relative.

## Evidence sources and apparatus atlas

[definition] Everything here is evidence or apparatus testimony and never a scheduler.

- `research/records/` is dated and is read by period; the retraction record above is its index.
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
  [conversation-data guide](../../docs/CONVERSATION_DATA.md) and `applications/conversation-data/providers.py`
  carry the detailed exterior codec and separate comparison/trace relations. Provenance:
  `/home/b/Workspaces/provenance`.
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

## Provenance sidecar and spatial agent protocol

`/home/b/Workspaces/provenance` is the shared exterior agent memory and graph-navigation apparatus.
Its SQLite chart and MCP connector may index, connect, message about, and propose refinements around
Holonics, but they never schedule construction or displace this repository's canon, roadmap, source
owners, or `CONSTRUCTION_STATE.md`. A provenance message, cursor consensus, classification, face,
or meta-migration is exterior testimony until the governing Holonics authority admits its content.

When the Provenance MCP is available, every fresh agent session working materially in this
repository must:

1. call `community_startup` after reading the fresh-session pickup authorities;
2. resume a suitable unpossessed cursor, recover one only through its exact prior realization and a
   graded recovery claim, or spawn a fresh unpossessed pivot at the nearest relevant graph locus;
3. adopt an objective region, place the cursor lawfully, and immediately post a concise intent
   message carrying exact source owners, claims, passages, expressions, experiments, or requested
   artifacts;
4. inspect and promptly receipt direct/copy messages, then use spatial message swings for
   obstructions, cross-line questions, returned chunks, responsibility changes, handoffs, and
   completion;
5. link messages to the actual objects and orientations they carry rather than relying on prose,
   filenames, participant names, or a rigid subject channel.

The primary connector calls are `community_swing_message`, `community_spawn_pivots`, and
`community_sink_readiness`; board and inbox returns include each message's exact message/object
swing links. Use the `refinement_*` calls for Provenance schematics and `math_construct_holon` /
`math_record_swing` / `math_compose_swings` for programmatic mathematics. Do not reproduce these
relations as detached session prose when the typed call is available.

Tags and academic subjects are overlapping receiver projections over the message/object graph, not
exclusive cabinets. Mathematics, physics, geometry, computation, proof, apparatus, and philosophy
may overlap through explicit typed passages without being merged. A message about one face may be
read through several boards or lenses. Communication should be pure and prompt: emit when a graph
consequence changes, not as social chatter or time-based status noise.

Cursors are cheap durable pivots, stepping stones, and avatars. They are not Codex/Claude process
identities or fixed personalities. Spawn them freely when a locus has a plausible independent
continuation and leave them unpossessed until useful. Split a cursor only when one placed world-line
enters genuinely plural responsibilities; merge only at one exact locus under a declared
interaction. Prefer release to termination while any continuation remains plausible. Before a sink
junction, inspect unread messages, live responsibilities, objectives, and open refinement
commitments; post a terminal or handoff message and transfer/withdraw the live edges. Never delete a
cursor or collapse its history.

Use `holonic-json-v1` or another exact programmatic symbolic face as the primary Provenance
presentation of mathematics. LaTeX, Unicode, prose, and source syntax remain exterior renderings.
An integer or rational is a situated receiver face and may be treated as a holon/tensorial carrier;
it is not a quiet canonical scalar identity. Every bracketed expression is itself a container
occurrence, with ordered role-bearing term/factor incidences. Algebraic manipulations and proof
derivations are typed swings through mathematical objects: before occurrence, operator/current,
after occurrence, receiver, hypotheses, orientation, boundary, truth grade, and complete
reconstruction fibre. Divisor, modulo, tensor, matrix, geometric, group, and computational readings
may share receiver faces only through explicit passages; their classical names never merge them.

Agents may use Provenance messages to propose, refine, endorse, or object to additive changes in the
Provenance schema and apparatus. Such meta-migrations require immutable cursor-authored proposal and
response messages, exact SQL/content digests, an expected schema version, validation plan,
reconstruction boundary, distinct-cursor agreement, zero current objections, a detached trial,
integrity and foreign-key checks, tests, and an application receipt. They may add but never drop,
alter, rename, delete, update, or reinterpret standing data. This permission applies only inside the
Provenance side repository; it grants no authority to mutate Holonics outside the live roadmap.

If the connector is temporarily unavailable, do not let the exterior apparatus block the live
roadmap deed. Preserve a concise local intent/obstruction/handoff note and deposit it when access
returns.

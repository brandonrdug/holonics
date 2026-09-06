# Conversation data preserves user-agent difference without a prover or synthetic feedback

**Authority:** Brandon's September 6 instruction to integrate/synthesize and refine Claude Code
and Codex conversation material. **Scope:** data review, preparation and curation; no model
training run or new language-capability judgment.

## Historical findings

[historical; source-inspected] The July 21
[authorship correction](2026-07-21_THE_CONVERSATION_OPENS_THE_HYPOTHESIS_THE_RECORD_PRESERVES_WHO_SAID_WHAT.md)
already distinguishes user exploration/constraints, agent-derived notation and assumptions,
ratification at a particular scope, and established evidence. A user message containing an
agent's quotation does not make the user the originator of every quoted assertion. Conversation
must not be flattened into a set of equally authoritative or eternally applicable statements.

[established-bounded; source-inspected] The August 22 A1/A2 work already retained useful distinctions:
visible dialogue versus richer event incidence; parent UUID versus shared-session membership;
tool-call/result references; branch/sibling relations; and different occurrences with equal
content. Their records explicitly did not establish training quality or a scalar winning reply.
Those distinctions are reused; a native equal-content quotient is not needed to package the data.

[counterexample; source-inspected] `dialogue_native_spool.rs` reduces the selected dialogue's
state to `depth % 2` and rejects a predecessor with two successors as `dialogue/native-branch`.
That bounded linear-chain/parity projection cannot carry the present request's user-agent
comparison or general conversation branching. Its bounded apparatus is not being reclassified
as the desired dataset relation.

[counterexample; source-inspected] `eros_agentic_research_conversation.rs` assigns
`correction_text = first.answer.text`, constructs `AgenticLanguageFeedbackKind::Correction`,
prints the result as `you>`, and submits it through the feedback path. This is an agent answer
presented as a user's correction, not actual human feedback. A data importer must preserve that
printed material as the tool/agent event in which it occurred, not infer a human speaker from it.

[established-bounded; source-inspected] The older language/research integration also carries
`AgenticFormalReturn { completion: LeanKernelDeedCompletion }` and a `FormalReturn` codec aperture
in `agentic_language.rs`. Such an application-specific formal return does not define the
user-agent comparison of conversation-history cultivation. The latest instruction excludes
using a Lean evaluator, theorem-emission route or proof verdict to provide that comparison.
This does not remove Lean discussions/tool records from the corpus or revoke separately scoped
mathematics; it keeps the actual human and tool receivers distinct.

[historical; source-inspected] The August 26
[situated-difference audit](2026-08-26_THE_RETURNED_DIFFERENCE_IS_A_SITUATED_HOLON_PERSPECTIVE_TRANSPORT_CARRIES_ITS_ADJOINT_AND_CULTIVATION_MUST_PRESERVE_THE_COMPLETE_LOSS_SECTION.md)
already rejects promoting an observed agent response to the correct answer, scalarizing the full
comparison, or making cross-history contact trivial by assigning every source a disjoint column.
The present data pass retains comparison operands, their context and overlap rather than choosing
an edit distance, token-ID difference, reward, provider ranking or theorem-check result.

## Actual schema hazards found in the current logs

[established-bounded; source-inspected] Claude's `role=user` records include tool-result blocks,
task notifications, generated compaction summaries and client-command output. Explicitly
human-origin commands remain human material; older command wrappers without that attribution are
kept as controls, not assumed fresh feedback. Codex agent rollouts can begin with their own subagent metadata and
later contain copied parent/main metadata. Visible assistant text can coexist with thinking or
tool calls; API message/generation IDs are not the same as record UUIDs. Codex also stores
presentation/completion mirrors alongside canonical response records. None of these should
manufacture a new human message, replace the container's actual origin, or leak a response into
its own alleged input.

[definition] The refined package therefore separates:

- actual direct human messages and visible responding-agent parts;
- worker input/inherited context and worker output;
- harness/client controls and duplicated presentations;
- available reasoning and opaque/unavailable content;
- individual tool call/result parts and their scoped references;
- explicit parentage, serialized order, declared occurrence views and later human observations.

[definition] An observed agent response is not gold. A later human message is not automatically
approval or correction. User-role text in an agent branch is named branch input, not new human
material. A source field or quoted `you>` label cannot change those relationships. Tags and
rhetorical/semantic interpretations are separately authored curation and do not override the raw
source or native learning law.

## Implemented preparation boundary

[established-bounded; implemented-exact] `applications/conversation-data/` is a Python
standard-library exterior application. Its SQLite artifact retains exact consumed JSONL records
in lossless compression, raw byte ranges and captured source-prefix extents, normalized parts,
provider/actor/turn/model attributes and explicit relations. It uses no native model, GPU, Lean,
Torch or network service. Raw logs are read, not modified; output files are private and published
without replacing existing destinations.

[established-bounded; implemented-exact] Visible-order fallback is limited to the same declared
conversation/branch; an unresolved explicit parent never silently falls back to the latest speaker.
Tool returns are resolved using source/session/branch, prior call occurrences and exact block
pointers. Reused IDs retain ambiguous candidates instead of choosing an arbitrary producer.
Multi-call/multi-result messages retain their complete part incidences. Same-ID captured views
remain grouped with their full occurrence populations; identical words alone do not merge events.

[established-bounded; implemented-exact] User/response comparison exports contain only their
proper visible operands and source/context references, with no gold status or assigned loss.
Later human observations have a separate export and are not added to the earlier response input.
Recorded response intervals are explicitly not automatic prompts or proof of causal reach.
Semantic curation is source-addressed, with author, grade, rationale and validated JSON pointers.
It can overlap topics and conversational moves without becoming an authored interior classifier.

[established-bounded; measured] The initial pilot retained 88,218,006 source bytes in 15,450
records across a main Codex thread, a child Codex thread and a Claude thread. It returned 213
user-agent comparison occurrences and excluded the child-agent exchange from that set while
retaining its material. The initial complete capture then retained 42,003,137,699 bytes from
1,886 files as 3,451,841 records. This is raw log volume, not a claim of equally weighted training
signal or a token-volume objective.

[definition] The initial complete capture remains private provenance. A separate refined
projection is derived from those same captured raw records, not by rereading now-growing logs.
The data guide names the final usable artifacts and curation. Parsing/categorization is not
reported as a trained-model result or a regression of the repository's existing capabilities.

[established-bounded; measured] The refined artifact contains 2,717 human-attributed records,
24,311 user-agent comparison views in 23,338 declared pair families, 2,612 separate later-human
observations and 30 authored curation annotations across 17 messages. The [data guide](../../docs/CONVERSATION_DATA.md#september-6-local-return)
names the private artifacts, historical-revision cases and unresolved references. All 1,886
source coordinates/counts matched the initial capture; 3,791 exact raw/coordinate comparisons,
including every source boundary and curated events, matched. This is scoped data verification,
not a semantic quality verdict.

## Verification and interpretation

[established-bounded; measured] Twenty-three focused tests cover source reconstruction, private
no-overwrite publication, missing IDs, mixed controls/material, real provider roles, quoted JSON,
branch origins, explicit-parent precedence, actor-scoped adjacency, part-level tool links,
ambiguous IDs, repeated words versus repeated views, separated later observations, source-addressed
curation and reprojection without source-log access. No unrelated paper/document or native-model
release suite was invoked for data preparation.

[counterexample; source-inspected] The first final-link query allowed SQLite to scan earlier
source records before matching call IDs. Its query plan exposed history-quadratic work. The
explicit join order now matches the indexed call ID first, then checks actor/chronological scope.
The already-completed raw capture and normalized projection were retained while that final
link-resolution step was repaired. No source import or model training was repeated to hide the
issue.

[counterexample; source-inspected] `docs/AGENT_PROTOCOL.md` still told agents to deduplicate
resumed history by text. That live clause now points to declared-occurrence views and the actual
provider codec: identical wording cannot collapse separately situated occurrences. The source
and navigation consumers were corrected together; no generated repository census was introduced.

[definition] The useful training distinctions are richer than prompt/answer imitation: request
versus realized response; response versus a later explicitly scoped correction; revised responses
under changed instructions; actually shared-source sibling continuations; and the tool/agent
route through which a response was produced. The package makes these differences addressable.
It does not pretend that data-role labels or parser success have computed their semantic loss.

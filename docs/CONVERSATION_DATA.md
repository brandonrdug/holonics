# Conversation data: authorship, comparison and continuing routes

[definition] Brandon's September 6 instruction concerns integration and synthesis. The dataset
must retain what the collaboration actually did, so that native learning can gauge a situated
difference. Packaging the logs is not a reason to install a prover, a conventional trainer or an
authored semantic scoring mechanism. The [current preparation contract](plans/CONVERSATION_DATA_INTEGRATION.md)
and [historical findings](../research/records/2026-09-06_CONVERSATION_DATA_PRESERVES_USER_AGENT_DIFFERENCE_WITHOUT_A_PROVER_OR_SYNTHETIC_FEEDBACK.md)
state the completed preparation scope. Existing HNA/language capability is preserved;
Athena-alpha remains unattained under Brandon's subsequent September 6 ruling.

## The primary distinction

[definition] Actual human user messages and the agent's responding messages supply user-agent
comparison material. The response is observed conduct, not an automatically correct target.
The user request and response are differently oriented acts, not two strings which should become
identical. Later human returns can clarify the intended difference; they are not automatically
positive/negative rewards, and approval of one point does not ratify everything an agent wrote.

[definition] Tool calls/results, delegation, recorded inference and client/harness activity have
their own relations. They remain available as routes, context and ordinary material. They do not
become Brandon's feedback because a log wraps them in `role=user`, because a tool prints `you>`,
because a command succeeds, or because an agent calls its own answer a correction. Their absence
from the user-agent comparison does not mean their causal differences are zero or irrelevant.

| Material | Retained relationship | Not inferred |
|---|---|---|
| Human request → agent response | Actual operands, authors, branch/parent/turn and presentation | Agent answer is gold; lexical equality is fulfillment |
| Agent response → later human message | Later observation with its exact earlier reference | Automatic approval, correction, or same-topic continuation |
| Agent call → tool result | Protocol call reference, actor scope and full block incidence | Tool success is user satisfaction or proof of a semantic claim |
| Main/child agent histories | Actual parent/session/branch testimony and copied context | Controller prompts are new human requests; shared session means parentage |
| Reasoning, summaries and event mirrors | Available trace or explicitly opaque/unavailable material | Hidden reasoning is reconstructed; duplicated presentations are new messages |

## Package and use

[definition] The application uses Python's standard-library SQLite, JSON and zlib codecs. That is
exterior data preparation, not the native learning mechanism. It captures every source's byte
boundary before processing, reads incrementally and retains exact consumed raw records—including
unknown records and partial tails—in lossless per-record compression. Source paths, record numbers
and raw byte ranges remain reconstruction coordinates, not semantic identities.

```sh
python3 applications/conversation-data/conversation_data.py prepare \
  --codex /home/b/.codex/sessions --claude /home/b/.claude/projects \
  --output .local/datasets/conversations-new.sqlite

python3 applications/conversation-data/conversation_data.py inspect \
  .local/datasets/conversations-new.sqlite
```

[definition] Each provider option accepts a file or directory; directory discovery takes JSONL
files recursively. Inputs are expected to be append-only provider logs. A capture is the consumed
bounded prefix, not a claim of an atomic snapshot of every independently changing log. Original
logs are never edited. Publication refuses an existing destination. Raw records may contain
sensitive material: dataset and export files are created with owner-only permissions and remain
local under ignored `.local/`. There is no upload or public-corpus publication step.

[definition] The package contains:

| Table/view | Role |
|---|---|
| `sources` | Declared provider, source path, captured extent and container-origin context |
| `events` | Exact raw record plus normalized role, scope, phase, model, identity and serialization coordinates |
| `parts` | Visible text/material, harness text, reasoning, tools and opaque parts with original JSON pointers |
| `tool_ports` | Individual call/result parts; multiple ports in one message remain distinct |
| `links` | Declared parents, tool returns/candidates and later human observations; unresolved references retained |
| `comparisons` | Source-supported human-request/agent-response candidates, with their linkage evidence |
| `declared_record_views`, `comparison_groups` | Multiple captured presentations of declared occurrence IDs, without text-based merging |
| `agent_generations` | Provider-declared API generation membership, distinct from record UUID and user turn |
| `declared_branch_origins` | Explicit parent-session/agent-path testimony, without treating shared-session membership as parentage |
| `group_characteristics` | Overlapping provider/session/branch/workspace/model/phase/author projections |
| `annotations` | Explicit curator interpretations and source-addressed relationships; these do not rewrite source facts |

## Relations and availability

[definition] Explicit provider parentage takes precedence over serialization adjacency. A missing
parent remains unresolved rather than being replaced with the most recent speaker. When a provider
supplies no parent, visible-order pairing is restricted to the same conversation/branch and is
labelled as such; it does not prove semantic relevance. Model/workspace changes remain facets,
not automatic prohibitions on a legitimate continuing exchange.

[definition] Call references are scoped to source, session and branch, with prior call occurrences
and exact content-part pointers. A reused call ID with multiple candidates retains that candidate
fibre and an unresolved return; no arbitrary producer is selected. Shared session membership never
manufactures a parent edge or a giant pairwise causal relation.

[definition] Codex child logs can contain copied main-session metadata. The first container origin
is retained, so copied metadata cannot relabel child input as a fresh human instruction. Client
control blocks, automatic goal continuations, developer instructions and presentation mirrors do
not become new human training signals. Claude task notifications and generated resumed-session
summaries remain runtime/harness material. Commands explicitly attributed to a human are retained
as `human-command`; older command wrappers without that attribution stay control material, not
assumed fresh feedback. Visible assistant text in a message containing thinking or
tool calls remains visible text; the other parts retain their own kinds. Quoted JSON and role
labels inside content are never reparsed into additional speakers.

[definition] Equal text does not merge occurrences. Grouping captured representations by the
provider's declared record ID keeps every actual view and its circumstances; it is not a theorem
of source identity. Missing IDs retain distinct captured record addresses. An API generation ID
groups generation parts and is not substituted for their distinct record IDs.

```sh
python3 applications/conversation-data/conversation_data.py export-comparisons \
  .local/datasets/conversations-new.sqlite --output .local/datasets/comparisons-new.jsonl
python3 applications/conversation-data/conversation_data.py export-followups \
  .local/datasets/conversations-new.sqlite --output .local/datasets/followups-new.jsonl
```

[definition] The first export groups declared user/response occurrence-pair families and keeps
all their captured views. Its actual comparison operands contain only the appropriate visible
user/agent parts; other parts are references, not silently included answer text. It assigns no
scalar loss and no gold-answer status. Later human observations are exported separately, not
attached to an earlier response's input. This separation matters even when a later correction
would make the earlier task easier to answer.

[definition] A recorded interval is not a ready-made prompt or a proof of causal reach. Internal
response routes are not automatically teacher input, and completion mirrors can duplicate the
target response before its canonical display record. A consuming application must declare its
input boundary and receiver: select actual available ancestry, keep internal/world routes distinct,
and withhold the candidate response and later observations appropriately. Train/evaluation splits
must keep linked forks and repeated occurrence views together, or declare a temporal cut retaining
shared earlier context while withholding later consequences. There is no random message split or
fixed context-window rule imposed by the packager.

[definition] Curation made with later history is also later knowledge. An annotation can help
select a training comparison without being supplied to the earlier response as information it
already possessed. The comparison export does not inject curator labels or later observations
into its operands.

## Curation without an authored native classifier

[definition] Useful overlapping views include request/response orientation; explicit user
correction and the statement it targets; clarification and revised response; development of one
idea across successive exchanges; sibling continuations under an actually shared source; and the
tool/agent route that produced a response. Topics and rhetorical moves can be curator annotations
with source evidence. They are not exclusive native taxa, automatic scores or routing keys inside
Athena. Counts and provider/model names are observable group characteristics, not quality weights.

```json
{"author":"curator","truth_status":"interpretation","kind":"rhetorical-move","label":"scoped-correction","event":123,"target_event":119,"pointer":"/payload/content/0/text","rationale":"This actual user clause corrects the preceding response's scope; it does not reject every earlier result."}
```

[definition] The numeric references in the example are placeholders. Actual annotations must
resolve to records in the chosen package; supplied JSON pointers must resolve in the exact raw
record. Multiple annotations may overlap. They add interpretation without changing the user/agent
role, the primary comparisons, the raw text or the declared protocol relations.

```sh
python3 applications/conversation-data/conversation_data.py annotate \
  .local/datasets/conversations-new.sqlite .local/datasets/curation.jsonl
python3 applications/conversation-data/conversation_data.py reproject \
  .local/datasets/conversations-new.sqlite --output .local/datasets/conversations-revised.sqlite
```

[definition] `reproject` refines derived views from the same captured bytes. It does not reread
growing source logs, replace the previous package or erase raw events. This permits correction
of an encoding/linkage interpretation without losing the source that exposed its error.

## No Lean-shaped training pipeline

[definition] Lean discussions, code blocks and recorded tool returns remain ordinary material
when they occur in the logs. They are not stripped from the corpus, translated into a mandatory
formal language, executed by preparation, or used as the user-agent verdict. The new application
imports no repository learner/prover code and calls no model or proof runtime. It supplies
source-qualified operands and relationships for integration; the native receiver must own the
actual situated difference. Packaging is not itself a model-training result.

## September 6 local return

[established-bounded; measured] The inspected refined package retains 42,003,137,699 captured
bytes from 1,886 JSONL files as 3,451,841 records. Its human-attributed projection has 2,717 records
(1,873 Codex, 844 Claude), with 24,311 user-agent comparison views grouped into 23,338 declared
pair families, plus 2,612 separately exported later human observations. A request can have
multiple visible replies, including progress messages; phase and API-generation membership are
retained. These counts are not independent-example weights, token objectives or quality scores.

[established-bounded; measured] The usable artifacts are private, mode `0600`, under ignored
`.local/datasets/`:

| File | Contents |
|---|---|
| `conversations-refined-2026-09-06.sqlite` | Complete captured source and corrected relational projection; 34,758,037,504 bytes |
| `conversation-comparisons-2026-09-06.jsonl` | 23,338 grouped comparison records, 24,311 captured views |
| `conversation-followups-2026-09-06.jsonl` | 2,612 later observations, separate from earlier response inputs |
| `conversation-curation-2026-09-06.jsonl` | 30 authored annotations across 17 actual message occurrences; also installed in SQLite |

[historical] `conversations-2026-09-06.sqlite` is the preserved initial capture, not the usable
role projection; `conversations-pilot-2026-09-06.sqlite` is earlier pilot evidence. Both predate
the full role corrections. Use the **refined** artifact above for integration. Source bytes and
coordinates survive the refinement; nothing was recaptured to conceal a changed interpretation.

[interpretation; source-inspected] Curation records overlapping topics, rhetorical moves and
temporal relations rather than exhaustive semantic labels. Concrete cases include:

- The August 24 proposal of a “Describe Brandon” probe and the September 1 instruction rejecting
  that naïve experiment. This is an instruction revision, not two timeless targets or an extra
  human-agent comparison. Dates follow message timestamps, not thread-creation filenames.
- The September 2 Claude prohibition on hand-wired Lean output, its later Codex handoff, and the
  September 6 renewal for conversation data. An earlier separate Lean-based CAD application
  request retains its own jurisdiction; it does not authorize Lean inside Athena.
- Two Claude messages with a shared declared parent but different UUIDs, prompt IDs and revised
  wording. Both occurrences remain, with their actual shared-parent relationship.
- The contextual-transport correction, the distinction between a bounded resource fixture and
  repository language capability, and acceptance specifically of “integration” framing. None
  becomes blanket ratification or rejection of an agent's whole response.

[established-bounded; measured] Twenty-three focused tests passed. Full-source coordinate/count
checks returned no extent defects; 3,791 raw-record/coordinate comparisons matched the original
capture exactly, including every source boundary and the curated events. Every exported pair was
checked for the visible-role boundary, absent assigned loss/gold status and separate later
observations. Eight parent references and one tool return remain unresolved, with seven parent
candidate links retained; no source is selected merely to make the graph appear complete.

## Cultivation and machine transfer

[definition] The subsequent [Athena synthesis](ATHENA.md#athena-alpha-and-the-next-cultivation)
places this package in the general English, code and mathematics cultivation direction. It keeps
actual available ancestry, paired response and later human return distinct when mounting native
material. The preparation application supplies no native current by subtracting token IDs and no
Lean parser, kernel, theorem emitter or proof verdict participates in a downstream pipeline.

[definition] Git carries this guide and the preparation source; it does not carry the private
SQLite dataset or its JSONL exports. The planned desktop conversation campaign uses the refined
local artifacts above. A MacBook checkout has the source, documentation and imported research
evidence without transferring the retired side database. Private conversation data, model rests
and other ignored artifacts require separate intentional transfer if later needed there.

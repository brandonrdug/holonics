# Conversation data integration

**Authority:** Brandon's September 6 request to integrate/synthesize the foundation and refine
Claude Code/Codex conversation material. **Status:** completed data-preparation and curation pass. This does not
reactivate the inherited-first training campaign or schedule a model-training run.

[definition] The actual human user and responding agent supply the user-agent comparison. Tool
calls/results, delegation, recorded inference activity and client/harness events retain their own
relationships; they are not fabricated human feedback. A provider's `role=user` wrapper around a
tool result or child-agent prompt does not make Brandon its speaker. An agent response is an
observed response, not an automatically correct target. A later human message is not automatically
approval, rejection or correction. Preserve the circumstances in which those interpretations can
be made.

[definition] The sequence is: review the July/August conversation attempts and actual current
provider schemas; implement the smallest exterior package preserving source records, visible
messages, parent/turn/branch/tool relations and comparison candidates; provide overlapping
source-grounded curation and leakage-safe comparison/export views; then build and inspect the
actual local package with targeted role/branch/replay/control tests. Reuse A1/A2's relational
distinctions, not the parity spool or synthetic-user-feedback example. No native learner is
introduced by the packager.

[definition] The artifact is a private SQLite dataset with lossless compressed raw records,
separate normalized dialogue and runtime relations, captured source-prefix boundaries, and
source-addressed curation. SQLite/zlib/JSON are exterior storage codecs, not the native ontology
or a repository authority. The Python standard-library application belongs under `applications/`;
it avoids new ML/prover dependencies and provides a JSONL boundary for downstream consumers.
Raw logs and generated datasets stay under ignored `.local/`, never in the public Git commit.

[definition] Required controls distinguish human input from tool/user-role wrappers, agent
branches and copied context, assistant-visible text from reasoning/tool events, actual parentage
from serialization adjacency, repeated words from repeated representations, and later feedback
from earlier available context. Identical text does not merge occurrences. Missing/unavailable
data stays explicit. Semantic curation is source-supported exterior annotation, not an authored
interior relevance classifier or a scalar reward.

[definition] Lean text and recorded Lean tool activity remain ordinary corpus material. No Lean
parser, compiler, theorem emitter or verdict participates in preparation or defines the user-agent
loss. The package carries comparison operands and their relations; it does not replace situated
native difference with token-ID subtraction, edit distance, cosine similarity, provider ranking,
tool success, silence-as-approval or a hand-authored correctness target.

[definition] Completion requires the actual package, its documented use and privacy boundary,
historical findings, inspected representative exchanges/branches and passing focused data tests.
It is data integration/preparation, not a claim that a language model has been trained merely
because a corpus was parsed. NCF and the repository's standing language capabilities are retained.

[established-bounded; measured] The [completed return](../../research/records/2026-09-06_CONVERSATION_DATA_PRESERVES_USER_AGENT_DIFFERENCE_WITHOUT_A_PROVER_OR_SYNTHETIC_FEEDBACK.md)
and [artifact guide](../CONVERSATION_DATA.md#september-6-local-return) record the actual private
package, 30 grounded annotations, inspected exports and 23 passing focused tests. All required
data-preparation artifacts returned. This completed contract schedules no automatic training run.

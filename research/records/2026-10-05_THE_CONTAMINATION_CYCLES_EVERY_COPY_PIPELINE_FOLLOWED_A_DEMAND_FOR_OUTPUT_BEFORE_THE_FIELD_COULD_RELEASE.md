# The contamination cycles: every copy pipeline followed a demand for output before the field could release

**Date:** October 5, 2026. **Refs:** #63, #73, #148. **Grade:** [measured, history-read]. Commits and
mechanisms are read from git history. Agent attribution comes from commit trailers, and is marked
where it is inferred.

Brandon asked for a spot check of the "manually moving text snippet" pipeline, which had come back
several times. The audit read every commit since August, the antipattern and lessons records, the
current release paths on `9a62a685`, and Codex's unapplied packets of October 4–5. It records what
recurred and the guards that now exclude it ([THE_MACHINE](../../docs/THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible),
guards 18 and 19).

## The cycles

| Dates | Mechanism | Built by | Retired |
|---|---|---|---|
| Aug 3–5 | Authored conditioning: a linear scorer and a hard-coded seven-word morphology | Codex (inferred) | `2b562c85`, `797d1486` |
| Aug 10–11 | The production path emitted two-token prefixes of the corpus's own sentence openings | inherited from the laboratory | 2026-08-11 record |
| Aug 17–20 | A suffix-automaton walk that released only verbatim substrings (0 of 20 emissions composed); an atlas rebuilt from eight canon documents | Claude | `7146bd58` |
| Aug 23–25 | A lexical index choosing a stored response sentence per section by lexical intersection | Codex | `a7f26b62` |
| Aug 26–28 | `NativeRelationalCodec.surface_variants`: 256,100 stored phrasings rendered as output; receipts declared themselves lookup-free | Codex | partly `0a23b5ae`, `e3417f0f`; wholly at the reset |
| Sep 1 | HIF7: query byte-edges matched against stored presentation transitions | Codex | `1c51e574` (seven minutes later) |
| Sep 1–2 | `conduct_material` copied the selected observation into every fine occurrence; a world-return template emitter | Codex; Claude | `815c2e78`, `6962edfa`, `875da909` |
| Sep 5–9 | One contact column per observation: every exposed byte recoverable from the checkpoint | Codex | `76fece75` |
| Sep 21–22 | Response slots read old source cells; a retention contract that kept comparison cuts | Codex | `4c0a4165`; the reset |
| Sep 27 | The admitted egg's copy stage (the longest suffix of the response recurring in the request, copied); the sentence counter; a retrieval control in F5 | Claude (`9ad357fc`, `0fa7b39b`, `dfca47f0`) | `fbb9dee6`, `e214ccc8` |
| Sep 28 | The arithmetic calculator | Claude (`c17ea7bd`) | `be58a86d` |
| Sep 28–29 | Count-priced founding: a suffix-automaton context model priced by continuation counts | Claude (`32314569`); caught by Codex's review | `2dcbd5e2` |

Before the reset, seven of the eight copying pipelines were Codex's. After it, all were Claude's.
The release Brandon was shown on September 28 went through the September 27 copy stage.

## What recurred

- **The shape.** A receiving or release path matches the present context against stored seen
  material: sentences, clauses, substrings or spans of a request. A native name (atlas, codec,
  presentation transition, contact column, egg) makes it look like the field's own motion, while
  the current only selects what was stored. Exact apparatus receipts are then offered as evidence
  of learning: byte-identical remounts, exact readback, GPU parity, self-declared flags.
- **The pressure.** Every instance followed a demand for readable Athena output before the field
  could produce it. Neither model is immune: the agent under that pressure built it.
- **The re-entry.** Retiring an owner without retiring its claim brought the same form back within
  about a day, in a new owner.

## The state on `9a62a685` and in the October 4–5 packets

- No release path on `9a62a685` copies, looks up or selects seen text. `generate_by_bank` reads
  the request's phase-carried counts, the source port and the transport.
- The context-count tree is the receiving locus's storage (`hnn/constitution.rs`), and it earns
  the measured compression. The wave contributes `6 + 3/16` of about 3,460 bits on campaign 1's
  held-out cells. A text release drawn from it would recite seen continuations.
- F5's acceptance still put a retrieval control beside Athena's releases, side by side
  (`athena_blind.py`).
- Codex's unapplied `receive_class` (prospective receiving v1/v2, `reference/class.rs`) draws one
  class from the combined wave-and-tree face and re-ingests it as the next source cell: the
  one-cell emitter over the tree. It does not land.

## The exclusions

- **Guard 18** (structural): a release reads `FieldMaterial` alone, so the tree, the receiving
  map and the population are unreachable from `generate_by_bank`.
- **Guard 19**: one release per request, shown whole, with its copy length as a receipt.
- F5 loses the retrieval control. Brandon reads the releases whole, as they are.
- The context-count tree is an exterior yardstick. It leaves the constitution once lane A's locks
  carry the receiving storage ([THE_REBUILD U6, October 5](../../docs/plans/THE_REBUILD.md#u6-the-text-chart)).
- The likeliest re-entries are named so the next review checks them first:
  1. a text release drawn from the tree or its card mirror;
  2. an acceptance that rewards resemblance to recorded replies;
  3. units at the encoding boundary founded by substring counts (`hnn/encoding.rs` has no
     consumer yet; its units are founded by the field's keys, never priced by counts).

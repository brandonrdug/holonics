# Holonics research

Research supplies the mathematical objects and laws the library and HNN implement. Start with
[the machine](../docs/THE_MACHINE.md) and the [subject reading routes](records/README.md): each route
connects important records to its maintained guide, formal statements and executable consumers.
The [roadmap](../docs/plans/THE_ROADMAP.md) orders construction; research evidence does not create
a competing schedule.

| Read or produce | Where it lives |
|---|---|
| A derivation, design decision, source comparison or substantial result | [Dated records](records/README.md), with its source, hypotheses, receiver and evidence |
| A reproducible calculation or native/application run | [Experiments](experiments/README.md), retaining inputs, source revision, outputs, command and cost |
| A paper, expository diagram or composed mathematical argument | [Papers](papers/README.md), with editable Typst sources and rendered artifacts |
| Symbolic exploration, exercises and handwritten development | [Notebook](notebook/README.md), including its local Lean checks |
| Current definitions and implementation contracts | [Formal framework](../docs/FORMAL_FRAMEWORK.md), [model formula](../docs/HNN_FORMULA.md), [subject guides](../docs/REPOSITORY.md) and actual source |
| Earlier corrected capabilities or decisions | [Retraction history](../docs/RETRACTIONS.md), [portable source evidence](records/2026-09-06_REPOSITORY_SYNTHESIS_AND_PORTABLE_EVIDENCE.md), and the relevant record's chronological corrections |

A record can establish a theorem, a source-scoped calculation, a native execution result or an
interpretation to develop. Use its stated grade and evidence; directory placement does not decide
which it is. An experiment can expose a defect in library code, and a renderer can present an
actual generated face. Inspect the source-to-receiver operation rather than deciding from the
language, filename or image alone.

To recover a subject, read its route and the linked source record, then follow the named owners
and current callers. Search both the subject and its mathematical operations when extending it:

```bash
rg --files research/records | rg -i 'helic|torus|phase|contact'
.agents/bin/prior-art 'normalization|softmax|NormalizedKernel|pullback'
git log --follow -- research/records/<record>.md
```

When a return changes a reusable law, update its guide and consuming source and add the record to
its subject route. Preserve older evidence and explain the changed claim. The
[evidence protocol](../docs/AGENT_PROTOCOL.md) locates private conversation sources and how their
actual occurrences are recovered without publishing raw captures.

The old August-heavy thematic index is retained as a
[historical navigation snapshot](../archive/operations/RESEARCH_NAVIGATION_BEFORE_2026-09-20.md).
It is useful provenance; the routes above carry current mathematical context.

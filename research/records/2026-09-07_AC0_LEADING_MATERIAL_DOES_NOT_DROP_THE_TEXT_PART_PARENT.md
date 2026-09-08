# Leading material does not drop the text part's parent

[counterexample; source-inspected] The `alpha_text` exposure driver selected the parent by
the original part index, then skipped non-text parts. Consequently, a preceding image or
other unmounted material made the first admitted textual part enter without its otherwise
available parent. The same ordinary field operation supports that parent; the driver lost it.

[established-bounded; measured] A cold read of the prepared 36,920-family exposure stream
finds **48 development families with this susceptible part layout**. Early examples are
sequences `3067`, `5700` and `5715`. This count is about source layout, not a claim that all
48 were previously cultivated with an available native parent. The preserved four-family
and 128-family models do not reach these cases; this defect does not explain their failed text.

[established-bounded; measured] The driver now enumerates the parts admitted by its declared
text chart before identifying the first one. Original part ordinals and pointers remain in
the receipt. A completed or pending older inscription keeps its actual prior receiving
history; correcting future framing does not retrospectively relabel its first operation.
The image/material itself is still outside this text projection and is not claimed as mounted.

[established-bounded; measured] The native example regression passes. A leading material part
followed by text receives the actual parent at native occurrence `1`. A separate legacy-pending
control remains parentless as originally staged, and its receipt says so. The source reader,
native field, material map and current source capabilities are the standing public owners;
there is no fixture-local learner.

[established-bounded; measured] Both example regressions subsequently pass together in `16.99 s`,
including the existing actual-data partial-part checkpoint/resume control. That check uses the
prepared private exposure and compares the resumed state with its uninterrupted reference.

```text
cargo test -p holonics-hna --example alpha_text leading_nontext_material_preserves_the_available_native_parent -- --ignored --test-threads=1
/tmp/athena-leading-material-parent-test.log
HOLONICS_ALPHA_TEST_EXPOSURE=/home/b/Workspaces/holonics/.local/datasets/athena-alpha-exposure-source-context-2026-09-06.jsonl cargo test -p holonics-hna --example alpha_text -- --ignored --test-threads=1
/tmp/athena-text-framing-resume-tests.log
```

[definition] The existing private datasets, checkpoints and unrelated research files remain
unchanged. This is a source-framing repair, not an alpha-quality result or a new source of authority.

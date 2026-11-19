# Brief: find the guide and atlas text that tonight's Lean proofs made stale

The repository is the repository (brandonrdug/holonics). Read-only: do not edit, create or delete any file inside it, run
no build (`lake`, `cargo`), and change nothing in git. Write only your findings file (below).

On November 18 and 19 the Lean passes merged as #992 to #1006 proved statements that issue #410 had listed as owed. Your file
`boxes_<x>.md` (beside this brief) holds the #410 boxes those passes ticked, each with the module and declarations that prove it.

For each box, search the tree for text that still says the statement is owed, unproved, not formalized, "not in Lean", "named
open", "an open Prop", "#410" pending, or graded `open`/`interpretation` where the box's Lean now states it:

- `rg -n -i '<the statement's key names, the module path it names, its classical name>' docs/ CONSTRUCTION_STATE.md research/records/README.md`
- the atlas: `rg -n '<names>' docs/atlas/` (rows are tab-separated: id, objects, expr, reads, scope, owners, grade, rel; a row
  whose grade is `open` or `interpretation`, or whose scope says "owed", "not in Lean" or "#410", for a statement the box's
  module now proves, is a finding).
- Lean docstrings: `rg -n -i 'owed|not proved|named open|remains open|#410' lean/Holonics lean/HolonicsResearch` near the names
  the box gives (an older module whose header says the statement is owed while the new module proves it).

Do not report dated records under `research/records/2026-*` (they are readings of their day and stay as written), the canon
(`docs/canon/`), or text that is still true (a statement only partly proved where the text names the part still owed). Before you
report a line, open the proving Lean declaration the box names (`lean/HolonicsResearch/<path>.lean`) and confirm it states what the
stale text says is missing, under the same hypotheses; if it states less, say so and do not report it as stale.

## Output

Append one tab-separated line per finding to `findings_<x>.tsv` beside this brief, as soon as you decide it:

```
<file>:<line>	<the stale text, quoted, at most 300 characters>	<the box's PR and the Lean file:declaration that now states it>	<replacement text for that sentence or field, in the file's own style>
```

For an atlas row give the field name and its whole new value in the last column (`grade: formal-checked` with the new owner
`L:<Dir>/<File>:<decl>`, path relative to `lean/HolonicsResearch/` or `lean/Holonics/`, appended to the owners field). Keep the
style: terse, no "exact", never call text "wrong". When done append `# DONE boxes=<n> findings=<n>` and return a short summary.

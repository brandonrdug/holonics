# Brief: verify the atlas findings against the Lean source and write each row's repair

The repository is the repository (brandonrdug/holonics). A first pass of reviewers read the 2,501 atlas rows graded
`formal-checked` against the statements of their Lean owners, and listed the rows whose expr claims more than the owners state.
Their findings are receipts from one reading, made partly after a context summary. Some will not hold. Your task is to check each
finding against the Lean source yourself and write the repair the row needs.

This is read-only on the repository: do not edit, create or delete any file inside the repository, do not run `lake`,
`cargo` or any build, and do not change git. Write only your fix file (below).

Read once: `docs/atlas/README.md` (the row format: id, objects, expr, reads, scope, owners, grade, rel; `L:<Dir>/<File>:<decl>`
is a Lean declaration, the path relative to `lean/Holonics/` or `lean/HolonicsResearch/`), and `docs/canon/EPISTEMIC_GRADES.md`.
The findings files are tab-separated: row id, shard:line, class, owner, what the Lean states, what the row claims beyond it, the
reviewer's proposed fix, confidence.

## For each finding

1. Read the row in `docs/atlas/<shard>` (find it by its id; the line number may be off or missing).
2. Open each Lean owner's file and read the declaration and the definitions its statement uses. Search the same file and the
   module's neighbours (`rg -n '<name or notion>' lean/`) for a declaration that states the clause the finding says is missing.
3. Decide, in this order of preference:
   - `NOFIX`: the owners do state the row's claim (the finding misread a definition or a statement). Say what you read.
   - `OWNERS`: a live declaration states the missing clause. Add it to the owners field, as `L:<Dir>/<File>:<decl>` with the
     declaration's last name, after reading its statement and confirming it states the clause under the row's scope.
   - `NARROW`: no declaration states the clause. Rewrite expr (and reads, when it needs it) to what the owners state, and keep each
     clause the owners do not state in the scope field, prefixed `not in Lean:` (a count measured by a run is `measured:`, with
     its record if the row names one). Nothing the row says is dropped; it is placed under the status it has.
   - `SCOPE`: the Lean carries a hypothesis the scope does not name. Add it to scope in the row's own terse style.
   - `GRADE`: the row's central claim (not a side clause) is stated by no owner. Give the grade the evidence supports
     (`proved-derived` where a record or guide derives it, `interpretation` or `open` otherwise) and say why.
4. Keep the atlas's style: Unicode notation as the row already writes it, terse, no floats where the row has none, integers with
   their factorization where the row has them. Do not call anything "exact" and do not call a row or a proof "wrong". Do not change
   the id, objects or rel fields.

## Output

Append one line per finding, tab-separated, to your fix file `<scratch>/atlascheck/fixes/<name>.tsv`:

```
<row id>	<shard>	<NOFIX|OWNERS|NARROW|SCOPE|GRADE>	<field>	<the field's whole new value>	<what you read: file:line of each declaration that decided it>
```

`<field>` is one of `expr`, `reads`, `scope`, `owners`, `grade` (the whole field as it should stand, never a diff), or `-` for
`NOFIX`. A finding that changes two fields is two lines. For `owners`, write the whole field: every existing owner kept in its order,
the new ones appended, separated by `; `. Write each line as soon as you have decided it. When you finish, append
`# DONE findings=<n> nofix=<n> changed=<n>` and return a short summary with the repairs you are least sure of.

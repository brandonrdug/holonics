# Brief: do the atlas rows graded formal-checked say what their Lean statements say?

You are one reviewer among several, each on disjoint chunks. This is a read-only audit of the repository at
the repository (brandonrdug/holonics, the Holonics research programme). Do not edit, create or delete any file inside
the repository, do not run `lake`, `cargo` or any build, and do not use git to change anything. Write only your findings
file (below).

## What the atlas is

`docs/atlas/*.tsv` holds about 4,000 rows, one derived expression each. Fields: id, objects, `expr` (the expression in full),
`reads` (what it says in one clause), `scope` (its hypotheses and domain, tersely), owners (`L:<Dir>/<File>:<decl>` is a Lean
declaration, the path relative to `lean/Holonics/` or `lean/HolonicsResearch/`), grade, relations. Read
`docs/atlas/README.md` (row format) and `docs/canon/EPISTEMIC_GRADES.md` (the `formal-checked` tag: "a named proof kernel
accepted the declared formal statement") once.

The grade `formal-checked` claims that the row's statement (expr under scope, as `reads` glosses it) is what the Lean kernel
accepted. Every Lean owner below is already known to exist and to build (the whole package built tonight with no `sorry`). The
question is only whether the Lean statement(s) say what the row claims.

## Your input

Your chunk files are listed in your task. Each row appears as:

```
=== ROW <id>  (docs/atlas/<shard> line <n>)
expr: ...
reads: ...
scope: ...
grade: formal-checked
  OWNER <Dir>/<File>:<decl>  [<kind> <full name>]  proof starts: ...
    statement: <the declaration's binders and type, as text, up to :=>
```

The statement text is extracted by a script: it is the declaration's text from its name to `:=`, whitespace folded, and is cut
at 900 characters. Where the match depends on what a defined name means (a `def`, a `structure`, a predicate), open the Lean
source (`lean/Holonics/<Dir>/<File>.lean` or `lean/HolonicsResearch/<Dir>/<File>.lean`) and read the definitions before
deciding. Do not report a row on a guess about a definition you did not read.

## What to look for

Read every row in your chunks. A row matches when its owners' statements, taken together, state the row's expr under its scope.
Report only the rows that do not match, in these classes:

- `WEAKER`: the Lean states less than the row claims. Typical cases: the Lean is over `ℚ`, a finite type, a fixed size or a
  specific instance while the row reads as general; the Lean proves one direction where the row claims `⇔`; the row's expr has a
  conjunct, a bound or a uniqueness clause that no owner states; the row says "every" or "all" where the Lean has a witness.
- `SCOPE`: the Lean carries a hypothesis that the row's scope field does not name, and that hypothesis is not routine. A routine
  side condition (a nonzero denominator, `n ≥ 1`) missing from scope is `SCOPE-MINOR`. A hypothesis that carries the claim's own
  content (it assumes the thing the row says is shown, or assumes a target statement such as RH or a positivity it reads off) is
  `SCOPE` and is the most important kind to find.
- `DIFFERENT`: the Lean statement is about another quantity or object than the row names.
- `DEFINITION-ONLY`: the row claims a law (an equation, a bound, an equivalence) and its owners are only definitions or
  structures, with no theorem stating the law.
- `CHECK`: you cannot decide even after reading the source; say what would decide it.

Do not report wording, notation or style. A row whose expr writes `ℝ` where the Lean writes a field `𝕜` that includes `ℝ` matches.
A row that states less than its Lean matches.

## Output

Append findings, one per line, tab-separated, to your findings file `<scratch>/atlascheck/findings/<name>.tsv`
(create it at your first finding; `<scratch>` is `<scratch>`):

```
<row id>	<shard>:<line>	<class>	<owner decl>	<what the Lean states, one line>	<what the row claims beyond it, one line>	<proposed row fix: the narrowed expr/scope text, or a grade>	<high|medium>
```

Write each finding as soon as you have decided it, so nothing is lost if you stop. When you finish, append one last line
`# DONE rows_read=<count>` and return a short summary: rows read, findings by class, and the five findings you think matter most.
Keep the words plain: say what the Lean states and what the row claims beyond it. Do not call a statement "exact", and do not
call a row or a proof "wrong"; say what it claims beyond its owner.

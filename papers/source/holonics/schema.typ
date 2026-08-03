// Cold entry grammar for the dependency-ordered holonics synopsis.
// This file deliberately contains no page or publication styling.

#let allowed-grades = (
  "project-postulate",
  "definition",
  "identity",
  "proved-standard",
  "proved-derived",
  "conditional",
  "conjecture",
  "counterexample",
  "computational-witness",
  "historical-toy",
)

#let entry(
  id: none,
  kind: none,
  grade: none,
  title: none,
  statement: none,
  boundary: none,
  depends: (),
  derivation: none,
  transformations: none,
  receiver: none,
  source: none,
) = {
  assert(id != none, message: "entry id is required")
  assert(kind != none, message: "entry kind is required")
  assert(grade != none, message: "entry grade is required")
  assert(title != none, message: "entry title is required")
  assert(statement != none, message: "entry statement is required")
  assert(boundary != none, message: "entry boundary is required")
  assert(allowed-grades.contains(grade), message: "unknown epistemic grade: " + grade)
  (
    id: id,
    kind: kind,
    grade: grade,
    title: title,
    depends: depends,
    statement: statement,
    derivation: derivation,
    transformations: transformations,
    receiver: receiver,
    boundary: boundary,
    source: source,
  )
}

#let field(label, body) = {
  if body != none {
    block(breakable: true, inset: (left: 8pt), [
      #text(size: 7.5pt, weight: "bold", tracking: 0.06em, label)
      #h(0.8em)
      #body
    ])
  }
}

#let render-entry(e) = {
  heading(level: 3, outlined: true)[#e.id #h(0.6em) #e.title]
  text(size: 8pt, fill: rgb("#38414a"))[
    #e.kind · #e.grade
  ]
  if e.depends.len() > 0 {
    linebreak()
    text(size: 7.5pt, fill: rgb("#58636e"))[
      depends: #e.depends.join(", ")
    ]
  }
  v(4pt)
  field("statement", e.statement)
  field("derivation", e.derivation)
  field("transformations", e.transformations)
  field("receiver", e.receiver)
  field("boundary", e.boundary)
  field("source", e.source)
  v(9pt)
}

#let render-sequence(entries) = {
  for e in entries {
    render-entry(e)
  }
}

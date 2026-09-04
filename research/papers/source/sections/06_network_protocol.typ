#import "../lib/holonics.typ": *

#let network-protocol = [
#pagebreak(weak: true)
= Theory network and presentation protocol <network-protocol>

#local-contents((
  ([Dependency register], <protocol-dependencies>),
  ([Presentation protocol], <protocol-presentation>),
  ([Claim receipt], <protocol-claim>),
  ([Mathematical notation], <protocol-notation>),
  ([Figures], <protocol-figures>),
  ([Source and citation], <protocol-citation>),
  ([Reader notes], <protocol-notes>),
  ([Typst package policy], <protocol-packages>),
  ([Journal architecture], <protocol-architecture>),
  ([Source ledger for this volume], <protocol-ledger>),
  ([Present boundary], <protocol-boundary>),
))

The value of a foundation volume is not the number of analogies it can hold. It is whether a
reader can identify which definitions support which derivations, measurements, and open
questions. The following register is the initial theory network. Node identifiers are editorial
addresses, not new machine state.

== Dependency register <protocol-dependencies>

#figure(
  text(
    size: 8.5pt,
    table(
      columns: (3em, 1.2fr, 0.75fr, 1.1fr),
      inset: 4pt,
      stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
      table.header([*ID*], [*Relation*], [*Depends on*], [*Strongest current support*]),
      [D1], [actual occurrence], [-], [working definition],
      [D2], [oriented incidence and $partial^2=0$], [D1], [definition + exact proposition],
      [D3], [atomic event], [D1], [direct constraint + implementation],
      [D4], [RIDE / FOUND / OPEN], [D2, D3], [definition + bounded measurement],
      [D5], [relative completion], [D2, D3], [exact proposition + implementation],
      [D6], [receiver-exact compression], [D3, D5], [linear theorem + bounded implementation],
      [D7], [learning as changed later conduct], [D3, D4], [definition + matched measurements],
      [F1], [formal exponential generator], [D1], [exact formal derivation],
      [F2], [Euler prime-power exponential], [F1], [exact formal/convergent theorem],
      [F3], [homogeneous aperture recurrence], [F1], [exact theorem + measurement],
      [F4], [theta involution], [D4, F1], [exact finite derivation + measurement],
      [F5], [aperture-tail balance], [F4], [inherited Poisson law + measurement],
      [R1], [completed RH positivity carrier], [F2, F4, F5], [OPEN],
    ),
  ),
  caption: [Foundation and formula nodes in the initial dependency register.],
) <dependency-register-core>

#figure(
  text(
    size: 8.5pt,
    table(
      columns: (3em, 1.2fr, 0.75fr, 1.1fr),
      inset: 4pt,
      stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
      table.header([*ID*], [*Relation*], [*Depends on*], [*Strongest current support*]),
      [C1], [hypergraph/rewrite specialization], [D1-D5], [direct correspondence],
      [C2], [manifold/coarea specialization], [D2, D5], [external theorem + correspondence],
      [C3], [annular/fractal return], [D4, F1], [local exact match + bounded analogy],
      [C4], [Ricci/physics specialization], [D4, C2], [external theory + typed bridge],
      [L1], [neural realization versus relation], [D4, D6], [derivation + ML comparison],
      [L2], [source-departed inherited law], [D3, D7], [exact measurement],
      [L3], [cultivation and local completion], [L1, L2], [exact bounded measurement],
      [M1], [machine-owned successor], [D3], [source + test evidence],
      [M2], [world consequence and rest], [M1], [host/CUDA measurement],
      [M3], [outgoing physical factor], [D5, D6, M1], [bounded host measurement],
    ),
  ),
  caption: [Comparative, learning, and machine nodes. A later paper may refine a node but must not
  silently change the meaning of its dependencies.],
) <dependency-register-applications>

The graph prevents three recurrent mistakes. First, a measured special case cannot become the
definition on which it depends. Second, a comparison cannot promote itself into an exact
cross-domain identity. Third, an open global bridge cannot borrow closure from several exact local
lemmas whose missing composition has not been proved.

== Presentation protocol <protocol-presentation>

Every substantive section begins by fixing four things in ordinary prose:

1. the exact question;
2. why standing evidence cannot already answer it;
3. the smallest qualitative observable or artifact sought; and
4. the stopping condition.

The manuscript then uses ordinary mathematical exposition. Provenance boxes are reserved for
places where authorship, source route, or an open boundary would otherwise be ambiguous. The page
does not become a dashboard.

The front outline exposes headings through level three. Every major journal part begins with a
compact local map of its named subsections. Both are hyperlinks in the digital artifact; neither
duplicates claims or evidence. The global outline answers “where is this relation?” while the
local map answers “what distinctions organize this part?”

=== Claim receipt <protocol-claim>

A load-bearing claim must let a reader recover:
$
  ("author", "body", "Current", "Standing", "source", "receiver"),
$
$
  ("frame", "grain", "grade", "support", "foil", "open boundary").
$
These fields may be distributed across prose, theorem, caption, and source note. They should not
be repeated ceremonially. The first substantial use of a measurement carries the complete
receipt; later uses link back.

=== Mathematical notation <protocol-notation>

Exact analytical structure uses integers, rational numbers, algebraic values, formal series, or
declared analytic limits. Floating-point geometry may render testimony but cannot become causal
evidence. The five judgments in J1 remain visually distinct. A symbol acquires a receiver,
frame, grain, aperture, or source index whenever changing that index can change the result.

Theorem-family labels are bold and their bodies are roman. Italic is reserved for a term being
defined, ordinary emphasis, variables, and the proof label; it does not wash across an entire
definition, lemma, corollary, proposition, axiom, theorem, or open problem.

`RIDE`, `FOUND`, and `OPEN` are reserved words. “Residual” names either the complete path pair or a
projection in a declared chart. “Holon,” “manifold,” “field,” “expert,” “probability,” “loss,” and
“memory” never carry an unindexed universal meaning.

=== Figures <protocol-figures>

Every figure caption states what kind of figure it is:

- *formal:* exact consequence of written definitions;
- *causal:* actual event incidence or measured lifecycle;
- *observer:* projection or testimony from exact material;
- *comparison:* an explicit map between domains; or
- *hypothesis:* a proposed, unmeasured relation.

The relational vector grammar uses four primitives: nodes for supplied occurrences, lines for
declared incidence or transport, polygonal faces for one captioned geometric role, and dashed
lines for a named receiver quotient, world passage, proposed bridge, or OPEN comparison.
Position, proximity, size, and color do not create identity, chronology, or incidence. Actual order
requires an arrow and a source chronology. Actual sharing is rendered as one shared occurrence;
equal disconnected faces remain plural. A triangle names whether it is boundary, comparison,
rewrite hinge, abstract simplex, or geometric realization. Accessibility is redundant: labels and
line styles carry every distinction made visually.

=== Source and citation <protocol-citation>

Primary papers, canonical texts, official documentation, and exact laboratory artifacts carry
theorem, architecture, and measurement claims. Visual explainers such as 3Blue1Brown are cited
for explanatory lineage and intuition. Wolfram Physics supplies an explicit comparison target for
hypergraph rewriting and event causality; it does not make Eros a Wolfram model. A mutable web
source records version or access date when it bears a substantive claim.

Internal records are routed through the current `src/soma/README.md` relation. Dated research
deposits preserve derivation and authorship; they are not presumed current merely because they are
newer. A superseded interpretation may be cited as provenance only alongside its correction.

=== Reader notes <protocol-notes>

Typst `//` comments are private editorial notes and do not render. A visible reader note carries
an author and a disposition: `open`, `answered`, `incorporated`, `rejected`, or `parked`.
Incorporation moves the idea into prose with its proper provenance. It does not turn a provisional
question into a theorem.

#reader-note(author: [Brandon], status: [open])[
  This space is intentionally available for objections, alternate derivations, missing sources,
  and requests to split or merge a theory node. A note remains visibly yours until you decide its
  disposition.
]

== Typst package policy <protocol-packages>

The page grammar is owned by `unequivocal-ams` 0.1.2: US-letter AMS margins, New Computer Modern,
numbered sections, and theorem/proof treatment. The local library does not override its page or
heading system. It supplies the journal's roman theorem-family body, global/local navigation,
repeated holonic notation, restrained provenance notes, and Fletcher diagrams.

#figure(
  table(
    columns: (7.5em, 5.2em, 1fr),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Package*], [*Policy*], [*Jurisdiction*]),
    [`unequivocal-ams` 0.1.2], [foundation], [page, theorem, proof, bibliography],
    [`fletcher` 0.5.8], [active], [commuting diagrams, incidence, dependency; wrapped locally],
    [`quill` 0.7.3], [conditional], [only specified qubits, gates, wires, and measurements],
    [`typed-dsa` 0.3.1], [conditional], [declared algorithms and external data structures],
    [`typed-smiles` 0.8.0], [conditional], [source-declared chemical structures and reactions],
  ),
  caption: [Package policy. Optional packages enter only when a real paper uses their native
  semantics.],
) <package-policy>

`Quill` is not a generic metaphor for quantum relation. `typed-dsa` may render an exact data
structure but cannot infer causal incidence. `typed-smiles` supplies chemistry-world technology;
a SMILES string or rendered molecule is not Soma ontology. A local wrapper is added only after two
or more manuscripts repeat a semantic need.

#pagebreak(weak: true)
== Journal architecture <protocol-architecture>

The five streams remain topical receivers:

#figure(
  table(
    columns: (4.2em, 1.1fr, 1.6fr),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Stream*], [*Core question*], [*First paper family*]),
    [J1], [What is the minimal calculus?], [Occurrence, event, comparison, completion, compression],
    [J4], [How do finite formula faces grow?], [Exponential/Euler apertures and theta boundary],
    [J5], [Which cross-domain maps survive?], [Typed geometry, physics, life, and culture atlas],
    [J3], [What counts as learning?], [Inherited ecology, retriangulation, and parent-on-OPEN],
    [J2], [What did the machine establish?], [Atomic owner, world return, rest, and physical factor],
  ),
  caption: [Standing journal streams in the requested development order. They are not a work
  queue.],
) <journal-streams>

Future entries should use:

```text
entries/YYYY-MM-DD_slug/
  entry.typ
  figures.typ
  notes.typ

research/papers/short-title/
  main.typ
  sections/
  figures/
  references.bib
```

An entry is authored once and may be referenced from several streams. The source directory,
Formula, research deposits, and observation artifacts remain the claim substrate. `PAPERS/` is a
reading and publication surface, not a second owner or scheduler.

#pagebreak(weak: true)
== Source ledger for this volume <protocol-ledger>

#figure(
  table(
    columns: (4em, 1.2fr, 1.4fr),
    inset: 4pt,
    stroke: (x: none, y: 0.35pt + rgb("#E7E7E7")),
    table.header([*Code*], [*Use*], [*Decisive internal route*]),
    [S1], [claim routing], [README],
    [S2], [foundational mechanics], [Elementary Mechanics],
    [S3], [historical/formal spine], [Formula],
    [S4], [mathematical analogy catalog], [Theory Map],
    [S5], [formula generator], [Infinite Formula],
    [S6], [aperture recurrence], [Aperture Grows],
    [S7], [rewrite/triangle derivation], [Hypergraph / Triangle],
    [S8], [scale-turn derivation], [Annulus],
    [S9], [hyperarea/receiver derivation], [Hyperarea],
    [S10], [Ricci/physics derivation], [Ricci Trace],
    [S11], [ML interpretation correction], [Network Is One Realization],
    [S12], [machine owner correction], [Event Emanates Successor],
    [O], [bounded measurements], [Observation RESULTS cited in place],
  ),
  caption: [Internal source ledger. Descriptive links at first use point to the complete paths;
  abbreviations here keep the table readable.],
) <source-ledger>

== Present boundary <protocol-boundary>

This foundation is intentionally nonfinal. It now supplies what the first prospectus lacked:
typed definitions, reusable derivations, exact evidence cuts, cross-domain non-equivalences, and a
dependency network. Its immediate open work is scholarly rather than rhetorical:

- formal semantics and countermodels for the calculus;
- arbitrary-degree covariance for formula apertures;
- the completed RH trace and positivity carrier;
- boundary-preserving neural retriangulation with physical cost;
- grounded later consequence outside retained transformer faces;
- general confluence and device-resident cellular execution; and
- domain-specific physical predictions with units and falsifying controls.

None is scheduled by appearing in this list. Each becomes active only when a present question
selects its README evidence route and fixes a new stopping condition.
]

#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge

// A deliberately small monochrome layer over unequivocal-ams.
// It supplies only repeated holonic notation and evidence conventions.

#let rule-gray = rgb("#777777")
#let light-gray = rgb("#E7E7E7")
#let open-gray = rgb("#555555")

#let statement(supplement, body, numbered: true) = figure(
  // The AMS template italicizes theorem figures by default. The journal's statements are often
  // paragraph-length definitions with several semantic emphases, so an explicit roman body keeps
  // those emphases visible and lets the bold statement label carry the hierarchy.
  text(style: "normal", body),
  kind: "theorem",
  supplement: supplement,
  numbering: if numbered { n => counter(heading).display() + [#n] },
)

#let definition(body, numbered: true) = statement([Definition], body, numbered: numbered)
#let axiom(body, numbered: true) = statement([Axiom], body, numbered: numbered)
#let proposition(body, numbered: true) = statement([Proposition], body, numbered: numbered)
#let lemma(body, numbered: true) = statement([Lemma], body, numbered: numbered)
#let corollary(body, numbered: true) = statement([Corollary], body, numbered: numbered)
#let open-problem(body, numbered: true) = statement([Open problem], body, numbered: numbered)

#let roman-statement(it) = block(spacing: 11.5pt, {
  set align(start)
  strong({
    it.supplement
    if it.numbering != none {
      [ ]
      it.counter.display(it.numbering)
    }
    [.]
  })
  [ ]
  it.body
})

#let remark(body) = block(spacing: 10pt)[
  #emph[Remark.]
  #h(5pt)
  #body
]

#let provenance(kind: [Provenance], source: none, body: none, boundary: none) = block(
  width: 100%,
  stroke: (left: 0.7pt + rule-gray),
  inset: (left: 9pt),
  above: 8pt,
  below: 8pt,
  breakable: true,
)[
  #set par(first-line-indent: 0pt, spacing: 0.35em)
  #text(size: 8.5pt)[
    #smallcaps[#kind.]
    #h(4pt)
    #body
    #if source != none [
      #linebreak()
      #emph[Source route.]
      #h(3pt)
      #source
    ]
    #if boundary != none [
      #linebreak()
      #emph[Open boundary.]
      #h(3pt)
      #boundary
    ]
  ]
]

#let source-note(body) = provenance(
  kind: [Source route],
  body: body,
)

#let evidence-note(claim, grade, support, limit) = provenance(
  kind: [Evidence receipt],
  body: [
    #emph[Claim.]
    #h(3pt)
    #claim
    #linebreak()
    #emph[Grade.]
    #h(3pt)
    #grade
    #linebreak()
    #emph[Support.]
    #h(3pt)
    #support
  ],
  boundary: limit,
)

#let reader-note(author: [Brandon], status: [open], body) = block(
  width: 100%,
  stroke: (top: 0.5pt + rule-gray, bottom: 0.5pt + rule-gray),
  inset: (y: 7pt),
  above: 10pt,
  below: 10pt,
)[
  #set par(first-line-indent: 0pt)
  #text(size: 8.5pt)[
    #smallcaps[Reader note - #author (#status).]
    #h(5pt)
    #body
  ]
]

#let local-contents(entries, title: [Contents of this part]) = {
  let cells = ()
  for entry in entries {
    cells.push(
      link(entry.at(1))[
        #text(size: 8.1pt)[#entry.at(0)]
      ]
    )
  }

  block(
    width: 100%,
    stroke: (top: 0.5pt + rule-gray, bottom: 0.5pt + rule-gray),
    inset: (y: 7pt),
    above: 7pt,
    below: 15pt,
    breakable: false,
  )[
    #set par(first-line-indent: 0pt)
    #text(size: 7.8pt, fill: rule-gray)[#smallcaps[#title]]
    #v(4pt)
    #grid(
      columns: (1fr, 1fr),
      column-gutter: 1.4em,
      row-gutter: 3.5pt,
      ..cells,
    )
  ]
}

#let notation-table(rows) = figure(
  table(
    columns: (9em, 1fr),
    inset: (x: 5pt, y: 3.5pt),
    stroke: (x: none, y: 0.35pt + light-gray),
    align: (left, left),
    table.header([*Notation*], [*Meaning and jurisdiction*]),
    ..rows,
  ),
  caption: [Core notation. Every symbol is indexed by a declared receiver, frame, or boundary
  when that index can change the result.],
)

#let dependency-figure() = figure(
  placement: none,
  text(
    size: 8.2pt,
    fletcher.diagram(
      node-stroke: 0.65pt + black,
      edge-stroke: 0.85pt + black,
      spacing: (3em, 3.1em),
      node((0, 0), [Occurrence], width: 5.8em),
      edge((0, 0), (1, 0), "-|>"),
      node((1, 0), [Boundary], width: 5.8em),
      edge((1, 0), (2, 0), "-|>"),
      node((2, 0), [Event], width: 5.8em),
      edge((2, 0), (3, 0), "-|>"),
      node((3, 0), [Standing], width: 5.8em),
      edge((0, 0), (0, 1), "-|>"),
      node((0, 1), [Chain], width: 5.8em),
      edge((0, 1), (1, 1), "-|>"),
      node((1, 1), [Comparison], width: 5.8em),
      edge((1, 1), (2, 1), "-|>"),
      node((2, 1), [Compression], width: 5.8em),
      edge((2, 1), (3, 1), "-|>"),
      node((3, 1), [Learning], width: 5.8em),
      edge(
        (1, 1),
        (2, 2),
        "dashed",
        label: [open],
        stroke: (paint: open-gray, thickness: 0.85pt, dash: "dashed"),
      ),
      node((2, 2), [Global bridges], width: 6.4em),
    ),
  ),
  caption: [Dependency graph of the foundation. Solid arrows are definitions or exact local
  constructions developed here. The dashed arrow collects distinct analytic and physical
  obligations which are not supplied by the calculus.],
)

#let event-figure() = figure(
  placement: none,
  text(
    size: 8.2pt,
    fletcher.diagram(
      node-stroke: 0.65pt + black,
      edge-stroke: 0.85pt + black,
      spacing: (3.1em, 3em),
      node((0, 0), [Current $K_t$], width: 6em),
      node((0, 1), [Standing $S_t$], width: 6em),
      edge((0, 0), (1, 0.5), "-|>"),
      edge((0, 1), (1, 0.5), "-|>"),
      node((1, 0.5), [Event $Lambda_e$], width: 6em),
      edge((1, 0.5), (2, 0), "-|>", [commit]),
      edge((1, 0.5), (2, 1), "-|>", [radiate]),
      node((2, 0), [Successor $S_(t^+)$], width: 6.5em),
      node((2, 1), [Immediate $R_e$], width: 6.5em),
      edge((2, 1), (3, 1), "dashed", label: [world]),
      node((3, 1), [Later consequence], width: 6.5em),
      edge((3, 1), (3, 0), "-|>", [new current]),
      node((3, 0), [Changed conduct], width: 6.5em),
    ),
  ),
  caption: [One event and its later causal circuit. Immediate radiation and a genuinely later
  world consequence are different cuts.],
)

#let open-square() = figure(
  placement: none,
  fletcher.diagram(
    node-stroke: 0.65pt + black,
    edge-stroke: 0.85pt + black,
    spacing: (5em, 3.3em),
    node((0, 0), [$x$], radius: 1.05em),
    edge((0, 0), (1, 0), "-|>", [$r_1$]),
    node((1, 0), [$y$], radius: 1.05em),
    edge((0, 0), (0, 1), "-|>", [$u$]),
    node((0, 1), [$x'$], radius: 1.05em),
    edge((0, 1), (1, 1), "-|>", [$r_2$]),
    node((1, 1), [$y'$], radius: 1.05em),
    edge((1, 0), (1, 1), "-|>", [$v$]),
    edge(
      (0, 0),
      (1, 1),
      "dashed",
      label: [$Chi = (v compose r_1, r_2 compose u)$],
      stroke: (paint: open-gray, thickness: 0.85pt, dash: "dashed"),
    ),
  ),
  caption: [A complete path comparison. Equality may close the square; otherwise both routes
  remain material and the comparison is OPEN at this receiver.],
)

#let boundary-transfer-figure() = figure(
  placement: none,
  fletcher.diagram(
    node-stroke: 0.65pt + black,
    edge-stroke: 0.85pt + black,
    spacing: (5.1em, 3.1em),
    node((0, 0), [$P_(d,N)$], width: 5.6em),
    edge((0, 0), (1, 0), "-|>", [$+2d_(N+1)$]),
    node((1, 0), [$P_(d,N+1)$], width: 6.4em),
    node((0, 1), [$T_(d,N)$], width: 5.6em),
    edge((0, 1), (1, 1), "-|>", [$-2d_(N+1)$]),
    node((1, 1), [$T_(d,N+1)$], width: 6.4em),
    edge((0, 0), (0, 1), "dashed", label: [$C_d=P+T$]),
    edge((1, 0), (1, 1), "dashed", label: [$C_d=P+T$]),
  ),
  caption: [Aperture growth transfers one boundary constituent from the generative remainder
  into the participating face. The complete chart is unchanged.],
)

#let relation-cell-figure() = figure(
  placement: none,
  text(
    size: 8pt,
    fletcher.diagram(
      node-stroke: 0.65pt + black,
      edge-stroke: 0.85pt + black,
      spacing: (3.2em, 2.8em),
      node((0, 0), [$a_0$], radius: 0.9em),
      node((0, 1), [$a_1$], radius: 0.9em),
      node((0, 2), [$a_2$], radius: 0.9em),
      edge((0, 0), (1, 1), "-|>"),
      edge((0, 1), (1, 1), "-|>"),
      edge((0, 2), (1, 1), "-|>"),
      node((1, 1), [relation $lambda$], width: 6.6em),
      edge((1, 1), (2, 0.5), "-|>"),
      edge((1, 1), (2, 1.5), "-|>"),
      node((2, 0.5), [$c_0$], radius: 0.9em),
      node((2, 1.5), [$c_1$], radius: 0.9em),
      edge((2, 1.5), (3, 1.5), "dashed", label: [world]),
      node((3, 1.5), [later $k'$], width: 5.2em),
      edge((3, 1.5), (3, 0.5), "-|>", [returns]),
      node((3, 0.5), [available Standing], width: 6.8em),
      edge(
        (1, 1),
        (1, 2.35),
        "dashed",
        label: [receiver $rho$],
        stroke: (paint: open-gray, thickness: 0.8pt, dash: "dashed"),
      ),
      node((1, 2.35), [face $F_rho(lambda)$], width: 6.8em),
    ),
  ),
  caption: [Relational diagram grammar. Antecedents meet in one actual relation occurrence;
  immediate consequents emanate; only a later world return can re-enter as Current. The dashed
  receiver edge is a presentation of the relation, not another causal owner.],
)

#let simplex-face-figure() = figure(
  placement: none,
  text(
    size: 7.8pt,
    fletcher.diagram(
      node-stroke: 0.6pt + black,
      edge-stroke: 0.8pt + black,
      spacing: (3.1em, 2.9em),

      // Convex face.
      node((0, 0), [$v_0$], radius: 0.78em),
      node((1.35, 0), [$v_1$], radius: 0.78em),
      node((0.68, -1.15), [$v_2$], radius: 0.78em),
      edge((0, 0), (1.35, 0), "-"),
      edge((1.35, 0), (0.68, -1.15), "-"),
      edge((0.68, -1.15), (0, 0), "-"),
      node((0.69, -0.38), [$o$], radius: 0.62em),
      edge((0, 0), (0.69, -0.38), "dashed", label: [$alpha_0$]),
      edge((1.35, 0), (0.69, -0.38), "dashed", label: [$alpha_1$]),
      edge((0.68, -1.15), (0.69, -0.38), "dashed", label: [$alpha_2$]),

      // Glued complex.
      node((2.75, 0), [$p_0$], radius: 0.72em),
      node((4.05, 0), [$p_1$], radius: 0.72em),
      node((3.4, -1.12), [$p_2$], radius: 0.72em),
      node((3.4, 1.12), [$p_3$], radius: 0.72em),
      edge((2.75, 0), (4.05, 0), "-", [shared face]),
      edge((2.75, 0), (3.4, -1.12), "-"),
      edge((4.05, 0), (3.4, -1.12), "-"),
      edge((2.75, 0), (3.4, 1.12), "-"),
      edge((4.05, 0), (3.4, 1.12), "-"),

      node((0.68, 1.15), [convex participation], stroke: none),
      node((3.4, 1.72), [actual gluing], stroke: none),
    ),
  ),
  caption: [Two structures which drawings often blur. Left: a receiver output is a barycentric
  point of the admitted values when the coefficients are nonnegative and sum to one. Right: a
  simplicial complex requires actual common-face incidence; geometric overlap alone is
  insufficient.],
)

#let retriangulation-figure() = figure(
  placement: none,
  text(
    size: 7.8pt,
    fletcher.diagram(
      node-stroke: 0.6pt + black,
      edge-stroke: 0.85pt + black,
      spacing: (3em, 2.8em),

      node((0, 0), [$a$], radius: 0.72em),
      node((1.4, 0), [$b$], radius: 0.72em),
      node((1.15, -1.2), [$c$], radius: 0.72em),
      node((-0.2, -0.95), [$d$], radius: 0.72em),
      edge((0, 0), (1.4, 0), "-"),
      edge((1.4, 0), (1.15, -1.2), "-"),
      edge((1.15, -1.2), (-0.2, -0.95), "-"),
      edge((-0.2, -0.95), (0, 0), "-"),
      edge((0, 0), (1.15, -1.2), "-"),

      edge((1.65, -0.55), (2.45, -0.55), "-|>", [$2 -> 2$]),

      node((2.75, 0), [$a$], radius: 0.72em),
      node((4.15, 0), [$b$], radius: 0.72em),
      node((3.9, -1.2), [$c$], radius: 0.72em),
      node((2.55, -0.95), [$d$], radius: 0.72em),
      edge((2.75, 0), (4.15, 0), "-"),
      edge((4.15, 0), (3.9, -1.2), "-"),
      edge((3.9, -1.2), (2.55, -0.95), "-"),
      edge((2.55, -0.95), (2.75, 0), "-"),
      edge((4.15, 0), (2.55, -0.95), "-"),
    ),
  ),
  caption: [The two-dimensional bistellar move. The exterior quadrilateral is retained while the
  interior diagonal changes. Preserving topology is supplied by the move's hypotheses; preserving
  transport, metric, or physical cost requires separate comparison.],
)

#let star-link-figure() = figure(
  placement: none,
  text(
    size: 7.8pt,
    fletcher.diagram(
      node-stroke: 0.55pt + black,
      edge-stroke: 0.75pt + black,
      spacing: (2.75em, 2.75em),
      node((0, 0), [$p$], radius: 0.72em),
      node((0, -1.45), [$v_0$], radius: 0.68em),
      node((1.25, -0.72), [$v_1$], radius: 0.68em),
      node((1.25, 0.72), [$v_2$], radius: 0.68em),
      node((0, 1.45), [$v_3$], radius: 0.68em),
      node((-1.25, 0.72), [$v_4$], radius: 0.68em),
      node((-1.25, -0.72), [$v_5$], radius: 0.68em),
      edge((0, 0), (0, -1.45), "-"),
      edge((0, 0), (1.25, -0.72), "-"),
      edge((0, 0), (1.25, 0.72), "-"),
      edge((0, 0), (0, 1.45), "-"),
      edge((0, 0), (-1.25, 0.72), "-"),
      edge((0, 0), (-1.25, -0.72), "-"),
      edge((0, -1.45), (1.25, -0.72), "-"),
      edge((1.25, -0.72), (1.25, 0.72), "-"),
      edge((1.25, 0.72), (0, 1.45), "-"),
      edge((0, 1.45), (-1.25, 0.72), "-"),
      edge((-1.25, 0.72), (-1.25, -0.72), "-"),
      edge((-1.25, -0.72), (0, -1.45), "-"),
      node((2.05, 0.55), [$"St"(p)$: incident cells], stroke: none),
      node((2.05, -0.15), [$"Lk"(p)$: opposite boundary], stroke: none),
      node((2.05, -0.85), [receiver cut selects a face], stroke: none),
      edge(
        (1.25, 0.72),
        (2.05, 0.55),
        "dashed",
        stroke: (paint: open-gray, thickness: 0.75pt, dash: "dashed"),
      ),
      edge(
        (1.25, -0.72),
        (2.05, -0.15),
        "dashed",
        stroke: (paint: open-gray, thickness: 0.75pt, dash: "dashed"),
      ),
    ),
  ),
  caption: [A local star and link. The star records the simplices incident to the selected
  occurrence; the link records the boundary seen opposite it. Either is a useful receiver-local
  chart, but neither is the complete ecology.],
)

#let scale-turn-figure() = figure(
  placement: none,
  text(
    size: 7.6pt,
    fletcher.diagram(
      node-stroke: 0.55pt + black,
      edge-stroke: 0.75pt + black,
      spacing: (2.7em, 2.7em),

      node((0, -1.2), [$u_0$], radius: 0.62em),
      node((0, -0.4), [$u_1$], radius: 0.62em),
      node((0, 0.4), [$u_2$], radius: 0.62em),
      node((0, 1.2), [$u_3$], radius: 0.62em),
      edge((0, -1.2), (0, -0.4), "-|>"),
      edge((0, -0.4), (0, 0.4), "-|>"),
      edge((0, 0.4), (0, 1.2), "-|>"),
      node((0.75, 0), [logarithmic lift $w=u+i theta$], stroke: none),

      edge((1.6, 0), (2.45, 0), "-|>", [$exp$]),

      node((3.25, 0), [], radius: 2em),
      node((3.25, 0), [], radius: 1.05em),
      node((3.25, -0.95), [$z_0$], radius: 0.58em),
      node((4.15, -0.25), [$z_1$], radius: 0.58em),
      node((3.8, 0.78), [$z_2$], radius: 0.58em),
      node((2.65, 0.82), [$z_3$], radius: 0.58em),
      edge((3.25, -0.95), (4.15, -0.25), "-|>"),
      edge((4.15, -0.25), (3.8, 0.78), "-|>"),
      edge((3.8, 0.78), (2.65, 0.82), "-|>"),
      edge((2.65, 0.82), (3.25, -0.95), "dashed", label: [return]),
      node((3.25, 1.6), [annular face: scale + turn], stroke: none),
    ),
  ),
  caption: [The scale-turn chart. Translation in the logarithmic lift becomes simultaneous radial
  scaling and angular return under exponentiation. A drawn recurrence becomes evidence only when
  the return map, receiver landmarks, multiplier, and residual are supplied.],
)

#let attention-geometry-figure() = figure(
  placement: none,
  text(
    size: 7.7pt,
    fletcher.diagram(
      node-stroke: 0.6pt + black,
      edge-stroke: 0.8pt + black,
      spacing: (3.15em, 2.8em),
      node((0, 0), [$v_1$], radius: 0.78em),
      node((1.65, 0), [$v_2$], radius: 0.78em),
      node((0.83, -1.45), [$v_3$], radius: 0.78em),
      edge((0, 0), (1.65, 0), "-"),
      edge((1.65, 0), (0.83, -1.45), "-"),
      edge((0.83, -1.45), (0, 0), "-"),
      node((0.83, -0.5), [$o_i$], radius: 0.64em),
      edge((0, 0), (0.83, -0.5), "-|>"),
      edge((1.65, 0), (0.83, -0.5), "-|>"),
      edge((0.83, -1.45), (0.83, -0.5), "-|>"),
      node((0.83, 0.65), [$o_i=sum_j alpha_(i,j)v_j$], stroke: none),

      edge((1.98, -0.65), (2.82, -0.65), "-|>", [context changes]),

      node((3.15, 0), [$v'_1$], radius: 0.78em),
      node((4.8, 0), [$v'_2$], radius: 0.78em),
      node((3.98, -1.45), [$v'_4$], radius: 0.78em),
      edge((3.15, 0), (4.8, 0), "-"),
      edge((4.8, 0), (3.98, -1.45), "-"),
      edge((3.98, -1.45), (3.15, 0), "-"),
      node((3.98, -0.5), [$o'_i$], radius: 0.64em),
      edge((3.15, 0), (3.98, -0.5), "-|>"),
      edge((4.8, 0), (3.98, -0.5), "-|>"),
      edge((3.98, -1.45), (3.98, -0.5), "-|>"),
      node((3.98, 0.65), [new admitted face], stroke: none),
    ),
  ),
  caption: [Attention as event-local barycentric transport. Context can change the query, keys,
  values, admitted population, and therefore the realized simplex itself. The picture does not
  identify a token, value vector, neuron, or attention coefficient with a stable meaning.],
)

#let architecture-axes-figure() = figure(
  placement: none,
  text(
    size: 7.55pt,
    fletcher.diagram(
      node-stroke: 0.6pt + black,
      edge-stroke: 0.8pt + black,
      spacing: (3em, 2.7em),

      node((0, 0), [sequence carrier], width: 7.2em),
      edge((0, 0), (1, 0), "-|>"),
      node((1, 0), [KDA Standing], width: 6.2em),
      edge((1, 0), (2, 0), "-|>"),
      node((2, 0), [context output], width: 6.8em),
      node((3, 0), [longitudinal incidence], stroke: none),

      node((0, 1), [prior layers], width: 7.2em),
      edge((0, 1), (1, 1), "-|>"),
      node((1, 1), [AttnRes], width: 6.2em),
      edge((1, 1), (2, 1), "-|>"),
      node((2, 1), [later layer], width: 6.8em),
      node((3, 1), [depth incidence], stroke: none),

      node((0, 2), [token carrier], width: 7.2em),
      edge((0, 2), (1, 2), "-|>"),
      node((1, 2), [router], width: 6.2em),
      edge((1, 2), (2, 1.6), "-|>"),
      edge((1, 2), (2, 2.4), "-|>"),
      node((2, 1.6), [shared branch], width: 7.6em),
      node((2, 2.4), [expert set], width: 7.6em),
      node((3, 2), [family incidence], stroke: none),
    ),
  ),
  caption: [Three independent architectural incidence axes in the public Kimi K3 account:
  longitudinal state across sequence, selective residual transport across depth, and sparse
  transformation-family routing. The diagram is a typed comparison, not a claim that these
  mechanisms are one universal holonic primitive.],
)

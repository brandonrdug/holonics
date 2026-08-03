#import "@preview/cetz:0.3.4"

// A native Typst proof language inspired by Oliver Byrne's geometric method.
// The implementation is original: it borrows the compositional idea that one
// colored construction should recur in the main figure, inline reasoning, and
// equations. Textual labels remain present so color is never the sole address.

#let by-red = rgb("#D94D1A")
#let by-blue = rgb("#265999")
#let by-yellow = rgb("#E3A511")
#let by-black = rgb("#171717")
#let by-paper = rgb("#F7F1E3")
#let by-pale = rgb("#EFE5CF")
#let by-rule = rgb("#C8BDA4")
#let by-muted = rgb("#706858")
#let by-open = rgb("#8C4651")

#let element-counter = counter("holonic-element")

#let colored-term(color, body) = text(fill: color, weight: "semibold", body)

#let segment-token(color, name: none) = box(
  baseline: 35%,
  inset: (x: 2pt),
)[
  #line(length: 1.15em, stroke: 2pt + color)
  #if name != none [
    #h(2pt)
    #text(size: 7.5pt, fill: color, weight: "semibold")[#name]
  ]
]

#let point-token(color, name: none) = box(
  baseline: 35%,
  inset: (x: 2pt),
)[
  #circle(radius: 2.2pt, fill: color, stroke: none)
  #if name != none [
    #h(2pt)
    #text(size: 7.5pt, fill: color, weight: "semibold")[#name]
  ]
]

#let proof-block(body, title: [Demonstration]) = block(
  width: 100%,
  above: 5pt,
  below: 9pt,
  inset: (left: 10pt),
  stroke: (left: 0.6pt + by-rule),
)[
  #set par(first-line-indent: 0pt, spacing: 0.5em)
  #text(size: 9.3pt)[
    #strong[#title.]
    #h(4pt)
    #body
  ]
]

#let object-entry(entry, show-proof: true, show-boundary: true) = {
  element-counter.step()
  context block(
    width: 100%,
    above: 9pt,
    below: 6pt,
  )[
    #set par(first-line-indent: 0pt)
    #strong[
      #entry.kind
      #h(3pt)
      #element-counter.display("1")
      #h(3pt)
      —
      #h(3pt)
      #entry.title
    ]
    #h(5pt)
    #entry.claim
  ]

  if show-proof and entry.proof != none {
    proof-block(entry.proof)
  }

  if show-boundary and entry.boundary != none {
    block(
      width: 100%,
      stroke: (left: 0.8pt + by-open),
      inset: (left: 9pt),
      above: 6pt,
      below: 8pt,
    )[
      #text(size: 8.3pt, fill: by-muted)[
        #smallcaps[Boundary.]
        #h(4pt)
        #entry.boundary
      ]
    ]
  }
}

#let construction-card(
  title: none,
  problem: none,
  diagram: none,
  demonstration: none,
  algebra: none,
  conclusion: none,
) = block(
  width: 100%,
  fill: by-paper,
  stroke: (top: 1pt + by-black, bottom: 1pt + by-black),
  inset: (x: 12pt, y: 11pt),
  above: 12pt,
  below: 12pt,
  breakable: false,
)[
  #text(size: 8pt, fill: by-muted, tracking: 0.08em)[#smallcaps[Geometric construction]]
  #v(2pt)
  #text(size: 13pt, weight: "semibold")[#title]
  #v(8pt)

  #grid(
    columns: (1.12fr, 0.88fr),
    column-gutter: 1.4em,
    align: (left, center),
    [
      #set par(first-line-indent: 0pt, spacing: 0.52em)
      #strong[Problem.]
      #h(4pt)
      #problem
      #v(7pt)
      #strong[Construction and demonstration.]
      #h(4pt)
      #demonstration
    ],
    [#diagram],
  )

  #if algebra != none [
    #v(8pt)
    #block(
      width: 100%,
      fill: white.transparentize(35%),
      inset: 7pt,
      stroke: 0.45pt + by-rule,
    )[
      #set par(first-line-indent: 0pt)
      #strong[Algebraic face.]
      #h(4pt)
      #algebra
    ]
  ]

  #if conclusion != none [
    #v(7pt)
    #text(fill: by-black)[
      #strong[Therefore.]
      #h(4pt)
      #conclusion
    ]
  ]
]

#let elements-paper(
  title: none,
  subtitle: none,
  authors: none,
  date: none,
  abstract: none,
  body,
) = {
  set page(
    paper: "us-letter",
    margin: (x: 0.88in, top: 0.78in, bottom: 0.76in),
    fill: rgb("#FFFEFA"),
    footer: context align(center)[
      #text(size: 8pt, fill: by-muted)[#counter(page).display("1")]
    ],
  )
  set text(font: ("C059", "DejaVu Serif"), size: 10.2pt, fill: by-black)
  set par(justify: true, first-line-indent: 1.1em, leading: 0.68em)
  set heading(numbering: "I.1")
  show heading.where(level: 1): set text(size: 17pt, weight: "regular", fill: by-black)
  show heading.where(level: 2): set text(size: 12.4pt, weight: "semibold", fill: by-blue)
  show heading.where(level: 3): set text(size: 10.6pt, weight: "semibold", fill: by-red)
  show link: set text(fill: by-blue)

  align(center)[
    #v(8pt)
    #text(size: 8.5pt, fill: by-red, tracking: 0.14em)[#smallcaps[Laboratory elements]]
    #v(8pt)
    #text(size: 25pt, weight: "regular")[#title]
    #v(4pt)
    #text(size: 12pt, style: "italic", fill: by-muted)[#subtitle]
    #v(12pt)
    #line(length: 55%, stroke: 1.2pt + by-black)
    #v(8pt)
    #text(size: 9.4pt)[#authors]
    #v(2pt)
    #text(size: 8.6pt, fill: by-muted)[#date]
  ]

  v(16pt)
  block(
    width: 88%,
    inset: (x: 12pt, y: 10pt),
    stroke: (left: 2pt + by-yellow),
    fill: by-paper,
  )[
    #set par(first-line-indent: 0pt, spacing: 0.5em)
    #text(size: 9.1pt)[
      #smallcaps[Abstract.]
      #h(5pt)
      #abstract
    ]
  ]

  v(14pt)
  body
}

#let comparison-triangle-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let A = (0, 0)
    let B = (3, 4)
    let C = (7, 0)

    line(A, B, C, close: true, fill: by-paper, stroke: 0.6pt + by-rule)
    line(A, B, stroke: 2.2pt + by-blue, mark: (end: ">"))
    line(B, C, stroke: 2.2pt + by-yellow, mark: (end: ">"))
    line(A, C, stroke: 2.2pt + by-red, mark: (end: ">"))

    circle(A, radius: 0.12, fill: by-black, stroke: none)
    circle(B, radius: 0.12, fill: by-black, stroke: none)
    circle(C, radius: 0.12, fill: by-black, stroke: none)

    content((-1/3, -1/3), text(size: 8pt, weight: "semibold")[$A$])
    content((3, 13/3), text(size: 8pt, weight: "semibold")[$B$])
    content((22/3, -1/3), text(size: 8pt, weight: "semibold")[$C$])
    content((7/6, 13/6), text(size: 8pt, fill: by-blue, weight: "semibold")[$u$])
    content((31/6, 13/6), text(size: 8pt, fill: by-yellow, weight: "semibold")[$v$])
    content((7/2, -1/3), text(size: 8pt, fill: by-red, weight: "semibold")[$w$])
    content((7/2, 4/3), text(size: 8.5pt, fill: by-muted)[$tau$])
  }),
  caption: [One supplied comparison face. The colored paths are the same addressed
  constituents in the figure, prose, and equations.],
)

#let point-line-loop-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.2, {
    import cetz.draw: *

    circle((0, 1), radius: 0.15, fill: by-red, stroke: none)
    content((0, 1/3), text(size: 8pt)[event cut])
    content((0, 5/3), text(size: 8pt, fill: by-red)[$x_t$])

    line((2, 1), (6, 1), stroke: 2pt + by-blue, mark: (end: ">"))
    circle((2, 1), radius: 0.1, fill: by-black, stroke: none)
    circle((4, 1), radius: 0.1, fill: by-black, stroke: none)
    circle((6, 1), radius: 0.1, fill: by-black, stroke: none)
    content((4, 1/3), text(size: 8pt)[ordered lineage])
    content((4, 5/3), text(size: 8pt, fill: by-blue)[$gamma$])

    circle((9, 1), radius: 4/3, stroke: 2pt + by-yellow)
    line((9, 1), (10, 1), stroke: 1pt + by-black, mark: (end: ">"))
    content((9, 1/3), text(size: 8pt)[returned path])
    content((9, 5/3), text(size: 8pt, fill: by-yellow)[$q(gamma)$])
  }),
  caption: [One occurrence may be point-like at an event cut, line-like across its
  ordered continuation, and loop-like after a return receiver closes it.],
)

#let atlas-overlap-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.2, {
    import cetz.draw: *

    circle((3, 2), radius: 2, fill: by-blue.transparentize(86%), stroke: 1.3pt + by-blue)
    circle((6, 2), radius: 2, fill: by-red.transparentize(86%), stroke: 1.3pt + by-red)
    content((2, 2), text(size: 8.5pt, fill: by-blue)[$U_alpha$])
    content((7, 2), text(size: 8.5pt, fill: by-red)[$U_beta$])
    content((9/2, 2), text(size: 8.5pt, weight: "semibold")[$g_(alpha beta)$])
    line((7/2, 3), (11/2, 3), stroke: 1.5pt + by-yellow, mark: (end: ">"))
    line((11/2, 1), (7/2, 1), stroke: 1.5pt + by-yellow, mark: (end: ">"))
    content((9/2, 1/2), text(size: 7.6pt, fill: by-muted)[declared overlap])
  }),
  caption: [A holonic atlas grows by actual overlap maps. Neither chart is an
  external master space, and no transition exists merely because the drawings overlap.],
)

#let scale-turn-figure-elements() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.2, {
    import cetz.draw: *

    line((0, 0), (0, 4), stroke: 1.5pt + by-blue, mark: (end: ">"))
    line((0, 0), (4, 0), stroke: 1.5pt + by-red, mark: (end: ">"))
    content((2, -1/3), text(size: 8pt, fill: by-red)[$u=log r$])
    content((-1/2, 2), text(size: 8pt, fill: by-blue)[$theta$])
    line((0, 0), (3, 3), stroke: 2pt + by-yellow, mark: (end: ">"))
    content((2, 7/3), text(size: 8pt, fill: by-yellow)[$w=u+i theta$])

    line((5, 2), (6, 2), stroke: 1.2pt + by-black, mark: (end: ">"))
    content((11/2, 7/3), text(size: 8pt)[$exp$])

    circle((9, 2), radius: 2, stroke: 1.5pt + by-blue)
    circle((9, 2), radius: 1, stroke: 1.5pt + by-red)
    line((9, 2), (31/3, 3), stroke: 2pt + by-yellow, mark: (end: ">"))
    content((9, 13/3), text(size: 8pt)[annular receiver])
  }),
  caption: [The logarithmic lift carries scale and turn additively. Exponentiation
  folds complete-turn translates into one nonzero receiver face.],
)

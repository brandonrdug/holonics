#import "../glossary.typ": glossary
#import "../units/001-trace-determinant.typ": characteristic-fiber-unit

#let ink = rgb("#172033")
#let blue = rgb("#315da8")
#let pale-blue = rgb("#edf3fc")
#let pale-gold = rgb("#fff6dd")
#let pale-green = rgb("#eaf7ef")
#let pale-red = rgb("#fff0ef")
#let rule = rgb("#cad2df")

#let panel(title, body, fill: pale-blue, border: blue) = block(
  width: 100%,
  inset: 10pt,
  radius: 4pt,
  fill: fill,
  stroke: 0.7pt + border,
  breakable: false,
  [
    #text(fill: border, weight: "bold")[#title]
    #v(4pt)
    #body
  ],
)

#let investigation(number, title, body) = block(
  width: 100%,
  inset: 11pt,
  radius: 4pt,
  stroke: 0.8pt + rule,
  breakable: false,
  [
    #text(fill: blue, weight: "bold")[Open relation #number — #title]
    #v(5pt)
    #body
  ],
)

#let derivation(show-derivations, body) = if show-derivations {
  panel("Symbolic derivation", body, fill: pale-green, border: rgb("#287247"))
} else {
  []
}

#let boundary(body) = panel(
  "Aperture",
  body,
  fill: pale-red,
  border: rgb("#a33c36"),
)

#let workbook(show-derivations: false) = {
  set page(
    paper: "us-letter",
    margin: (top: 0.72in, bottom: 0.72in, x: 0.78in),
    numbering: "1 / 1",
    number-align: center,
  )
  set text(size: 10.5pt, fill: ink)
  set par(justify: true, leading: 0.68em)
  set heading(numbering: "1.1")
  set math.equation(numbering: "(1)")
  show link: set text(fill: blue)
  show heading.where(level: 1): it => block(
    above: 18pt,
    below: 10pt,
    [#text(size: 18pt, weight: "bold", fill: ink)[#counter(heading).display() #it.body]],
  )
  show heading.where(level: 2): it => block(
    above: 13pt,
    below: 7pt,
    [#text(size: 13pt, weight: "bold", fill: blue)[#counter(heading).display() #it.body]],
  )

  align(center)[
    #v(0.35in)
    #text(size: 29pt, weight: "bold", fill: ink)[Symbolic Mathematical Notebook]
    #v(8pt)
    #text(size: 16pt, fill: blue)[Couplings · fibers · strata · transport]
    #v(22pt)
    #block(
      width: 78%,
      inset: 14pt,
      radius: 6pt,
      fill: pale-blue,
      stroke: 0.8pt + blue,
    )[
      #align(left)[
        *Surface:* #if show-derivations [derivation companion] else [open symbolic workbench]
        #linebreak()
        *First unit:* The geometry inside a characteristic receiver
        #linebreak()
        *Status:* educational exploration; not construction standing
      ]
    ]
    #v(1fr)
    #text(size: 9pt, fill: luma(90))[
      Follow the variables before evaluating them.
    ]
    #v(0.35in)
  ]

  pagebreak()

  characteristic-fiber-unit(
    show-derivations: show-derivations,
    panel: panel,
    investigation: investigation,
    derivation: derivation,
    boundary: boundary,
  )

  pagebreak()

  [= Navigation

  This notebook begins from a symbolic object rather than a sequence of prerequisite calculations.
  The named operation is unfolded first; numerical evaluation is optional and subordinate.

  #table(
    columns: (1.1fr, 1.65fr, 1.75fr),
    inset: 7pt,
    stroke: 0.5pt + rule,
    [*Surface*], [*What it exposes*], [*Typical motion*],
    [Entry coordinates], [Which symbols are coupled], [Expand named operations],
    [Changed coordinates], [Hidden quadratic or incidence geometry], [Reparameterize],
    [Receiver fiber], [All sources sharing one output], [Hold invariants fixed],
    [Strata], [Where qualitative behavior changes], [Solve boundary equations],
    [Transport], [Motion within or between fibers], [Derive preserved relations],
    [Lean mirror], [General polynomial identity and hypotheses], [Mutate the formal map],
  )

  #v(10pt)
  #panel(
    "The motion",
    [
      #align(center)[
        object $arrow.r$ unfold $arrow.r$ reparameterize $arrow.r$ vary $arrow.r$ locate strata
        $arrow.r$ transport $arrow.r$ formalize
      ]
    ],
    fill: pale-gold,
    border: rgb("#9a6b12"),
  )

  A concrete scalar instance is useful only when it witnesses a distinction that the symbolic
  relation has already made precise. It is not the default object of practice here.

  #v(10pt)
  #panel(
    "External construction atlases",
    [
      Chris van Tienhoven's
      #link("https://www.chrisvantienhoven.nl/epg/n-geometry/quadri-figures/ql-items/ql-tf1/")[Clawson–Schmidt conjugate entry]
      organizes one transformation through its reference configuration, construction, coordinate
      forms, mapped object classes, invariants, and compositions. The
      #link("https://en.wikipedia.org/wiki/Clawson_point")[Clawson point]
      is a distinct triangle center; its multiple geometric constructions are another useful model
      of one object transported across problem-solving frameworks.
    ],
    fill: pale-blue,
    border: blue,
  )
  ]

  pagebreak()
  glossary()
}

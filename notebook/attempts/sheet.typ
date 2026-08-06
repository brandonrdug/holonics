#set page(
  paper: "us-letter",
  margin: (top: 0.52in, bottom: 0.52in, x: 0.58in),
)
#set text(size: 10pt, fill: rgb("#172033"))

#let blue = rgb("#315da8")
#let rule = rgb("#aeb9ca")

#let write-box(title, height) = block(
  width: 100%,
  height: height,
  inset: 9pt,
  radius: 4pt,
  stroke: 0.7pt + rule,
  [#text(fill: blue, weight: "bold")[#title]],
)

#align(center)[
  #text(size: 19pt, weight: "bold")[Symbolic algebra canvas]
]

#v(7pt)
#grid(
  columns: (1.25fr, 1.25fr, 1fr),
  gutter: 8pt,
  [*Object or family*], [*Current chart*], [*Page / date*],
  [#line(length: 100%, stroke: 0.5pt + rule)],
  [#line(length: 100%, stroke: 0.5pt + rule)],
  [#line(length: 100%, stroke: 0.5pt + rule)],
)

#v(8pt)
#write-box("Named operations unfolded into coupled variables", 1.08in)
#v(8pt)
#write-box("Change of variables / alternate chart", 1.15in)
#v(8pt)
#write-box("Parameter motion — what varies, and what remains fixed?", 1.15in)
#v(8pt)
#write-box("Fiber, strata, graph, or higher-dimensional geometry", 2.45in)
#v(8pt)
#grid(
  columns: (1fr, 1fr),
  gutter: 8pt,
  write-box("Identity or proof obligation", 1.02in),
  write-box("Open relation / next deformation", 1.02in),
)


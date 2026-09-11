# holonic-engraving

`lib.typ` renders a compiled receiver scene dictionary as a pure CeTZ vector face.

```typst
#import "lib.typ": engrave
#let scene = (
  bounds: (0, 0, 4, 3),
  marks: (
    (points: ((0, 0), (4, 3)), rgb: (1, 1/5, 1/10), width: 1, kind: "ray"),
  ),
  meta: (:),
)
#engrave(scene, width: 80mm)
```

The packet supplies numeric bounds, marks, clipping, visibility, and phase RGB values in the
`0..1` range. `mode: "phase"` uses a black viewport and packet colors; `mode: "mono"` uses a
white viewport and black marks. No color correction, depth ordering, visibility test, or frame
outline is performed here. `figure-frame` is available when an outer presentation explicitly asks
for one.


`line-width` is a physical pen width (default `1pt/4`), multiplied by each packet mark's width.
An explicit `height` fits the viewport without distortion and centers it on the requested ground.
Stipple marks contain one location. Mark clipping, source intervals and field levels belong to
the compiler packet; the painter does not replace them. The optional SVG exporter consumes the
same marks and embeds source metadata, supporting a shared Typst/web view. The example file can
be compiled from the papers source root after the receiver packet build.

`tests.typ` checks the explicit-height viewport contract. `svg-comparison.typ`, built with
`--root research/papers`, compares a Typst packet and its SVG export using the same source marks.

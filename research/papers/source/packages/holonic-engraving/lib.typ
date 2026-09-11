// Receiver engraving: a pure presentation face for an already compiled scene packet.
// The packet owns bounds, marks, visibility, clipping, and phase values. This package only
// maps those values into CeTZ vectors; it does not infer geometry or re-decide visibility.
#import "@preview/cetz:0.3.4"

#let _paint(mark, mode) = {
  if mode == "mono" {
    black
  } else {
    let c = mark.rgb
    // CeTZ/Typst accepts integer channels or ratios. The packet value is transferred directly
    // to the display channel; this is only the platform's 8-bit paint representation.
    rgb(int(c.at(0) * 255), int(c.at(1) * 255), int(c.at(2) * 255))
  }
}

#let _stroke-width(base, mark) = base * mark.at("width", default: 1)

#let _mark(mark, mode, base) = {
  let points = mark.points
  let kind = mark.at("kind", default: "contour")
  let paint = _paint(mark, mode)
  let thickness = _stroke-width(base, mark)
  if kind == "stipple" {
    // Radius is tied to the packet width, so stipple density is a face of the packet.
    for point in points.slice(0, calc.min(1, points.len())) {
      cetz.draw.circle(point, radius: thickness / 2, fill: paint, stroke: none)
    }
  } else if points.len() > 1 {
    // Packet marks are already clipped. Preserve their supplied order and do not close them.
    cetz.draw.line(..points, stroke: thickness + paint)
  } else if points.len() == 1 {
    cetz.draw.circle(points.at(0), radius: thickness / 2, fill: paint, stroke: none)
  }
}

#let engrave(scene, width: 80mm, height: auto, mode: "phase", line-width: 1pt/4) = {
  assert(width>0mm and (height==auto or height>0mm),message:"positive presentation extent required")
  let bounds = scene.bounds
  let xmin = bounds.at(0)
  let ymin = bounds.at(1)
  let xmax = bounds.at(2)
  let ymax = bounds.at(3)
  let sx = xmax - xmin
  let sy = ymax - ymin
  assert(sx > 0 and sy > 0, message: "holonic-engraving: bounds must have positive extent")
  assert(mode == "phase" or mode == "mono", message: "holonic-engraving: mode must be phase or mono")
  let ground = if mode == "phase" { black } else { white }
  // CeTZ's scalar length maps one scene unit to one physical unit. The scene is normalized
  // here, so the requested width fixes the x scale and auto height preserves the packet aspect.
  let unit = if height == auto {width / sx} else {calc.min(width / sx,height / sy)}
  let canvas-height = unit * sy
  block(width: width, height: if height == auto { canvas-height } else { height },fill:ground)[
    #align(center+horizon,cetz.canvas(length: unit, padding: 0, {
      import cetz.draw: *
      cetz.draw.rect((xmin, ymin), (xmax, ymax), fill: ground, stroke: none)
      for mark in scene.marks {
        _mark(mark, mode, line-width)
      }
    }))
  ]
}

// Optional explicit frame helper. A frame is a presentation choice and is never added by engrave.
#let figure-frame(body, fill: none, stroke: (7pt/20) + black) = block(
  fill: fill,
  stroke: stroke,
  inset: 3pt,
  body,
)

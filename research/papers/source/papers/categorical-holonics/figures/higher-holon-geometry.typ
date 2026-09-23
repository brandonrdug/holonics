#import "@preview/cetz:0.3.4"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-paper, by-muted, by-rule

// Three higher-dimensional Holonic constructions. CeTZ projects supplied
// coordinates; a projected crossing never becomes a contact without a vertex.

#set page(width: 10in, height: 4.95in, margin: (x: 0.55in, y: 0.30in), fill: white)
#set text(font: ("C059", "DejaVu Serif"), size: 10.5pt)
#set par(first-line-indent: 0pt, justify: false)
#show figure.caption: set text(size: 9.2pt)

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1.2cm, padding: 0.7, {
    import cetz.draw: *

    let v(a, g, r) = (4*a, 2.7*r, -3.2*g)
    let x(a, g, r) = v(a, g, r)

    ortho(x: 31deg, y: 30deg, z: 0deg, sorted: false, cull-face: none, {
      // Three source-qualified comparison faces.
      line(x(0, 0, 0), x(1, 0, 0), x(1, 1, 0), x(0, 1, 0),
        close: true, fill: by-blue.transparentize(92%), stroke: none)
      line(x(0, 0, 0), x(0, 0, 1), x(0, 1, 1), x(0, 1, 0),
        close: true, fill: by-red.transparentize(93%), stroke: none)
      line(x(0, 0, 1), x(1, 0, 1), x(1, 1, 1), x(0, 1, 1),
        close: true, fill: by-yellow.transparentize(93%), stroke: none)

      for a in range(2) {
        for g in range(2) {
          line(x(a, g, 0), x(a, g, 1),
            stroke: 0.8pt + by-yellow, mark: (end: ">"))
        }
      }
      for a in range(2) {
        for r in range(2) {
          line(x(a, 0, r), x(a, 1, r),
            stroke: 0.8pt + by-red, mark: (end: ">"))
        }
      }
      for g in range(2) {
        for r in range(2) {
          line(x(0, g, r), x(1, g, r),
            stroke: 0.9pt + by-blue, mark: (end: ">"))
        }
      }

      for a in range(2) {
        for g in range(2) {
          for r in range(2) {
            circle(x(a, g, r), radius: 0.065, fill: by-black, stroke: none)
            content(
              (4*a + if a == 0 { -0.35 } else { 0.35 },
               2.7*r + if r == 0 { -0.24 } else { 0.24 },
               -3.2*g + if g == 0 { 0.25 } else { -0.25 }),
              text(size: 8.2pt)[$x_(#a#g#r)$],
            )
          }
        }
      }

      content((2, 0, 0.52), text(size: 8.6pt, fill: by-blue)[$T_a$])
      content((-0.45, 0, -1.55), text(size: 8.6pt, fill: by-red)[$pi$])
      content((-0.35, 1.4, 0.55), text(size: 8.6pt, fill: by-yellow)[$U_(F'←F)$])
      content((2, 1.35, -1.6), text(size: 10pt)[$Gamma$])
    })
  })),
  caption: [
    *A three-direction Holon cube.* Vertex $x_(a,g,r)$ records an action cut $a$,
    grain $g$ and frame $r$. Blue arrows carry a generator action, red arrows
    restrict grain, and gold arrows rechart frame. The face squares compare
    these operations; $Gamma$ is the proposed 3-cell comparing two pastings.
    *Status:* the full cube is open. Curvature or retained interior may obstruct a face.
  ],
)

#pagebreak()

#let torus(u, v) = {
  let R = 1.85
  let r = 0.57
  let radial = R + r * calc.cos(v)
  (radial * calc.cos(u), radial * calc.sin(u), r * calc.sin(v))
}

#figure(
  placement: none,
  align(center, grid(
    columns: (1fr, auto, 1.3fr),
    column-gutter: 0.35in,
    align: center,
    [
      #cetz.canvas(length: 1.08cm, padding: 0.45, {
        import cetz.draw: *
        line((0, 0), (4, 0), (4, 4), (0, 4), close: true,
          stroke: 0.6pt + by-black)
        line((0, 0), (2, 4), stroke: 1.45pt + by-blue,
          mark: (end: ">"))
        line((2, 0), (4, 4), stroke: 1.45pt + by-blue,
          mark: (end: ">"))
        circle((2, 4), radius: 0.075, fill: by-red, stroke: none)
        circle((2, 0), radius: 0.075, fill: by-red, stroke: none)
        content((2, -0.42), text(size: 8.4pt)[$theta_a$])
        content((-0.48, 2), text(size: 8.4pt)[$theta_b$])
        content((3.55, 4.36), text(size: 8pt, fill: by-red)[carry])
        content((2, 2.15), text(size: 8.5pt, fill: by-blue)[$(1,2)$])
      })
    ],
    [
      #align(center)[
        #text(size: 14pt)[$q : RR^2 -> TT^2$]
      ]
    ],
    [
      #cetz.canvas(length: 1.08cm, padding: 0.5, {
        import cetz.draw: *
        ortho(x: 35deg, y: 13deg, z: 0deg,
          sorted: false, cull-face: none, {
          for v in (0deg, 90deg, 180deg, 270deg) {
            let pts = range(97).map(k => torus(k * 360deg / 96, v))
            line(..pts, stroke: 0.4pt + by-muted.transparentize(60%))
          }
          for u in (0deg, 45deg, 90deg, 135deg, 180deg, 225deg, 270deg, 315deg) {
            let pts = range(97).map(k => torus(u, k * 360deg / 96))
            line(..pts, stroke: 0.4pt + by-muted.transparentize(64%))
          }
          let orbit = range(145).map(k =>
            torus(k * 360deg / 144, 2 * k * 360deg / 144))
          line(..orbit, stroke: 1.6pt + by-blue)
          circle(torus(0deg, 0deg), radius: 0.09,
            fill: by-red, stroke: none)
        })
      })
    ],
  )),
  caption: [
    *Pair phase and its helical lift.* The left chart shows
    $(theta_a,theta_b)=(t,2t)$ on one fundamental square; red endpoints
    mark the carried edge. Quotienting gives the blue path on the phase torus
    $TT^2$ at right. The full pair retains integer winding and axial screw
    motion beyond this three-dimensional display. *Scope:* a projection of the
    supplied generator law, not a proof of physical contact or finite closure.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1.07cm, padding: 0.5, {
    import cetz.draw: *

    // A declared composite region; presentation of an actual port join.
    rect((0.4, 0.65), (7.6, 5.15),
      stroke: (paint: by-muted, thickness: 0.6pt, dash: "dashed"),
      fill: by-paper.transparentize(83%))
    content((7.15, 5.35), text(size: 8.2pt)[$H_A bowtie_Sigma H_R$])

    // Two source Holons enter one helical pair contact.
    line((1.7, 6.1), (1.7, 5.25), stroke: 0.95pt + by-black)
    line((5.1, 6.1), (5.1, 5.25), stroke: 0.95pt + by-black)
    bezier((1.7, 5.25), (3.4, 4.25),
      (1.8, 4.7), (2.55, 4.3), stroke: 0.95pt + by-black)
    bezier((5.1, 5.25), (3.4, 4.25),
      (5.0, 4.7), (4.25, 4.3), stroke: 0.95pt + by-black)
    circle((3.4, 4.25), radius: 0.11, fill: by-black, stroke: none)
    content((3.85, 4.45), text(size: 8.7pt)[$J$])
    content((1.35, 6.36), text(size: 8.5pt)[$H_A$])
    content((5.35, 6.36), text(size: 8.5pt)[$H_R$])

    // A parametron's internal storage and its active receiving face.
    line((3.4, 4.25), (3.4, 3.0),
      stroke: 1pt + by-blue, mark: (end: ">"))
    circle((3.4, 2.55), radius: 0.43,
      stroke: 1.05pt + by-blue, fill: white)
    content((3.4, 2.55), text(size: 8pt, fill: by-blue)[$C,L$])
    line((3.4, 2.12), (3.4, 1.45),
      stroke: 1pt + by-blue, mark: (end: ">"))
    circle((3.4, 1.32), radius: 0.11, fill: by-black, stroke: none)
    content((2.9, 1.22), text(size: 8.7pt)[$rho_R$])
    line((3.4, 1.32), (3.4, 0.2),
      stroke: 0.95pt + by-black, mark: (end: ">"))
    content((3.75, 0.15), text(size: 8.7pt)[$y_R$])

    // A stored internal mode reaches the contact at a later clock crossing.
    bezier((3.83, 2.55), (3.55, 4.12),
      (6.95, 2.2), (6.95, 4.48),
      stroke: 1pt + by-yellow, mark: (end: ">"))
    content((6.5, 3.0), text(size: 8pt, fill: by-yellow)[next tick + carry])
  })),
  caption: [
    *A ported Holon with a declared internal return.* The interaction vertex
    is the pair slip $J$; the ring stores and exchanges energy through $C,L$;
    the active receiving Holon reads a face through $rho_R$. The gold loop
    carries an internal mode back to the contact at a later clock crossing.
    Wires carry typed currents and dual efforts, and the dashed
    region is their composite Holon. *Scope:* the diagram states incidence;
    its constitutive power and recurrence laws remain the specified operands.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, fletcher.diagram(
    node-stroke: none,
    edge-stroke: 0.78pt + by-black,
    spacing: (11.2em, 4.0em),
    node((1, 0), [$((A ⊗ B) ⊗ C) ⊗ D$], stroke: none),
    node((0, 1), [$(A ⊗ (B ⊗ C)) ⊗ D$], stroke: none),
    node((0.3, 2), [$A ⊗ ((B ⊗ C) ⊗ D)$], stroke: none),
    node((1.7, 2), [$A ⊗ (B ⊗ (C ⊗ D))$], stroke: none),
    node((2, 1), [$(A ⊗ B) ⊗ (C ⊗ D)$], stroke: none),
    edge((1, 0), (0, 1), "-|>", [$alpha_(A,B,C) ⊗ 1_D$]),
    edge((0, 1), (0.3, 2), "-|>", [$alpha_(A,B⊗C,D)$]),
    edge((0.3, 2), (1.7, 2), "-|>", [$1_A ⊗ alpha_(B,C,D)$]),
    edge((1, 0), (2, 1), "-|>", [$alpha_(A⊗B,C,D)$]),
    edge((2, 1), (1.7, 2), "-|>", [$alpha_(A,B,C⊗D)$]),
  )),
  caption: [
    *The port-juxtaposition pentagon.* $A,B,C,D$ are Holons considered in
    parallel; $alpha$ is the canonical reassociation of their typed port
    sums. The two paths should agree as one reindexing. *Status:* coherence
    for the complete Holon, including constitutions, generators and
    restrictions, is an obligation beyond the proved two-body Dirac join.
    Actual contact is a further declared wiring of these ports.
  ],
)

#pagebreak()

#let screw-point(u, cx, radius, turns, phase, rise) = (
  cx + radius * calc.cos(turns * 360deg * u + phase),
  radius * calc.sin(turns * 360deg * u + phase),
  rise * u,
)

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1.15cm, padding: 0.75, {
    import cetz.draw: *

    let a(u) = screw-point(u, -1.7, 0.63, 2, 0deg, 4.2)
    let b(u) = screw-point(u, 1.7, 0.53, 3, 35deg, 3.85)
    let s = 0.43
    let t = 0.58
    let pa = a(s)
    let pb = b(t)

    ortho(x: 51deg, y: 24deg, z: 0deg, sorted: false, cull-face: none, {
      line((-1.7, 0, 0), (-1.7, 0, 4.2),
        stroke: (paint: by-muted, thickness: 0.55pt, dash: "dashed"))
      line((1.7, 0, 0), (1.7, 0, 3.85),
        stroke: (paint: by-muted, thickness: 0.55pt, dash: "dashed"))
      let orbit-a = range(145).map(k => a(k / 144))
      let orbit-b = range(145).map(k => b(k / 144))
      line(..orbit-a, stroke: 1.55pt + by-blue)
      line(..orbit-b, stroke: 1.55pt + by-yellow)
      circle(pa, radius: 0.1, fill: by-blue, stroke: none)
      circle(pb, radius: 0.1, fill: by-yellow, stroke: none)
      line(pb, pa, stroke: 1.15pt + by-red, mark: (end: ">"))
      line(pa, a(s + 0.06), stroke: 1.0pt + by-blue, mark: (end: ">"))
      line(pb, b(t + 0.045), stroke: 1.0pt + by-yellow, mark: (end: ">"))
      content((-1.7, 0, 4.7), text(size: 8.7pt, fill: by-blue)[$G_a$])
      content((1.7, 0, 4.4), text(size: 8.7pt, fill: by-yellow)[$G_b$])
      content((pa.at(0) - 0.35, pa.at(1), pa.at(2) - 0.28),
        text(size: 8.4pt, fill: by-blue)[$x_a(s)$])
      content((pb.at(0) + 0.42, pb.at(1), pb.at(2) - 0.25),
        text(size: 8.4pt, fill: by-yellow)[$x_b(t)$])
      content(((pa.at(0) + pb.at(0)) / 2,
               (pa.at(1) + pb.at(1)) / 2,
               (pa.at(2) + pb.at(2)) / 2 + 0.25),
        text(size: 9pt, fill: by-red)[$Delta$])
    })
  })),
  caption: [
    *Two situated helical generators.* The blue and gold curves use separate
    initial configurations, rates and clocks. Their selected orbit points give
    $Delta=x_a(s)-x_b(t)$; the short arrow segments show the two tangent
    directions, so the contact slip map is $J=[v_a | -v_b]$.
    The red segment is geometric separation. An admitted pair contact and its
    material $D$ supply the actual interaction. Their joint phase and axial
    chart has four coordinates $(theta_a,z_a,theta_b,z_b)$; Figure 2 shows one
    possible path in its angular torus. Axial carry remains in the lift.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1.12cm, padding: 0.85, {
    import cetz.draw: *

    // Four independent binary directions, projected by an explicit affine map.
    // Coordinates are (action, grain, frame, receiver).
    let p(a, g, r, s) = (
      3.7*a + 1.2*r + 6.2*s,
      2.6*g + 0.85*r + 0.35*s,
    )

    // Receiver changes are the fourth direction; their dashed style remains
    // distinct from the three coloured Holon operations.
    for a in range(2) {
      for g in range(2) {
        for r in range(2) {
          line(p(a, g, r, 0), p(a, g, r, 1),
            stroke: (paint: by-muted, thickness: 0.58pt, dash: "dashed"))
        }
      }
    }
    for s in range(2) {
      for g in range(2) {
        for r in range(2) {
          line(p(0, g, r, s), p(1, g, r, s),
            stroke: 0.75pt + by-blue)
        }
      }
      for a in range(2) {
        for r in range(2) {
          line(p(a, 0, r, s), p(a, 1, r, s),
            stroke: 0.72pt + by-red)
        }
      }
      for a in range(2) {
        for g in range(2) {
          line(p(a, g, 0, s), p(a, g, 1, s),
            stroke: 0.72pt + by-yellow)
        }
      }
    }
    for s in range(2) {
      for r in range(2) {
        for g in range(2) {
          for a in range(2) {
            circle(p(a, g, r, s), radius: 0.052, fill: by-black, stroke: none)
          }
        }
      }
    }

    line(p(0, 0, 0, 0), p(1, 0, 0, 0),
      stroke: 1.3pt + by-blue, mark: (end: ">"))
    line(p(0, 0, 0, 0), p(0, 1, 0, 0),
      stroke: 1.3pt + by-red, mark: (end: ">"))
    line(p(0, 0, 0, 0), p(0, 0, 1, 0),
      stroke: 1.3pt + by-yellow, mark: (end: ">"))
    line(p(0, 0, 0, 0), p(0, 0, 0, 1),
      stroke: (paint: by-black, thickness: 1.05pt, dash: "dashed"),
      mark: (end: ">"))

    content((-0.35, -0.27), text(size: 8pt)[$Y_(0000)$])
    content((11.55, 4.12), text(size: 8pt)[$Y_(1111)$])
    content((1.85, -0.34), text(size: 8.5pt, fill: by-blue)[$T_a$])
    content((-0.42, 1.4), text(size: 8.5pt, fill: by-red)[$pi$])
    content((0.65, 1.18), text(size: 8.5pt, fill: by-yellow)[$U$])
    content((5.2, 0.12), text(size: 8.4pt)[$eta_R$])
    content((5.9, 3.85), text(size: 10pt)[$Xi$])
  })),
  caption: [
    *A four-direction received-face hypercube.* $Y_(a,g,r,s)$ is a face indexed
    by action cut, grain, frame and receiving Holon. Blue, red and gold edges
    carry action, restriction and rechart; dashed edges change the receiver.
    The sixteen vertices and thirty-two edges are an explicit projection of
    four independent binary directions. Squares compare pairs of operations;
    cubes compare their pastings; $Xi$ names the open four-cell coherence.
    *Status:* this diagram is a typed obligation, not an asserted theorem.
  ],
)

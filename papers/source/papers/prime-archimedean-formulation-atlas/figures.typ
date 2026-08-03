#import "@preview/cetz:0.3.4"
#import "../../lib/elements.typ": by-red, by-blue, by-yellow, by-black, by-paper, by-pale, by-rule, by-muted, by-open

#let valuation-simplex-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let a = (0.7, 0.35)
    let b = (7.1, 0.35)
    let c = (3.9, 5.45)
    let mid(ab, ac, k) = (
      ab.at(0) + k * (ac.at(0) - ab.at(0)),
      ab.at(1) + k * (ac.at(1) - ab.at(1)),
    )

    line(a, b, c, close: true, fill: by-paper, stroke: 0.8pt + by-rule)
    for k in (1/3, 2/3) {
      line(mid(a, c, k), mid(b, c, k), stroke: 0.45pt + by-pale)
      line(mid(a, b, k), mid(c, b, k), stroke: 0.45pt + by-pale)
      line(mid(b, a, k), mid(c, a, k), stroke: 0.45pt + by-pale)
    }

    let points = (
      (a, by-blue, [$3e_2$], [$8$]),
      (b, by-red, [$3e_5$], [$125$]),
      (c, by-yellow, [$3e_3$], [$27$]),
      (mid(a, b, 1/3), by-black, [$2e_2+e_5$], [$20$]),
      (mid(a, b, 2/3), by-black, [$e_2+2e_5$], [$50$]),
      (mid(a, c, 1/3), by-black, [$2e_2+e_3$], [$12$]),
      (mid(a, c, 2/3), by-black, [$e_2+2e_3$], [$18$]),
      (mid(b, c, 1/3), by-black, [$2e_5+e_3$], [$75$]),
      (mid(b, c, 2/3), by-black, [$e_5+2e_3$], [$45$]),
      (((a.at(0)+b.at(0)+c.at(0))/3, (a.at(1)+b.at(1)+c.at(1))/3),
        by-open, [$e_2+e_3+e_5$], [$30$]),
    )
    for item in points {
      circle(item.at(0), radius: 0.105, fill: item.at(1), stroke: none)
      content((item.at(0).at(0), item.at(0).at(1) + 0.25),
        text(size: 6.3pt, fill: item.at(1))[#item.at(2)])
      content((item.at(0).at(0), item.at(0).at(1) - 0.24),
        text(size: 6.2pt, fill: by-muted)[#item.at(3)])
    }

    let u = mid(a, c, 1/3)
    let v = mid(a, b, 1/3)
    let w = ((a.at(0)+b.at(0)+c.at(0))/3, (a.at(1)+b.at(1)+c.at(1))/3)
    line(u, w, stroke: 1.1pt + by-blue, mark: (end: ">"))
    line(w, v, stroke: 1.1pt + by-red, mark: (end: ">"))
    line(v, u, stroke: 1.1pt + by-yellow, mark: (end: ">"))

    rect((8.0, 0.35), (14.5, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.25, 4.85), text(size: 8.5pt, weight: "semibold")[degree $d=3$, axes $r=3$])
    content((11.25, 4.15), text(size: 8pt)[$binom(5,2)=10$ addresses])
    line((8.7, 3.75), (13.8, 3.75), stroke: 0.5pt + by-rule)
    content((9.0, 3.25), text(size: 7.4pt, fill: by-blue)[$[3]$])
    content((11.7, 3.25), text(size: 7.4pt)[3 pure cubes])
    content((9.0, 2.55), text(size: 7.4pt, fill: by-yellow)[$[2,1]$])
    content((11.7, 2.55), text(size: 7.4pt)[6 oriented mixed forms])
    content((9.0, 1.85), text(size: 7.4pt, fill: by-open)[$[1,1,1]$])
    content((11.7, 1.85), text(size: 7.4pt)[1 full-support form])
    content((11.25, 0.95), text(size: 7pt, fill: by-muted)[
      colored triangle: $(e_2-e_3)+(e_3-e_5)+(e_5-e_2)=0$
    ])
  }),
  caption: [
    The degree-three valuation fiber over $S={2,3,5}$.  Its ten addresses
    split into the three permutation orbits $[3]$, $[2,1]$, and
    $[1,1,1]$.  The colored three-step transfer closes in the fixed chart;
    this is the smallest exact prime-axis $A_2$ loop.
  ],
)

#let formula-cell-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    rect((0.25, 0.35), (7.15, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((3.7, 4.95), text(size: 8.6pt, weight: "semibold")[$pi$: Gaussian factorization])
    circle((2.0, 3.25), radius: 0.11, fill: by-black, stroke: none)
    line((2.0, 3.25), (4.4, 3.25), stroke: 1.2pt + by-blue)
    line((4.4, 3.25), (4.4, 4.35), stroke: 1.2pt + by-red)
    line((2.0, 3.25), (4.4, 4.35), stroke: 1.5pt + by-yellow)
    content((3.2, 2.88), text(size: 7pt, fill: by-blue)[$5$])
    content((4.7, 3.8), text(size: 7pt, fill: by-red)[$i$])
    content((3.25, 4.18), text(size: 7pt, fill: by-yellow)[$5+i$])
    content((3.7, 2.0), text(size: 7.3pt)[$(5+i)^4=2(1+i)(239+i)$])
    content((3.7, 1.38), text(size: 7.1pt)[$N(5+i)=2 dot 13$])
    content((3.7, 0.86), text(size: 7.1pt)[$N(239+i)=2 dot 13^4$])

    rect((7.65, 0.35), (14.55, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.1, 4.95), text(size: 8.6pt, weight: "semibold")[$e$: factorial traversal])
    for item in (
      ((8.55, 3.55), [$1/(n!)$]),
      ((10.25, 3.55), [$1/((n+1)!)$]),
      ((12.25, 3.55), [$nu(n+1)$]),
      ((13.7, 3.55), [$a_(n+1)$]),
    ) {
      rect((item.at(0).at(0)-0.5, item.at(0).at(1)-0.36),
        (item.at(0).at(0)+0.5, item.at(0).at(1)+0.36),
        radius: 3pt, fill: white, stroke: 0.55pt + by-rule)
      content(item.at(0), text(size: 6.8pt)[#item.at(1)])
    }
    line((9.05, 3.55), (9.75, 3.55), stroke: 1pt + by-blue, mark: (end: ">"))
    line((10.75, 3.55), (11.75, 3.55), stroke: 1pt + by-yellow, mark: (end: ">"))
    line((12.75, 3.55), (13.2, 3.55), stroke: 1pt + by-red, mark: (end: ">"))
    content((11.1, 2.55), text(size: 7.4pt)[$a_(n+1)=a_n/(n+1)$])
    content((11.1, 1.82), text(size: 7.2pt)[
      $v_p(n!)=sum_(k>=1) floor(n/p^k)$
    ])
    content((11.1, 1.08), text(size: 6.2pt, fill: by-muted)[
      each denominator step crosses
      #linebreak()
      precisely the prime axes of $n+1$
    ])
  }),
  caption: [
    Two constant-formulation cells expose different prime-axis interiors.
    Machin's arctangent identity closes through exact Gaussian factorization;
    the factorial series for $e$ walks through the valuation address of every
    successor denominator.  The constant is the shared return, not the loss
    of the paths which produced it.
  ],
)

#let double-atlas-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let xs = (2.5, 6.2, 9.9)
    let ys = (4.8, 3.25, 1.7)
    let labels = (
      [$S$],
      [$S union {p}$],
      [$S union {p,q}$],
    )
    let rows = (
      [Euler],
      [theta],
      [completed],
    )

    for i in range(0, 3) {
      content((xs.at(i), 5.55), text(size: 7.5pt, weight: "semibold")[#labels.at(i)])
      content((0.65, ys.at(i)), text(size: 6.4pt, fill: by-muted)[#rows.at(i)])
      for j in range(0, 3) {
        rect((xs.at(j)-0.85, ys.at(i)-0.42), (xs.at(j)+0.85, ys.at(i)+0.42),
          radius: 3pt, fill: by-paper, stroke: 0.65pt + by-rule)
        content((xs.at(j), ys.at(i)),
          text(size: 6.7pt)[#if i == 0 [$nu_#j$] else if i == 1 [$theta_#j$] else [$Xi_#j$]])
      }
    }

    for y in ys {
      line((2.42, y), (5.13, y), stroke: 1.15pt + by-blue, mark: (end: ">"))
      line((6.87, y), (9.58, y), stroke: 1.15pt + by-blue, mark: (end: ">"))
    }
    for x in xs {
      line((x, 4.36), (x, 3.69), stroke: 1.15pt + by-yellow, mark: (end: ">"))
      line((x, 2.81), (x, 2.14), stroke: 1.15pt + by-yellow, mark: (end: ">"))
    }

    line((4.35, 4.8), (4.35, 3.25), stroke: (paint: by-open, thickness: 0.75pt, dash: "dashed"))
    content((4.35, 4.05), text(size: 6.5pt, fill: by-open)[residual $K$])
    line((8.05, 3.25), (8.05, 1.7), stroke: 1.05pt + by-red, mark: (end: ">"))
    content((8.35, 2.48), text(size: 6.5pt, fill: by-red)[commuting cell])

    rect((12.0, 0.8), (14.65, 5.35), radius: 4pt, fill: white, stroke: 0.65pt + by-rule)
    content((13.32, 4.85), text(size: 7.5pt, weight: "semibold")[two directions])
    line((12.35, 4.25), (13.35, 4.25), stroke: 1.3pt + by-blue, mark: (end: ">"))
    content((13.65, 3.95), text(size: 6.7pt)[prime support])
    line((12.85, 3.85), (12.85, 2.85), stroke: 1.3pt + by-yellow, mark: (end: ">"))
    content((13.65, 3.3), text(size: 6.7pt)[formulation])
    content((13.32, 2.25), text(size: 6.7pt, fill: by-red)[
      square commutes
      #linebreak()
      or exposes an
      #linebreak()
      oriented deficit
    ])
    content((13.32, 1.2), text(size: 6.4pt, fill: by-muted)[
      no path is erased
      #linebreak()
      merely because its
      #linebreak()
      value agrees
    ])
  }),
  caption: [
    The proposed formulation atlas is fibered in two directions.  Horizontal
    maps enlarge or transfer finite prime support; vertical maps change the
    formulation receiver.  A commuting square certifies one exact
    translation.  A noncommuting square records the explicit residual needed
    to extend the atlas; it is not silently identified with zero.
  ],
)

#let ray-receiver-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    rect((0.2, 0.35), (10.0, 5.55), radius: 4pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((1.1, 4.95), text(size: 7.5pt, weight: "semibold")[receiver $R$])
    circle((1.1, 3.25), radius: 0.22, fill: by-black, stroke: none)
    line((1.32, 3.25), (1.85, 3.25), stroke: 1.2pt + by-black)

    // A schematic real affine face with one self-crossing singular occurrence.
    line(
      (6.0, 0.9), (4.8, 1.35), (4.15, 2.2), (4.5, 3.2),
      (5.55, 4.25), (7.05, 4.65), (8.25, 4.05), (8.65, 2.9),
      (8.1, 1.65), (7.0, 1.05), (5.8, 1.35), (5.25, 2.35),
      (5.65, 3.35), (6.75, 3.65), (7.65, 3.05), (7.1, 2.2),
      (6.0, 2.5), (5.25, 3.2),
      stroke: 1.25pt + by-blue,
    )
    content((7.65, 5.05), text(size: 7pt, fill: by-blue)[$X_F:F(x)=0$])

    let hits = ((4.3, 2.55), (5.65, 3.35), (8.2, 3.82))
    for i in range(0, 3) {
      let target = hits.at(i)
      line((1.55, 3.25), target,
        stroke: (paint: if i == 1 { by-red } else { by-rule },
          thickness: if i == 1 { 1.5pt } else { 0.75pt },
          dash: if i == 1 { none } else { "dashed" }),
        mark: (end: ">"))
      circle(target, radius: 0.09,
        fill: if i == 1 { by-red } else { by-muted }, stroke: none)
    }
    content((3.3, 4.05), text(size: 6.8pt, fill: by-red)[$r(t)=o+t d$])
    content((5.55, 3.72), text(size: 6.7pt, fill: by-red)[selected root $t_R$])
    circle((5.25, 3.2), radius: 0.13, fill: by-open, stroke: none)
    content((4.75, 2.75), text(size: 6.6pt, fill: by-open)[$F=0, nabla F=0$])

    line((10.45, 2.95), (11.45, 2.95), stroke: 1.2pt + by-black, mark: (end: ">"))
    content((10.95, 3.35), text(size: 6.6pt)[$Pi_R$])
    rect((11.9, 0.85), (14.65, 5.05), radius: 4pt, fill: white, stroke: 0.65pt + by-rule)
    for item in (
      ((12.45, 4.4), by-pale),
      ((13.15, 4.4), by-blue),
      ((13.85, 4.4), by-pale),
      ((12.45, 3.7), by-pale),
      ((13.15, 3.7), by-red),
      ((13.85, 3.7), by-pale),
      ((12.45, 3.0), by-pale),
      ((13.15, 3.0), by-blue),
      ((13.85, 3.0), by-pale),
    ) {
      rect((item.at(0).at(0)-0.25, item.at(0).at(1)-0.25),
        (item.at(0).at(0)+0.25, item.at(0).at(1)+0.25),
        fill: item.at(1), stroke: 0.4pt + by-rule)
    }
    content((13.28, 2.15), text(size: 6.8pt, weight: "semibold")[rendered face])
    content((13.28, 1.55), text(size: 6.4pt, fill: by-muted)[
      chart + root law
      #linebreak()
      + occlusion + light
    ])
  }),
  caption: [
    Ray tracing is itself a receiver.  It intersects one declared real affine
    chart along $r(t)=o+t d$, chooses an admissible visible root, and maps
    local differential data into pixels.  The result can faithfully testify
    about that cut while still hiding complex points, projective closure,
    interior sheets, occluded roots, and singular resolutions.
  ],
)

#let surface-cases-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.28, {
    import cetz.draw: *

    // Bowl of Integers
    rect((0.2, 3.35), (7.2, 7.05), radius: 4pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((3.7, 6.65), text(size: 8pt, weight: "semibold")[Bowl of Integers])
    circle((1.3, 4.8), radius: 0.95, stroke: 1pt + by-blue)
    circle((3.0, 4.8), radius: 0.75, stroke: 1pt + by-yellow)
    circle((4.25, 4.8), radius: 0.5, stroke: 1pt + by-red)
    circle((5.1, 4.8), radius: 0.35, stroke: 1pt + by-open)
    circle((5.72, 4.8), radius: 0.24, stroke: 1pt + by-black)
    line((0.55, 3.8), (6.5, 3.8), stroke: 0.75pt + by-rule)
    content((3.7, 3.55), text(size: 6.5pt, fill: by-muted)[
      tangent-sphere reflections preserve integral bends
    ])
    content((1.3, 4.8), text(size: 6.4pt)[$-1$])
    content((3.0, 4.8), text(size: 6.4pt)[$2$])
    content((4.25, 4.8), text(size: 6.4pt)[$5$])
    content((5.1, 4.8), text(size: 6.4pt)[$6$])

    // Cayley cubic
    rect((7.55, 3.35), (14.55, 7.05), radius: 4pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((11.05, 6.65), text(size: 8pt, weight: "semibold")[Cayley cubic])
    let ta = (8.55, 4.0)
    let tb = (13.55, 4.0)
    let tc = (11.05, 6.0)
    let td = (11.05, 4.75)
    line(ta, tb, tc, close: true, stroke: 0.8pt + by-rule)
    line(ta, td, tb, stroke: 1pt + by-blue)
    line(tc, td, stroke: 1pt + by-red)
    for p in (ta, tb, tc, td) {
      circle(p, radius: 0.12, fill: by-open, stroke: none)
    }
    content((11.05, 3.58), text(size: 6.5pt, fill: by-muted)[
      four nodes; nine lines; tetrahedral symmetry
    ])

    // Chen--Gackstatter
    rect((0.2, 0.0), (7.2, 3.0), radius: 4pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((3.7, 2.65), text(size: 8pt, weight: "semibold")[Chen--Gackstatter family])
    for i in range(0, 4) {
      for j in range(0, 3) {
        let p = (1.2 + i*1.35, 0.72 + j*0.62)
        circle(p, radius: 0.16 + 0.025*i + 0.02*j,
          stroke: (if calc.rem(i+j, 2) == 0 { 1pt + by-blue } else { 1pt + by-yellow }))
        line((p.at(0)-0.2, p.at(1)), (p.at(0)+0.2, p.at(1)), stroke: 0.55pt + by-rule)
      }
    }
    line((1.2, 0.48), (5.25, 0.48), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line((0.9, 0.72), (0.9, 1.96), stroke: 0.7pt + by-rule, mark: (end: ">"))
    content((5.65, 0.48), text(size: 6.4pt)[$i$])
    content((0.65, 2.05), text(size: 6.4pt)[$j$])
    content((6.25, 1.45), text(size: 6.2pt, fill: by-muted)[
      genus $i j$
      #linebreak()
      winding $2j+1$
    ])

    // Klein quartic
    rect((7.55, 0.0), (14.55, 3.0), radius: 4pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((11.05, 2.65), text(size: 8pt, weight: "semibold")[Klein quartic])
    let center = (9.25, 1.35)
    let ring = (
      (9.25, 2.15), (9.88, 1.85), (10.03, 1.18), (9.6, 0.65),
      (8.9, 0.65), (8.47, 1.18), (8.62, 1.85),
    )
    line(..ring, close: true, stroke: 1.2pt + by-blue)
    for p in ring {
      line(center, p, stroke: 0.55pt + by-rule)
    }
    circle(center, radius: 0.09, fill: by-red, stroke: none)
    content((12.1, 1.85), text(size: 6.7pt)[$24$ heptagons])
    content((12.1, 1.35), text(size: 6.7pt)[$84$ edges])
    content((12.1, 0.85), text(size: 6.7pt)[$56$ vertices])
    content((12.1, 0.4), text(size: 6.4pt, fill: by-muted)[$op("PSL")(2,7)$: $168$ orientations])
  }),
  caption: [
    Four original incidence schematics, deliberately not photorealistic.
    Each ray-traced subject is compelling because a compact local law unfolds
    into a globally constrained population: reflection orbits, extremal
    singularities, period-closed minimal surfaces, and a hyperbolic quotient
    of exceptional symmetry.
  ],
)

#let completion-seam-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let finite = ((0.7, 4.8), (2.2, 4.8), (3.7, 4.8), (5.2, 4.8))
    for i in range(0, 4) {
      circle(finite.at(i), radius: 0.25, fill: by-paper,
        stroke: 1pt + (if i == 0 { by-blue } else if i == 1 { by-yellow } else { by-red }))
      content(finite.at(i), text(size: 6.4pt)[$p_#(i+1)$])
      if i < 3 {
        line((finite.at(i).at(0)+0.28, 4.8), (finite.at(i+1).at(0)-0.28, 4.8),
          stroke: 0.8pt + by-rule, mark: (end: ">"))
      }
    }
    content((2.95, 5.45), text(size: 7.5pt, weight: "semibold")[finite prime places])
    content((2.95, 4.15), text(size: 6.8pt, fill: by-muted)[Euler factors and prime powers])

    rect((0.55, 0.55), (5.35, 2.95), radius: 5pt, fill: by-paper, stroke: 0.65pt + by-rule)
    content((2.95, 2.5), text(size: 7.5pt, weight: "semibold")[archimedean place])
    content((1.4, 1.65), text(size: 7pt)[$e^(-pi x^2)$])
    line((2.05, 1.65), (2.8, 1.65), stroke: 1pt + by-yellow, mark: (end: ">"))
    content((3.25, 1.65), text(size: 7pt)[$theta$])
    line((3.7, 1.65), (4.3, 1.65), stroke: 1pt + by-yellow, mark: (end: ">"))
    content((4.72, 1.65), text(size: 7pt)[$Gamma$])
    content((2.95, 0.95), text(size: 6.6pt, fill: by-muted)[Fourier / Poisson / Mellin])

    line((5.7, 4.8), (7.2, 3.25), stroke: 1.2pt + by-blue, mark: (end: ">"))
    line((5.7, 1.75), (7.2, 3.05), stroke: 1.2pt + by-yellow, mark: (end: ">"))
    rect((7.4, 2.45), (10.0, 3.85), radius: 5pt, fill: white, stroke: 0.8pt + by-black)
    content((8.7, 3.35), text(size: 8pt, weight: "semibold")[$Xi(s)$])
    content((8.7, 2.85), text(size: 6.8pt)[completed receiver])

    line((10.2, 3.15), (11.2, 3.15), stroke: 1.2pt + by-black, mark: (end: ">"))
    line((12.0, 0.55), (12.0, 5.55), stroke: 1.8pt + by-blue)
    content((12.0, 5.8), text(size: 7.2pt, fill: by-blue)[fixed seam $Re(s)=1/2$])
    let z1 = (13.45, 4.4)
    let z2 = (10.55, 4.4)
    circle(z1, radius: 0.11, fill: by-red, stroke: none)
    circle(z2, radius: 0.11, fill: by-yellow, stroke: none)
    line(z1, z2, stroke: (paint: by-open, thickness: 0.9pt, dash: "dashed"), mark: (end: ">"))
    content((13.65, 4.55), text(size: 6.6pt, fill: by-red)[$s$])
    content((10.1, 4.55), text(size: 6.6pt, fill: by-yellow)[$1-overline(s)$])
    circle((12.0, 1.45), radius: 0.11, fill: by-blue, stroke: none)
    content((13.1, 1.45), text(size: 6.6pt, fill: by-blue)[fixed occurrence])
  }),
  caption: [
    The completed zeta receiver joins finite prime places to the archimedean
    Gaussian--theta--Mellin chain.  The critical line is the fixed seam of
    $s mapsto 1-overline(s)$, not a preferred line drawn independently of
    completion.  The atlas question is whether transported response remains
    sign-coherent around every admissible completed loop.
  ],
)

#let presentation-current-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    rect((0.25, 3.55), (14.55, 6.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((1.55, 6.05), text(size: 8pt, weight: "semibold")[arctangent term current])

    for item in (
      ((2.0, 4.95), [$2n+1$], by-blue),
      ((5.3, 4.95), [$r_n$], by-yellow),
      ((8.6, 4.95), [$2n+3$], by-red),
    ) {
      rect(
        (item.at(0).at(0)-0.75, item.at(0).at(1)-0.38),
        (item.at(0).at(0)+0.75, item.at(0).at(1)+0.38),
        radius: 3pt,
        fill: white,
        stroke: 0.75pt + item.at(2),
      )
      content(item.at(0), text(size: 7.3pt, fill: item.at(2))[#item.at(1)])
    }
    line((2.78, 4.95), (4.5, 4.95), stroke: 1.15pt + by-blue, mark: (end: ">"))
    line((6.08, 4.95), (7.8, 4.95), stroke: 1.15pt + by-red, mark: (end: ">"))
    content((3.65, 5.25), text(size: 6.4pt, fill: by-blue)[returns / departs])
    content((6.95, 5.25), text(size: 6.4pt, fill: by-red)[next face enters])

    line((1.25, 4.05), (9.35, 4.05), stroke: 1.5pt + by-black)
    content((5.3, 3.82), text(size: 6.7pt)[$-2 op("div")(v)$ fixed scale rail])
    circle((7.15, 4.05), radius: 0.12, fill: by-open, stroke: none)
    line((7.15, 4.05), (7.15, 4.55), stroke: 0.9pt + by-open, mark: (end: ">"))
    content((10.9, 5.35), text(size: 7pt, fill: by-open)[
      collision sheet:
      #linebreak()
      $2n plus.minus 1=0 mod p^k$
    ])
    content((11.95, 4.25), text(size: 6.4pt, fill: by-muted)[
      same recurrence species;
      #linebreak()
      parameter-relative cancellation
    ])

    rect((0.25, 0.15), (7.1, 3.1), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((3.68, 2.72), text(size: 8pt, weight: "semibold")[coupled accumulation])
    rect((0.7, 1.35), (2.35, 2.1), radius: 3pt, fill: white, stroke: 0.65pt + by-rule)
    content((1.53, 1.73), text(size: 7.1pt)[$(a_n,S_n)$])
    line((2.38, 1.73), (3.15, 1.73), stroke: 1.1pt + by-yellow, mark: (end: ">"))
    rect((3.2, 1.18), (4.45, 2.28), radius: 3pt, fill: white, stroke: 0.7pt + by-yellow)
    content((3.83, 1.73), text(size: 6.6pt)[$mat(r_n,0; r_n,1)$])
    line((4.5, 1.73), (5.25, 1.73), stroke: 1.1pt + by-yellow, mark: (end: ">"))
    rect((5.3, 1.35), (6.75, 2.1), radius: 3pt, fill: white, stroke: 0.65pt + by-rule)
    content((6.03, 1.73), text(size: 6.8pt)[$(a_(n+1),S_(n+1))$])
    line((3.83, 1.15), (3.83, 0.72), stroke: 0.9pt + by-open, mark: (end: ">"))
    content((3.83, 0.43), text(size: 6.4pt, fill: by-open)[$g=gcd(A D+B C,B D)$])

    rect((7.55, 0.15), (14.55, 3.1), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.05, 2.72), text(size: 8pt, weight: "semibold")[formulation changes support])
    for item in (
      ((8.75, 1.73), [series], [${5,239}$], by-blue),
      ((11.05, 1.73), [Gaussian], [${2,13}$], by-yellow),
      ((13.35, 1.73), [Chudnovsky], [${2,3,5,23,29}$], by-red),
    ) {
      rect(
        (item.at(0).at(0)-0.85, item.at(0).at(1)-0.65),
        (item.at(0).at(0)+0.85, item.at(0).at(1)+0.65),
        radius: 3pt,
        fill: white,
        stroke: 0.7pt + item.at(3),
      )
      content((item.at(0).at(0), item.at(0).at(1)+0.2),
        text(size: 6.5pt, weight: "semibold", fill: item.at(3))[#item.at(1)])
      content((item.at(0).at(0), item.at(0).at(1)-0.22),
        text(size: 6.3pt)[#item.at(2)])
    }
    line((9.63, 1.73), (10.17, 1.73), stroke: 1pt + by-open, mark: (end: ">"))
    line((11.93, 1.73), (12.47, 1.73), stroke: (paint: by-open, thickness: 0.8pt, dash: "dashed"),
      mark: (end: ">"))
    content((11.05, 0.62), text(size: 6.3pt, fill: by-muted)[
      equal return does not imply one conserved finite-prime chart
    ])
  }),
  caption: [
    The measured presentation topology.  The arctangent recurrence carries a
    moving odd face over a fixed parameter rail; modular collisions alter
    cancellation without changing the formula species.  Partial sums form a
    second coupled topology through an exact gcd quotient.  Vertical
    formulation transport can change finite-prime support, so the common
    transcendental return cannot replace its paths.
  ],
)

#let mean-transport-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    rect((0.2, 0.25), (9.4, 5.7), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((1.05, 5.25), text(size: 8pt, weight: "semibold")[situated path $gamma$])
    let path = (
      (1.0, 1.25), (1.9, 1.65), (2.8, 2.45), (3.8, 3.35),
      (4.9, 3.75), (6.0, 3.55), (7.1, 2.85), (8.3, 1.55),
    )
    line(..path, stroke: 1.65pt + by-blue, mark: (end: ">"))
    circle(path.at(0), radius: 0.12, fill: by-black, stroke: none)
    circle(path.at(7), radius: 0.12, fill: by-black, stroke: none)
    content((0.78, 0.92), text(size: 6.8pt)[$p$])
    content((8.55, 1.28), text(size: 6.8pt)[$q$])

    let c = (3.8, 3.35)
    circle(c, radius: 0.11, fill: by-yellow, stroke: none)
    line(c, (4.65, 4.05), stroke: 1.15pt + by-yellow, mark: (end: ">"))
    content((4.95, 4.2), text(size: 6.6pt, fill: by-yellow)[$dot(gamma)(c)$])
    content((3.25, 3.8), text(size: 6.6pt, fill: by-yellow)[mean witness $c$])

    let seam = (6.0, 3.55)
    circle(seam, radius: 0.15, fill: by-open, stroke: none)
    line((6.0, 2.65), (6.0, 4.5), stroke: (paint: by-open, thickness: 0.9pt, dash: "dashed"))
    content((6.65, 4.5), text(size: 6.5pt, fill: by-open)[seam $Delta_k$])
    content((2.55, 1.25), text(size: 6.4pt, fill: by-muted)[$I_1$: smooth transport])
    content((6.95, 2.1), text(size: 6.4pt, fill: by-muted)[$I_2$: rebased transport])

    rect((9.85, 0.25), (14.65, 5.7), radius: 5pt, fill: white, stroke: 0.7pt + by-rule)
    content((12.25, 5.25), text(size: 8pt, weight: "semibold")[one comparison fiber])
    circle((11.1, 3.95), radius: 0.1, fill: by-blue, stroke: none)
    line((11.1, 3.95), (12.2, 4.55), stroke: 1.25pt + by-blue, mark: (end: ">"))
    content((10.65, 3.55), text(size: 6.3pt)[$V(0)$])
    circle((11.1, 2.65), radius: 0.1, fill: by-red, stroke: none)
    line((11.1, 2.65), (12.05, 3.55), stroke: 1.25pt + by-red, mark: (end: ">"))
    content((10.45, 2.25), text(size: 6.3pt)[$cal(P)_(L arrow.r 0)V(L)$])
    line((12.55, 4.4), (13.25, 3.65), (12.55, 2.9),
      stroke: (paint: by-open, thickness: 0.85pt, dash: "dashed"),
      mark: (end: ">"))
    content((13.25, 2.3), text(size: 6.3pt, fill: by-open)[
      another path
      #linebreak()
      may return holonomy
    ])
    content((12.25, 1.1), text(size: 6.1pt, fill: by-muted)[
      parallel transport first;
      #linebreak()
      subtraction second
    ])
  }),
  caption: [
    Mean transport on a manifold is path-relative.  A scalar field admits a
    one-dimensional mean witness along the chosen $gamma$.  Bundle-valued
    states must first be parallel-transported into one fiber, and a discrete
    branch, rank, phase, or valuation seam contributes an explicit jump
    $Delta_k$.  Curvature becomes visible as path-dependent holonomy, not as
    an absolute coordinate bend.
  ],
)

#let conformal-rebase-atlas-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    // Completed orbit and its fixed/normal factorization.
    rect((0.15, 2.55), (4.55, 6.35), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((2.35, 5.98), text(size: 8pt, weight: "semibold")[completed orbit])
    line((2.35, 3.15), (2.35, 5.55), stroke: 1.55pt + by-blue)
    content((2.35, 2.88), text(size: 6.5pt, fill: by-blue)[$op("Fix")(J): op("Re")(s)=1/2$])
    let left = (1.25, 4.45)
    let fixed = (2.35, 4.45)
    let right = (3.45, 4.45)
    circle(left, radius: 0.11, fill: by-yellow, stroke: none)
    circle(fixed, radius: 0.11, fill: by-blue, stroke: none)
    circle(right, radius: 0.11, fill: by-red, stroke: none)
    line(left, right,
      stroke: (paint: by-open, thickness: 0.9pt, dash: "dashed"),
      mark: (end: ">"))
    content((1.25, 4.78), text(size: 6.4pt, fill: by-yellow)[$-epsilon$])
    content((2.35, 4.78), text(size: 6.4pt, fill: by-blue)[$P_"fix"$])
    content((3.45, 4.78), text(size: 6.4pt, fill: by-red)[$+epsilon$])
    content((2.35, 3.55), text(size: 6.7pt)[$s=1/2+epsilon+i t$])
    content((2.35, 3.25), text(size: 6.1pt, fill: by-muted)[
      $P_"normal"=epsilon$ retains oriented hand
    ])

    // Exact log-polar carrier; the visible spiral is derived from these lines.
    rect((5.05, 2.55), (9.45, 6.35), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((7.25, 5.98), text(size: 8pt, weight: "semibold")[logarithmic rebase])
    line((5.55, 4.35), (8.95, 4.35), stroke: 0.65pt + by-rule, mark: (end: ">"))
    line((7.25, 3.05), (7.25, 5.55), stroke: 0.65pt + by-rule, mark: (end: ">"))
    content((9.08, 4.18), text(size: 6.2pt)[$u$])
    content((7.47, 5.35), text(size: 6.2pt)[$epsilon u$])
    line((5.65, 3.5), (8.85, 5.2), stroke: 1.25pt + by-red)
    line((5.65, 5.2), (8.85, 3.5), stroke: 1.25pt + by-yellow)
    line((5.65, 4.35), (8.85, 4.35), stroke: 1.35pt + by-blue)
    content((8.45, 5.32), text(size: 6.2pt, fill: by-red)[$+epsilon$])
    content((8.55, 4.58), text(size: 6.2pt, fill: by-blue)[$0$])
    content((8.45, 3.36), text(size: 6.2pt, fill: by-yellow)[$-epsilon$])
    content((7.25, 2.88), text(size: 6.1pt, fill: by-muted)[
      same phase; reciprocal radius
    ])

    // Centered Cayley/Smith lift.
    rect((9.95, 2.55), (14.55, 6.35), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((12.25, 5.98), text(size: 8pt, weight: "semibold")[centered Smith shell])
    circle((11.65, 4.35), radius: 1.15, stroke: 0.8pt + by-rule)
    line((10.3, 4.35), (13.0, 4.35), stroke: 0.55pt + by-pale)
    line((11.65, 3.05), (11.65, 5.65), stroke: 0.7pt + by-open,
      mark: (end: ">"))
    content((11.93, 5.45), text(size: 6.1pt, fill: by-open)[normal])
    let upper = (12.2, 4.72)
    let lower = (12.2, 3.98)
    circle(upper, radius: 0.1, fill: by-yellow, stroke: none)
    circle(lower, radius: 0.1, fill: by-red, stroke: none)
    line(lower, upper, stroke: (paint: by-open, thickness: 0.8pt, dash: "dashed"))
    circle((10.55, 4.35), radius: 0.1, fill: by-blue, stroke: none)
    content((13.5, 4.82), text(size: 5.9pt, fill: by-yellow)[$(21,48,+8)/53$])
    content((13.5, 3.88), text(size: 5.9pt, fill: by-red)[$(21,48,-8)/53$])
    content((10.6, 3.05), text(size: 5.9pt, fill: by-blue)[
      $epsilon=0$
      #linebreak()
      unit shell
    ])

    line((4.6, 4.45), (4.98, 4.45), stroke: 1.15pt + by-black, mark: (end: ">"))
    line((9.5, 4.45), (9.88, 4.45), stroke: 1.15pt + by-black, mark: (end: ">"))

    // Four local germ events which a flattened crossing must not identify.
    rect((0.15, 0.0), (14.55, 2.15), radius: 5pt, fill: white, stroke: 0.7pt + by-rule)
    let centers = ((1.75, 0.95), (5.25, 0.95), (8.75, 0.95), (12.35, 0.95))
    for x in (3.5, 7.0, 10.55) {
      line((x, 0.2), (x, 1.95), stroke: 0.45pt + by-pale)
    }

    // Regular conformal crossing.
    let c0 = centers.at(0)
    line((1.15, 0.55), (2.35, 1.35), stroke: 1.15pt + by-blue)
    line((1.35, 1.55), (2.15, 0.35), stroke: 1.15pt + by-yellow)
    circle(c0, radius: 0.08, fill: by-black, stroke: none)
    content((1.75, 1.85), text(size: 6.4pt, weight: "semibold")[regular])
    content((1.75, 0.16), text(size: 5.8pt, fill: by-muted)[$F != 0, F' != 0$])

    // Simple zero: regular tangent plus radius collapse and winding.
    let c1 = centers.at(1)
    line((4.55, 0.95), (5.95, 0.95), stroke: 1.15pt + by-blue)
    line((5.25, 0.25), (5.25, 1.65), stroke: 1.15pt + by-yellow)
    circle(c1, radius: 0.11, fill: by-red, stroke: none)
    circle(c1, radius: 0.42, stroke: (paint: by-open, thickness: 0.65pt, dash: "dashed"))
    content((5.25, 1.85), text(size: 6.4pt, weight: "semibold")[simple zero])
    content((5.25, 0.16), text(size: 5.8pt, fill: by-muted)[$F=0, F' != 0$])

    // Nonzero critical branch.
    let c2 = centers.at(2)
    for p in ((8.1, 0.3), (8.1, 1.6), (9.4, 0.3), (9.4, 1.6)) {
      line(c2, p, stroke: 1.05pt + (if p.at(0) < 8.5 { by-blue } else { by-yellow }))
    }
    circle(c2, radius: 0.11, fill: by-open, stroke: none)
    content((8.75, 1.85), text(size: 6.4pt, weight: "semibold")[critical branch])
    content((8.75, 0.16), text(size: 5.8pt, fill: by-muted)[$F != 0, F'=0$])

    // Two source lineages meet one output but retain different hands.
    let out = (12.7, 0.95)
    circle((11.55, 1.45), radius: 0.1, fill: by-blue, stroke: none)
    circle((11.55, 0.45), radius: 0.1, fill: by-yellow, stroke: none)
    line((11.68, 1.42), out, stroke: 1.1pt + by-blue, mark: (end: ">"))
    line((11.68, 0.48), out, stroke: 1.1pt + by-yellow, mark: (end: ">"))
    circle(out, radius: 0.11, fill: by-red, stroke: none)
    content((12.35, 1.85), text(size: 6.4pt, weight: "semibold")[coincident output])
    content((12.35, 0.16), text(size: 5.8pt, fill: by-muted)[$z_1 != z_2, F(z_1)=F(z_2)$])
  }),
  caption: [
    The exact conformal-rebase carrier.  The completed involution first
    factors an occurrence into fixed and signed-normal parts.  The same
    normal coordinate becomes the real exponent of logarithmic rebase and
    the signed normal of the centered Smith sphere; its two nonzero hands
    retain reciprocal radius.  The lower strip keeps four local events
    distinct before any rendering: regular crossing, simple zero, critical
    branch, and distinct-source coincidence.
  ],
)

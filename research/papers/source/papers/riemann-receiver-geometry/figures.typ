#import "@preview/cetz:0.3.4"
#import "../../lib/elements.typ": by-red, by-blue, by-yellow, by-black, by-paper, by-pale, by-rule, by-muted, by-open

#let prime-valuation-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let o = (2.8, 2.4)
    let p2 = (6.0, 2.4)
    let p3 = (1.0, 4.75)
    let p5 = (1.0, 0.05)

    line(o, p2, stroke: 1.4pt + by-blue, mark: (end: ">"))
    line(o, p3, stroke: 1.4pt + by-yellow, mark: (end: ">"))
    line(o, p5, stroke: 1.4pt + by-red, mark: (end: ">"))
    circle(o, radius: 0.11, fill: by-black, stroke: none)
    content((2.8, 2.0), text(size: 7.5pt)[$1:0$])

    for item in (
      ((4.25, 2.4), by-blue, [$2:e_2$]),
      ((5.35, 2.4), by-blue, [$4:2e_2$]),
      ((1.9, 3.55), by-yellow, [$3:e_3$]),
      ((1.3, 4.3), by-yellow, [$9:2e_3$]),
      ((1.9, 1.25), by-red, [$5:e_5$]),
      ((1.3, 0.5), by-red, [$25:2e_5$]),
    ) {
      circle(item.at(0), radius: 0.09, fill: item.at(1), stroke: none)
      content((item.at(0).at(0) + 0.15, item.at(0).at(1) + 0.18),
        text(size: 7.2pt, fill: item.at(1))[#item.at(2)])
    }

    content((3.55, 5.08), text(size: 8pt, weight: "semibold")[valuation rays])
    content((3.55, -0.28), text(size: 7.2pt, fill: by-muted)[prime powers repeat one primitive axis])

    let a = (8.0, 0.35)
    let b = (11.1, 5.0)
    let c = (14.2, 0.35)
    line(a, b, c, close: true, fill: by-paper, stroke: 0.8pt + by-rule)

    for item in (
      (a, by-blue, [$X_2^2$], [$4$]),
      (b, by-yellow, [$X_3^2$], [$9$]),
      (c, by-red, [$X_5^2$], [$25$]),
      (((a.at(0)+b.at(0))/2, (a.at(1)+b.at(1))/2), by-black, [$X_2X_3$], [$6$]),
      (((b.at(0)+c.at(0))/2, (b.at(1)+c.at(1))/2), by-black, [$X_3X_5$], [$15$]),
      (((a.at(0)+c.at(0))/2, (a.at(1)+c.at(1))/2), by-black, [$X_2X_5$], [$10$]),
    ) {
      circle(item.at(0), radius: 0.10, fill: item.at(1), stroke: none)
      content((item.at(0).at(0), item.at(0).at(1) + 0.30),
        text(size: 7.1pt, fill: item.at(1))[#item.at(2)])
      content((item.at(0).at(0), item.at(0).at(1) - 0.28),
        text(size: 6.8pt, fill: by-muted)[#item.at(3)])
    }

    content((11.1, 5.45), text(size: 8pt, weight: "semibold")[degree-two face])
    content((11.1, -0.15), text(size: 7.2pt, fill: by-muted)[squares and mixed semiprimes share one graded simplex])
  }),
  caption: [
    Prime axes are primitive valuation directions. Prime powers are repeated traversal of one
    ray; products of distinct primes occupy mixed faces. This geometry is exact in the exponent
    lattice. It does not assert a Euclidean metric on the integers.
  ],
)

#let euler-chord-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let c = (3.5, 3.0)
    let one = (7.0, 3.0)
    let z = (5.15, 4.75)
    let radial = (5.15, 3.0)

    circle(c, radius: 3.5, stroke: (paint: by-rule, thickness: 0.7pt, dash: "dashed"))
    circle(c, radius: 2.48, stroke: 0.65pt + by-pale)
    line(c, one, stroke: 1.1pt + by-black)
    line(c, z, stroke: 1.2pt + by-yellow)
    line(z, one, stroke: 2.1pt + by-blue, mark: (end: ">"))
    line(z, radial, stroke: (paint: by-rule, thickness: 0.6pt, dash: "dashed"))
    circle(c, radius: 0.10, fill: by-black, stroke: none)
    circle(one, radius: 0.11, fill: by-red, stroke: none)
    circle(z, radius: 0.11, fill: by-yellow, stroke: none)

    content((3.5, 2.65), text(size: 7.2pt)[$0$])
    content((7.25, 2.9), text(size: 7.2pt, fill: by-red)[$1$])
    content((4.7, 5.05), text(size: 7.3pt, fill: by-yellow)[$p^(-sigma-i t)$])
    content((6.35, 4.15), text(size: 7.4pt, fill: by-blue)[$D_(p,sigma)(t)$])
    content((4.2, 3.95), text(size: 7pt, fill: by-yellow)[$p^(-sigma)$])
    content((5.15, 3.35), text(size: 7pt, fill: by-muted)[$t log p$])

    rect((8.1, 0.65), (14.5, 5.4), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.3, 4.85), text(size: 8.5pt, weight: "semibold")[one local Euler receiver])
    content((11.3, 4.1), text(size: 8pt)[$D_(p,sigma)(t)=1-p^(-sigma-i t)$])
    content((11.3, 3.4), text(size: 8pt)[$g_(p,sigma)(t)=abs(D_(p,sigma)(t))^2$])
    content((11.3, 2.45), text(size: 7.5pt, fill: by-muted)[radial change in $sigma$])
    line((9.25, 2.05), (13.35, 2.05), stroke: 1.1pt + by-red, mark: (end: ">"))
    content((11.3, 1.55), text(size: 7.6pt)[$partial_sigma log g$])
    content((11.3, 0.95), text(size: 7.2pt, fill: by-blue)[symmetric modes at $plus.minus m log p$])
  }),
  caption: [
    The Euler successor metric is a squared chord. Its endpoint rotates by $t log p$ while
    $sigma$ changes the radius. The logarithmic normal derivative of this chord metric expands
    into the complete repeated-prime current. This is the paper's central geometric derivation.
  ],
)

#let mellin-seam-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let x0 = 4.0
    line((0.3, 3.0), (8.0, 3.0), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line((x0, 0.25), (x0, 5.8), stroke: 1.6pt + by-blue, mark: (end: ">"))
    content((7.7, 2.65), text(size: 7.2pt)[$Re(z)$])
    content((4.25, 5.55), text(size: 7.2pt)[$Im(z)$])
    content((4.45, 0.55), text(size: 7.2pt, fill: by-blue)[fixed seam $z=i gamma$])

    let z = (6.35, 4.45)
    let jz = (1.65, 4.45)
    circle(z, radius: 0.12, fill: by-red, stroke: none)
    circle(jz, radius: 0.12, fill: by-yellow, stroke: none)
    line(z, jz, stroke: (paint: by-open, thickness: 1pt, dash: "dashed"), mark: (end: ">"))
    content((6.55, 4.6), text(size: 7.4pt, fill: by-red)[$z$])
    content((1.05, 4.6), text(size: 7.4pt, fill: by-yellow)[$J(z)=-overline(z)$])
    content((4.0, 4.85), text(size: 7pt, fill: by-open)[adjoint reflection])

    let seampt = (4.0, 1.65)
    circle(seampt, radius: 0.12, fill: by-blue, stroke: none)
    content((4.55, 1.65), text(size: 7.2pt, fill: by-blue)[$J(i gamma)=i gamma$])

    rect((8.65, 0.65), (14.6, 5.35), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.62, 4.75), text(size: 8.2pt, weight: "semibold")[returned Mellin face])
    content((11.62, 3.85), text(size: 7.7pt)[$A_f(z) overline(A_f(J(z)))$])
    line((9.45, 3.25), (13.8, 3.25), stroke: 0.7pt + by-rule)
    content((11.62, 2.65), text(size: 7.5pt, fill: by-blue)[on the seam])
    content((11.62, 1.95), text(size: 8.3pt, fill: by-blue)[$abs(A_f(i gamma))^2$])
    content((11.62, 1.25), text(size: 7.1pt, fill: by-muted)[fixed seam supplies the norm-square chart])
    content((11.62, 0.95), text(size: 7.1pt, fill: by-muted)[it does not locate every zero])
  }),
  caption: [
    Centering at $s=1/2$ turns the functional reflection into $J(z)=-overline(z)$. The critical
    line is its fixed locus, and only there does the returned Mellin pair become a norm square.
  ],
)

#let parametric-seam-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    line((0.4, 0.65), (6.25, 0.65), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line((0.9, 0.25), (0.9, 5.35), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line((3.2, 0.35), (3.2, 5.15), stroke: 1.5pt + by-blue)
    content((3.2, 5.48), text(size: 7.4pt, fill: by-blue)[$op("Fix")(J)$])
    content((5.85, 0.28), text(size: 7pt)[$op("Re")(s)$])

    line(
      (1.25, 1.1),
      (1.85, 1.65),
      (2.55, 2.0),
      (4.4, 2.65),
      (4.85, 3.45),
      (5.25, 4.65),
      stroke: 1.35pt + by-yellow,
      mark: (end: ">"),
    )
    circle((4.4, 2.65), radius: 0.11, fill: by-red, stroke: none)
    line((3.2, 2.65), (4.4, 2.65),
      stroke: (paint: by-red, thickness: 0.9pt, dash: "dashed"))
    content((3.8, 2.95), text(size: 7pt, fill: by-red)[$epsilon(t)$])
    content((1.8, 4.65), text(size: 7.3pt, fill: by-yellow)[$s(t)$])

    line((6.55, 2.75), (8.05, 2.75), stroke: 1.4pt + by-black, mark: (end: ">"))
    content((7.3, 3.1), text(size: 7.4pt)[$phi$])

    line((8.4, 0.65), (14.55, 0.65), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line((8.9, 0.25), (8.9, 5.35), stroke: 0.7pt + by-rule, mark: (end: ">"))
    line(
      (10.25, 0.4),
      (9.65, 1.25),
      (10.55, 2.05),
      (9.8, 2.9),
      (10.75, 3.75),
      (10.1, 5.15),
      stroke: 1.5pt + by-blue,
    )
    line(
      (9.35, 1.05),
      (10.15, 1.55),
      (11.4, 2.2),
      (12.55, 2.7),
      (13.15, 3.55),
      (13.65, 4.7),
      stroke: 1.35pt + by-yellow,
      mark: (end: ">"),
    )
    circle((12.55, 2.7), radius: 0.11, fill: by-red, stroke: none)
    content((11.95, 5.15), text(size: 7.3pt, fill: by-blue)[$op("Fix")(J_phi)$])
    content((12.55, 2.35), text(size: 7.2pt, fill: by-red)[$phi(s(t))$])
    content((11.65, 0.15), text(size: 6.9pt, fill: by-muted)[the fixed seam need not look straight])
  }),
  caption: [
    The real coordinate is one affine chart. The invariant object is the fixed seam of the
    completed antiholomorphic involution. A biholomorphic rechart conjugates both the
    trajectory and the seam; it does not move an off-seam point onto the seam.
  ],
)

#let response-bundle-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    line((1.0, 0.55), (13.9, 0.55), stroke: 1pt + by-black, mark: (end: ">"))
    content((13.3, 0.15), text(size: 7.2pt)[$gamma(t)$])

    for item in (
      (2.3, [$cal(H)_(lambda_0)$]),
      (7.3, [$cal(H)_(lambda_1)$]),
      (12.3, [$cal(H)_(lambda_2)$]),
    ) {
      let x = item.at(0)
      line((x, 0.55), (x, 4.95), stroke: 0.8pt + by-rule)
      line((x, 2.75), (x - 1.2, 4.35), stroke: 1.2pt + by-blue)
      line((x, 2.75), (x + 1.2, 4.35), stroke: 1.2pt + by-blue)
      line((x, 2.75), (x - 1.2, 1.15), stroke: 1.2pt + by-open)
      line((x, 2.75), (x + 1.2, 1.15), stroke: 1.2pt + by-open)
      circle((x + 0.55, 3.45), radius: 0.10, fill: by-blue, stroke: none)
      circle((x - 0.55, 2.05), radius: 0.10, fill: by-open, stroke: none)
      content((x, 5.25), text(size: 7.3pt, weight: "semibold")[#item.at(1)])
    }

    line((2.85, 3.45), (7.85, 3.45), stroke: 1pt + by-blue, mark: (end: ">"))
    line((7.85, 3.45), (12.85, 3.45), stroke: 1pt + by-blue, mark: (end: ">"))
    line((1.75, 2.05), (6.75, 2.05), stroke: 1pt + by-open, mark: (end: ">"))
    line((6.75, 2.05), (11.75, 2.05), stroke: 1pt + by-open, mark: (end: ">"))
    content((4.8, 3.78), text(size: 6.9pt, fill: by-blue)[positive direction])
    content((9.8, 1.72), text(size: 6.9pt, fill: by-open)[negative direction])
    content((7.3, 4.65), text(size: 7pt, fill: by-muted)[$W_mu(T f,T f)=c W_lambda(f,f), c>0$])
  }),
  caption: [
    A parametric response is a field of Hermitian geometries, not a sequence of detached
    scalars. Positive-congruence transport carries both positive and negative directions.
    Finding another positive direction is therefore insufficient; a proof must show that the
    exhaustive admitted bundle has no transported negative direction.
  ],
)

#let gaussian-family-figure() = figure(
  placement: none,
  block(
    width: 100%,
    fill: by-paper,
    stroke: 0.7pt + by-rule,
    inset: 10pt,
  )[
    #grid(
      columns: (1fr, auto, 1fr, auto, 1fr),
      column-gutter: 7pt,
      align: center,
      [
        #align(center)[
          *scale chart* $u$ \
          $g_u(x)=e^(u/2) exp(-pi e^(2u)x^2)$ \
          $a=e^(2u)$
        ]
      ],
      [$arrow.r^cal(F)$],
      [
        #align(center)[
          *reciprocal chart* \
          $cal(F)g_u=g_(-u)$ \
          $a arrow.r a^(-1)$
        ]
      ],
      [$arrow.r^cal(M)$],
      [
        #align(center)[
          *spectral chart* \
          $s arrow.r 1-s$ \
          $op("Fix")=1/2+i RR$
        ]
      ],
    )
    #v(7pt)
    #align(center)[
      #text(size: 7.3pt, fill: by-muted)[
        $u=0$ is the self-Fourier Gaussian seam; Mellin transport carries reciprocal
        scale into the completed zeta reflection.
      ]
    ]
  ],
  caption: [
    A parametric $pi$--$e$ bridge. Exponentiation turns additive log-scale $u$ into the
    multiplicative width $a$; $pi$ fixes the standard self-Fourier normalization.
    Reciprocal Gaussian scale is transported by Mellin analysis into the zeta reflection.
  ],
)

#let theta-boundary-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let xs = (1.4, 4.8)
    let xt = (5.2, 4.8)
    let ys = (1.4, 1.2)
    let yt = (5.2, 1.2)

    rect((0.1, 4.25), (2.7, 5.35), radius: 4pt, fill: by-paper, stroke: 0.7pt + by-blue)
    rect((3.9, 4.25), (6.5, 5.35), radius: 4pt, fill: by-paper, stroke: 0.7pt + by-yellow)
    rect((0.1, 0.65), (2.7, 1.75), radius: 4pt, fill: by-paper, stroke: 0.7pt + by-blue)
    rect((3.9, 0.65), (6.5, 1.75), radius: 4pt, fill: by-paper, stroke: 0.7pt + by-yellow)
    content(xs, text(size: 8pt)[$P_(d,N)$])
    content(xt, text(size: 8pt)[$T_(d,N)$])
    content(ys, text(size: 8pt)[$P_(r,N)$])
    content(yt, text(size: 8pt)[$T_(r,N)$])
    line((2.7, 4.8), (3.9, 4.8), stroke: 1pt + by-black, mark: (end: ">"))
    line((2.7, 1.2), (3.9, 1.2), stroke: 1pt + by-black, mark: (end: ">"))
    content((3.3, 5.15), text(size: 7pt)[$+$])
    content((3.3, 1.55), text(size: 7pt)[$+$])
    line((1.4, 4.25), (1.4, 1.75), stroke: 1.2pt + by-red, mark: (end: ">"))
    line((5.2, 4.25), (5.2, 1.75), stroke: 1.2pt + by-red, mark: (end: ">"))
    content((1.75, 3.0), text(size: 7.2pt, fill: by-red)[$J$])
    content((5.55, 3.0), text(size: 7.2pt, fill: by-red)[$J$])

    rect((7.6, 0.65), (14.6, 5.35), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((11.1, 4.75), text(size: 8.2pt, weight: "semibold")[aperture transfer $N arrow.r N+1$])
    content((11.1, 3.85), text(size: 7.7pt)[$P_(d,N+1)=P_(d,N)+2d_(N+1)$])
    content((11.1, 3.15), text(size: 7.7pt)[$T_(d,N+1)=T_(d,N)-2d_(N+1)$])
    content((11.1, 2.25), text(size: 7.7pt)[$P_(r,N+1)=P_(r,N)+2r_(N+1)$])
    content((11.1, 1.55), text(size: 7.7pt)[$T_(r,N+1)=T_(r,N)-2r_(N+1)$])
    content((11.1, 0.95), text(size: 7.1pt, fill: by-muted)[the complete chart stays fixed while its visible boundary moves])
  }),
  caption: [
    Finite theta truncations are not self-dual. Direct and reciprocal partials become equal
    only after their generative tails are included. Aperture growth transfers the same shell
    across the finite/remainder boundary in both charts.
  ],
)

#let support-place-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    line((0.7, 0.75), (14.3, 0.75), stroke: 1pt + by-black, mark: (end: ">"))
    line((0.7, 0.75), (0.7, 5.5), stroke: 1pt + by-black, mark: (end: ">"))
    content((13.7, 0.35), text(size: 7.4pt)[$R$ — support aperture])
    content((0.25, 5.25), text(size: 7.4pt)[places])

    let seams = (
      (2.2, [$log 2$], by-blue),
      (3.5, [$log 3$], by-yellow),
      (4.7, [$2 log 2$], by-blue),
      (6.0, [$log 5$], by-red),
      (7.1, [$log 7$], by-open),
      (8.25, [$3 log 2$], by-blue),
      (9.55, [$2 log 3$], by-yellow),
      (11.0, [$log 11$], by-black),
      (12.4, [$log 13$], by-muted),
    )

    for s in seams {
      line((s.at(0), 0.75), (s.at(0), 4.85),
        stroke: (paint: s.at(2), thickness: 0.7pt, dash: "dashed"))
      circle((s.at(0), 1.15), radius: 0.08, fill: s.at(2), stroke: none)
      content((s.at(0), 0.15), text(size: 6.5pt, fill: s.at(2))[#s.at(1)])
    }

    line(
      (0.7, 1.15),
      (2.2, 1.15),
      (2.2, 1.75),
      (3.5, 1.75),
      (3.5, 2.35),
      (6.0, 2.35),
      (6.0, 2.95),
      (7.1, 2.95),
      (7.1, 3.55),
      (11.0, 3.55),
      (11.0, 4.15),
      (12.4, 4.15),
      stroke: 2pt + by-blue,
      mark: (end: ">"),
    )
    content((3.0, 4.75), text(size: 7.6pt, weight: "semibold")[finite-place receiver $S(R)$])
    content((9.0, 4.75), text(size: 7.1pt, fill: by-muted)[prime powers enter at $m log p <= R$])
  }),
  caption: [
    Support and place form two coupled axes. Increasing $R$ admits discrete prime-power
    incidences but also continuously enlarges an infinite-dimensional test aperture. The
    staircase records which finite places are required; it is not a finite-dimensional proof.
  ],
)

#let successor-metric-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    rect((0.3, 0.55), (6.2, 5.25), radius: 6pt, fill: by-paper, stroke: 0.8pt + by-rule)
    content((3.25, 4.75), text(size: 8.2pt, weight: "semibold")[predecessor chart $H_S$])
    line((1.0, 1.4), (5.5, 1.4), stroke: 2pt + by-blue, mark: (end: ">"))
    line((3.2, 0.9), (3.2, 4.15), stroke: 1pt + by-black, mark: (end: ">"))
    content((5.2, 1.08), text(size: 7.2pt, fill: by-blue)[$op("range")(P)$])
    content((3.6, 3.8), text(size: 7.2pt)[$P^perp$])

    line((3.2, 1.4), (4.45, 3.9), stroke: 1.5pt + by-red, mark: (end: ">"))
    content((4.85, 3.65), text(size: 7.2pt, fill: by-red)[$ker(Pi_p)$])
    content((4.65, 2.45), text(size: 7pt, fill: by-red)[$G_p$-orthogonal])
    line((3.2, 1.4), (4.0, 1.4), stroke: 2.5pt + by-yellow)
    content((2.0, 2.4), text(size: 7.1pt, fill: by-muted)[same range])
    content((2.0, 2.05), text(size: 7.1pt, fill: by-muted)[different complement])

    line((6.55, 2.9), (8.25, 2.9), stroke: 1.6pt + by-blue, mark: (end: ">"))
    content((7.4, 3.25), text(size: 7.4pt, fill: by-blue)[$J_(S,p)$])

    rect((8.6, 0.55), (14.5, 5.25), radius: 6pt, fill: by-paper, stroke: 0.8pt + by-rule)
    content((11.55, 4.75), text(size: 8.2pt, weight: "semibold")[successor receiver $H_(S union {p})$])
    line((9.3, 1.4), (13.8, 1.4), stroke: 2pt + by-blue, mark: (end: ">"))
    line((11.55, 1.4), (13.1, 4.0), stroke: 1.4pt + by-red, mark: (end: ">"))
    content((13.3, 3.75), text(size: 7.2pt, fill: by-red)[native orthogonal])
    content((11.55, 0.95), text(size: 7.2pt, fill: by-muted)[$G_p=J^*J$ records the rebase])
  }),
  caption: [
    A new prime does not append an untouched block. The whole receiver is transported. In the
    predecessor chart the Sonin range can be the same vector subspace while its orthogonal
    complement turns under the pulled-back Euler metric.
  ],
)

#let defect-recurrence-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    let d0 = (1.2, 3.0)
    let w = (5.0, 4.8)
    let k = (5.0, 1.2)
    let d1 = (9.0, 3.0)
    circle(d0, radius: 0.18, fill: by-blue, stroke: none)
    circle(w, radius: 0.18, fill: by-red, stroke: none)
    circle(k, radius: 0.18, fill: by-yellow, stroke: none)
    circle(d1, radius: 0.18, fill: by-black, stroke: none)
    line(d0, d1, stroke: 2pt + by-blue, mark: (end: ">"))
    line(w, d1, stroke: 1.5pt + by-red, mark: (end: ">"))
    line(k, d1, stroke: 1.5pt + by-yellow, mark: (end: ">"))
    content((1.2, 3.45), text(size: 7.6pt, fill: by-blue)[$D_S$])
    content((5.0, 5.2), text(size: 7.6pt, fill: by-red)[$-W_p$])
    content((5.0, 0.75), text(size: 7.6pt, fill: by-yellow)[$-kappa_(S,p)$])
    content((9.0, 3.45), text(size: 7.6pt)[$D_(S union {p})$])

    rect((10.0, 0.75), (14.6, 5.2), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((12.3, 4.55), text(size: 8.1pt, weight: "semibold")[two coupled changes])
    content((12.3, 3.6), text(size: 7.5pt, fill: by-red)[explicit prime-power return])
    content((12.3, 2.75), text(size: 7.5pt, fill: by-yellow)[receiver-aperture turn])
    line((10.75, 2.25), (13.85, 2.25), stroke: 0.7pt + by-rule)
    content((12.3, 1.7), text(size: 7.4pt)[neither term has a required local sign])
    content((12.3, 1.15), text(size: 7.1pt, fill: by-open)[the completed endpoint sign is open])
  }),
  caption: [
    The exact one-prime balance. Adjoining $p$ changes both the explicit arithmetic response
    and the receiver which measures the positive Sonin return. The missing theorem must control
    their completed balance; positivity of either local ingredient alone is insufficient.
  ],
)

#let proof-spine-figure() = figure(
  placement: none,
  block(
    width: 100%,
    fill: by-paper,
    stroke: 0.7pt + by-rule,
    inset: 9pt,
  )[
    #let stage(title, status, face, open: false) = block(
      width: 100%,
      height: 7.3em,
      fill: if open { by-open.transparentize(91%) } else { white.transparentize(35%) },
      stroke: 0.45pt + if open { by-open } else { by-rule },
      inset: (x: 5pt, y: 5pt),
    )[
      #align(center)[
        #text(size: 7.4pt, weight: "semibold", fill: if open { by-open } else { by-black })[#title]
        #v(4pt)
        #text(size: 6.6pt, weight: "bold", fill: if open { by-open } else { by-muted })[#smallcaps[#status]]
        #v(5pt)
        #text(size: 7.2pt)[#face]
      ]
    ]

    #grid(
      columns: (1fr, auto, 1fr, auto, 1fr, auto, 1fr),
      column-gutter: 4pt,
      align: center,
      stage([Euler / theta completion], [classical], [$p^m, Gamma, pi$]),
      [$arrow.r$],
      stage([Mellin adjoint seam], [exact identity], [$J(z)=-overline(z)$]),
      [$arrow.r$],
      stage([Weil explicit formula], [classical equivalence], [$Q_W=sum_rho cal(M)h(rho)$]),
      [$arrow.r$],
      stage([exhaustive sign-preserving atlas], [open], [$Q_W(f)>=0$ in every carried fiber], open: true),
    )
    #v(6pt)
    #align(center)[
      #text(size: 7.2pt, fill: by-muted)[
        A positive chart is a base cell. Exhaustive covariant transport is the missing bridge.
      ]
    ]
  ],
  caption: [
    The proof spine and its stopping condition. Everything to the left of the final arrow is
    either classical or derived exactly in this paper. The final global sign is the
    coordinate expression of an exhaustive transported-cone statement and remains unproved.
  ],
)

#let coarea-carrier-figure() = figure(
  placement: none,
  cetz.canvas(length: 1cm, padding: 0.25, {
    import cetz.draw: *

    // Cartesian/polar fiber panel.
    rect((0.15, 0.45), (4.65, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((2.4, 5.0), text(size: 8pt, weight: "semibold")[polar fiber])
    let o = (2.35, 2.6)
    circle(o, radius: 0.09, fill: by-red, stroke: none)
    circle(o, radius: 0.85, stroke: 0.7pt + by-pale)
    circle(o, radius: 1.55, stroke: 1.2pt + by-blue)
    line(o, (3.65, 3.45), stroke: 1.1pt + by-yellow, mark: (end: ">"))
    content((3.75, 3.7), text(size: 7pt, fill: by-yellow)[$r$])
    content((2.35, 0.63), text(size: 7pt, fill: by-blue)[$dif A=r dif r dif theta$])
    content((2.35, 1.02), text(size: 6.8pt, fill: by-red)[$r=0$: rank seam])

    // Logarithmic half-density panel.
    line((4.95, 2.95), (5.75, 2.95), stroke: 1.2pt + by-black, mark: (end: ">"))
    content((5.35, 3.27), text(size: 6.8pt)[$r=e^u$])
    rect((5.95, 0.45), (10.35, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((8.15, 5.0), text(size: 8pt, weight: "semibold")[half-Jacobian chart])
    for y in (1.35, 2.25, 3.15, 4.05) {
      line((6.55, y), (9.75, y), stroke: 0.65pt + by-pale)
    }
    line((7.0, 0.95), (7.0, 4.55), stroke: 1pt + by-blue, mark: (end: ">"))
    line((7.0, 2.75), (9.35, 2.75), stroke: 1pt + by-yellow, mark: (end: ">"))
    content((7.3, 4.35), text(size: 6.8pt, fill: by-blue)[$theta$])
    content((9.45, 2.48), text(size: 6.8pt, fill: by-yellow)[$u$])
    content((8.15, 1.0), text(size: 7pt)[$cal(U)f=e^(u/2)f(e^u)$])
    content((8.15, 0.68), text(size: 6.6pt, fill: by-muted)[square-root Jacobian preserves the norm])

    // Contemporary carrier path panel.
    line((10.65, 2.95), (11.35, 2.95), stroke: 1.2pt + by-black, mark: (end: ">"))
    rect((11.55, 0.45), (16.0, 5.45), radius: 5pt, fill: by-paper, stroke: 0.7pt + by-rule)
    content((13.78, 5.0), text(size: 8pt, weight: "semibold")[changing receiver])
    let a = (12.2, 2.7)
    let b = (13.75, 3.55)
    let c = (15.35, 2.25)
    circle(a, radius: 0.13, fill: by-blue, stroke: none)
    circle(b, radius: 0.13, fill: by-yellow, stroke: none)
    circle(c, radius: 0.13, fill: by-red, stroke: none)
    line(a, b, stroke: 1.2pt + by-open, mark: (end: ">"))
    line(b, c, stroke: 1.2pt + by-open, mark: (end: ">"))
    content((12.0, 2.25), text(size: 6.6pt, fill: by-blue)[$norm(Psi_0)^2>=0$])
    content((13.55, 3.95), text(size: 6.6pt, fill: by-yellow)[$norm(Psi_1)^2>=0$])
    content((15.2, 1.8), text(size: 6.6pt, fill: by-red)[$norm(Psi_2)^2>=0$])
    content((12.95, 2.98), text(size: 6.4pt, fill: by-open)[$2 Re chevron.l Psi,nabla Psi chevron.r$])
    content((14.7, 3.05), text(size: 6.4pt, fill: by-open)[$Delta_p$ may change sign])
    content((13.78, 0.72), text(size: 6.5pt, fill: by-muted)[positive endpoints do not require positive local increments])
  }),
  caption: [
    The coarea carrier has three inseparable faces. A coordinate fiber carries its induced
    measure; a chart change moves the Jacobian into the amplitude as a half-density; and a
    path of contemporary receivers carries nonnegative endpoint norms through generally signed
    connection currents and discrete seams.
  ],
)

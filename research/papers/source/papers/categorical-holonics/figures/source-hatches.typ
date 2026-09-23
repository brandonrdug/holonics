#import "@preview/cetz:0.3.4"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-paper, by-muted

#set page(width: 10in, height: 6in, margin: (x: 1in/2, y: 1in/2), fill: white)
#set text(font: ("C059", "DejaVu Serif"), size: 10pt)
#set par(first-line-indent: 0pt, justify: false)
#show figure.caption: set text(size: 9pt)

#figure(
  placement: none,
  align(center, grid(
    columns: (1fr, 1fr),
    column-gutter: 1in/2,
    align: center,
    [
      #cetz.canvas(length: 1cm, padding: 1, {
        import cetz.draw: *
        rect((0, 0), (4, 4), stroke: 1pt + by-black, fill: by-paper)
        for k in range(5) {
          line((k, 0), (k, 4), stroke: 1pt + by-blue)
          line((0, k), (4, k), stroke: 1pt + by-red)
        }
        circle((2, 2), radius: 1/10, fill: by-black, stroke: none)
        content((2, 9/2), text(size: 9pt)[$B_0$ at $1/2+14i$])
        content((2, -1/2), text(size: 8pt)[$r_0=1/10^8$])
      })
    ],
    [
      #fletcher.diagram(
        node-stroke: none,
        edge-stroke: 1pt + by-black,
        spacing: (5em, 4em),
        node((0, 0), [EM jet], stroke: none),
        node((2, 0), [certified $B_R$], stroke: none),
        node((0, 1), [$("Re" zeta, "Im" zeta)$], stroke: none),
        node((2, 1), [winding $=1$], stroke: none),
        edge((0, 0), (2, 0), "->", [release]),
        edge((0, 0), (0, 1), "->", [dual]),
        edge((2, 0), (2, 1), "->", [boundary]),
        edge((0, 1), (2, 1), "->", [argument]),
      )
    ],
  )),
  caption: [
    *Exact zeta source and two coholon hatch directions.*
    The blue and red lines are a rational subdivision of the supplied
    initial square, read by the real and imaginary jet coholons.
    They are not guessed contour levels. The actual source is an
    Euler–Maclaurin generator with $N=24$, order $M=12$, 96-bit dyadic
    enclosures, and an explicit remainder. Its separately certified
    receiving square has radius $1/10^4$, contraction
    $q <= 45/4096$, and independent winding one. The map between
    squares retains the full interval jet and its source.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, grid(
    columns: (1fr, auto, 1fr),
    column-gutter: 1in/4,
    align: center,
    [
      #cetz.canvas(length: 1cm, padding: 1, {
        import cetz.draw: *
        rect((0, 0), (4, 4), stroke: 1pt + by-black)
        for k in range(1, 4) {
          line((0, k), (4, k), stroke: 1pt + by-blue)
          line((k, 0), (k, 4), stroke: 1pt + by-red)
        }
        line((0, 2), (4, 2), stroke: 1pt + by-black, mark: (end: ">"))
        line((2, 0), (2, 4), stroke: 2pt + by-red)
        circle((2, 3), radius: 1/10, fill: by-black, stroke: none)
        content((2, 9/2), text(size: 9pt)[harmonic $(0,1)$])
      })
    ],
    [#text(size: 16pt)[$S:(x,y) mapsto (x+y,y)$]],
    [
      #cetz.canvas(length: 1cm, padding: 1, {
        import cetz.draw: *
        rect((0, 0), (4, 4), stroke: 1pt + by-black)
        for k in range(1, 4) {
          line((0, k), (4, k), stroke: 1pt + by-blue)
        }
        line((0, 1), (3, 4), stroke: 1pt + by-red)
        line((0, 0), (4, 4), stroke: 2pt + by-red)
        line((1, 0), (4, 3), stroke: 1pt + by-red)
        line((0, 2), (4, 2), stroke: 1pt + by-black, mark: (end: ">"))
        line((2, 3), (3, 3), stroke: 1pt + by-yellow, mark: (end: ">"))
        circle((3, 3), radius: 1/10, fill: by-black, stroke: none)
        content((2, 9/2), text(size: 9pt)[sheared $(1,1)$])
      })
    ],
  )),
  caption: [
    *Exact finite Hodge class under a cochain generator.*
    Horizontal blue hatches are class fibres modulo the exact horizontal
    axis. Red hatches are the original cochain coordinates and their
    exact shear. The harmonic representative $(0,1)$ maps to $(1,1)$,
    outside the original harmonic subspace; the gold difference is
    exact, so both read the same cohomology class. This is proved in
    Foundation/HodgeReceiver.lean. The global cycle-class surjectivity
    question remains separate.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, grid(
    columns: (1fr, 1fr),
    column-gutter: 1in/2,
    align: center,
    [
      #cetz.canvas(length: 1cm, padding: 1, {
        import cetz.draw: *
        rect((0, 0), (4, 4), stroke: 1pt + by-black, fill: by-paper)
        for k in range(5) {
          line((k, 0), (k, 4), stroke: 1pt + by-blue)
          line((0, k), (4, k), stroke: 1pt + by-red)
        }
        line((0, 0), (4, 0), stroke: 1pt + by-black, mark: (end: ">"))
        line((0, 0), (0, 4), stroke: 1pt + by-black, mark: (end: ">"))
        content((2, 9/2), text(size: 9pt)[$x=0$ face])
        content((4, -1/2), text(size: 8pt)[$y$])
        content((-1/2, 4), text(size: 8pt)[$z$])
        content((2, 2), text(size: 9pt)[$d y ∧ d z$])
      })
    ],
    [
      #grid(
        columns: (1fr,),
        row-gutter: 1in/8,
        [*A symbolic face of the complex flux Holon*],
        [$U=a+i b$],
        [$a=(0,sin x+sin z,0)$],
        [$b=(sin y,0,sin x)$],
        [$C=U times (nabla times U)$],
        [$F_x^x=C_x U_x-nu partial_x C_x$],
        [On $x=0$:],
        [$"Re" F_x^x=sin z sin y cos y$],
        [$"Im" F_x^x=sin z sin y+nu cos y$],
      )
    ],
  )),
  caption: [
    *Complex Euler and Navier–Stokes flux as an exact series generator.*
    The blue and red hatch directions are the ordered $y$ and $z$
    phase generators on one oriented face; their wedge supplies
    its area blade. The displayed normal flux follows symbolically
    from a divergence-free $U=a+i b$. Euler is $nu=0$; viscosity
    adds the exact $i nu cos y$ term. Sine and cosine here denote
    their convergent power-series generators, not sampled floats.
    This datum is kinematic; a time-dependent PDE solution and
    terminal continuation are further Holon laws.
  ],
)


#pagebreak()

#figure(
  placement: none,
  align(center, grid(
    columns: (1fr, 1fr),
    column-gutter: 1in,
    align: center,
    [
      #fletcher.diagram(
        node-stroke: none,
        edge-stroke: 1pt + by-black,
        spacing: (5em, 4em),
        node((0, 0), [$H_l^"ext"$], stroke: none),
        node((2, 0), [$H_l^"ext"$], stroke: none),
        node((0, 1), [$R_l$], stroke: none),
        node((2, 1), [$R_l$], stroke: none),
        edge((0, 0), (2, 0), "->", [$T_w$ state]),
        edge((0, 0), (0, 1), "->", [$rho_R$ observe]),
        edge((2, 0), (2, 1), "->", [$rho_R$ observe]),
        edge((0, 1), (2, 1), "->", [receiver transport?]),
      )
    ],
    [
      #fletcher.diagram(
        node-stroke: none,
        edge-stroke: 1pt + by-black,
        spacing: (5em, 4em),
        node((0, 0), [$H_(l+1)^"ext"$], stroke: none),
        node((2, 0), [$H_(l+1)^"ext"$], stroke: none),
        node((0, 1), [$H_l^"ext"$], stroke: none),
        node((2, 1), [$H_l^"ext"$], stroke: none),
        edge((0, 0), (2, 0), "->", [$T_(l+1,w)$]),
        edge((0, 0), (0, 1), "->", [$pi_l$]),
        edge((2, 0), (2, 1), "->", [$pi_l$]),
        edge((0, 1), (2, 1), "->", [$T_(l,w)$]),
      )
    ],
  )),
  caption: [
    *The exterior Holon as state, observer and scale object.*
    $H_l^"ext"$ is the exterior realization of the foundational Holon,
    including incidence, ports, Dirac interconnection, constitution,
    generator word $w$ and restriction. The left square asks whether a
    receiving Holon has its own compatible transport; it is not assumed.
    The right square compares action with restriction. Its failure is
    the typed defect $delta_(l,w)=pi_l T_(l+1,w)-T_(l,w) pi_l$.
    An exact square is a proved property of a source-conforming Holon,
    not a numerical tolerance or a separately imposed estimate.
  ],
)

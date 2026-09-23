#import "@preview/cetz:0.3.4"
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../../lib/elements.typ": by-blue, by-red, by-yellow, by-black, by-paper, by-muted

#set page(width: 10in, height: 6in, margin: (x: 1in/2, y: 1in/2), fill: white)
#set text(font: ("C059", "DejaVu Serif"), size: 10pt)
#set par(first-line-indent: 0pt, justify: false)
#show figure.caption: set text(size: 9pt)

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1cm, padding: 1, {
    import cetz.draw: *
    let p(x, y, z) = (x, y, z)
    ortho(x: 30deg, y: 20deg, z: 0deg, sorted: false, cull-face: none, {
      for z in (0, 2) {
        line(p(0, 0, z), p(4, 0, z), p(4, 4, z), p(0, 4, z),
          close: true, stroke: 1pt + by-black)
      }
      for x in (0, 4) {
        for y in (0, 4) {
          line(p(x, y, 0), p(x, y, 2), stroke: 1pt + by-black)
        }
      }
      line(p(2, 0, 0), p(2, 4, 0), p(2, 4, 2), p(2, 0, 2),
        close: true, stroke: 1pt + by-yellow,
        fill: by-yellow.transparentize(90%))
      // Exact rational area chart on a tau-section, not an authored zero path.
      for k in range(5) {
        line(p(2 + k/2, 0, 1), p(2 + k/2, 4, 1),
          stroke: 1pt + by-blue)
        line(p(2, k, 1), p(4, k, 1),
          stroke: 1pt + by-red)
      }
      content(p(2, -1, 1), text(size: 9pt)[$sigma=1/2$])
      content(p(4, 0, 0), text(size: 9pt)[$sigma$])
      content(p(0, 4, 0), text(size: 9pt)[$t$])
      content(p(0, 0, 2), text(size: 9pt)[$tau$])
      content(p(3, 4, 1), text(size: 9pt)[$d sigma ∧ d t$])
    })
  })),
  caption: [
    *RH: a three-dimensional exterior receiver.*
    The source is $F_tau(s)="heatE"(-tau,xi,s)$ on
    $(sigma,t,tau)$. The gold critical plane is fixed by
    $J(s)=1-overline(s)$. The cross-hatch is an exact rational chart
    for integrating $d sigma ∧ d t$ on one section; it depicts no
    invented zero path. The source phase coholon
    $a_F=(2pi)^(-1) "Im"(d F/F)$ and zero current $Z_F=d a_F$
    determine which oriented faces have zero intersections.
    The global normal class is a question about this source Holon.
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
        let q(s, t) = (3*s+t, s+3*t)
        line(q(0,0), q(1,0), q(1,1), q(0,1), close: true,
          stroke: 1pt + by-black, fill: by-paper)
        for k in range(5) {
          let u = k/4
          line(q(u,0), q(u,1), stroke: 1pt + by-blue)
          line(q(0,u), q(1,u), stroke: 1pt + by-red)
        }
        line(q(0,0), q(1,0), stroke: 1pt + by-black, mark: (end: ">"))
        line(q(0,0), q(0,1), stroke: 1pt + by-black, mark: (end: ">"))
        content((2, 5), text(size: 9pt)[$p_1 ∧ p_2$])
        content((2, -1), text(size: 9pt)[$"det"(P^T P)=64$])
      })
    ],
    [
      #fletcher.diagram(
        node-stroke: none,
        edge-stroke: 1pt + by-black,
        spacing: (5em, 4em),
        node((0, 0), [$Z^p(X)_QQ$], stroke: none),
        node((2, 0), [$H^(2p)(X,QQ) ∩ H^(p,p)$], stroke: none),
        node((0, 1), [$H_(2n-2p)(X,QQ)$], stroke: none),
        node((2, 1), [harmonic $2p$-forms], stroke: none),
        edge((0, 0), (2, 0), "->", [cycle class]),
        edge((0, 0), (0, 1), "->", [fundamental]),
        edge((0, 1), (2, 1), "->", [PD + harmonic]),
        edge((2, 0), (2, 1), "->", [metric choice]),
      )
    ],
  )),
  caption: [
    *Hodge: an exact exterior blade beside the cycle-class square.*
    The supplied integer tangents are $p_1=(3,1)$ and $p_2=(1,3)$;
    their oriented area is $8$ and Gram determinant $64$.
    The hatch families follow their rational quarter subdivisions.
    A codimension-$p$ algebraic cycle enters the square through its
    $(2n-2p)$-dimensional fundamental class and degree-$2p$
    Poincaré dual. Whether every rational $(p,p)$ class comes from
    this cycle morphism remains the global Hodge question.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, cetz.canvas(length: 1cm, padding: 1, {
    import cetz.draw: *
    let p(x, y, z) = (x, y, z)
    ortho(x: 30deg, y: 20deg, z: 0deg, sorted: false, cull-face: none, {
      for x in (0, 2, 4) {
        for y in (0, 2) {
          line(p(x, y, 0), p(x, y, 2), stroke: 1pt + by-black)
        }
        for z in (0, 2) {
          line(p(x, 0, z), p(x, 2, z), stroke: 1pt + by-black)
        }
      }
      for y in (0, 2) {
        for z in (0, 2) {
          line(p(0, y, z), p(4, y, z), stroke: 1pt + by-black)
        }
      }
      line(p(2, 0, 0), p(2, 2, 0), p(2, 2, 2), p(2, 0, 2),
        close: true, stroke: 1pt + by-yellow,
        fill: by-yellow.transparentize(90%))
      for k in range(5) {
        line(p(2, k/2, 0), p(2, k/2, 2),
          stroke: 1pt + by-blue)
        line(p(2, 0, k/2), p(2, 2, k/2),
          stroke: 1pt + by-red)
      }
      line(p(1, 1, 1), p(2, 1, 1),
        stroke: 2pt + by-blue, mark: (end: ">"))
      line(p(3, 1, 1), p(2, 1, 1),
        stroke: 2pt + by-red, mark: (end: ">"))
      content(p(1, 3, 0), text(size: 9pt)[$Omega_L$])
      content(p(3, 3, 0), text(size: 9pt)[$Omega_R$])
      content(p(2, 3, 1), text(size: 9pt)[$Sigma$])
      content(p(2, -1, 1), text(size: 9pt)[$beta_i=iota_(F_i) "vol"$])
    })
  })),
  caption: [
    *Euler and Navier–Stokes: exact face incidence and volume balance.*
    The blue/red rational hatch directions span the shared oriented
    two-face. For one Lamb-current component, $beta_i=iota_(F_i) "vol"_3$
    is its flux form; the two volumes see opposite orientations of
    the same face. When their actual traces agree, interconnection
    cancels that port. The state law is
    $partial_t(c_i "vol"_3)+d beta_i=S_i "vol"_3$.
    The current Lean two-cell theorem proves this gluing from local
    balances; translated physical cells and complex source dynamics
    require their own conformance maps.
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
        let levels = (
          ((0, 1),),
          ((0, 1/3), (2/3, 1)),
          ((0, 1/9), (2/9, 1/3), (2/3, 7/9), (8/9, 1)),
          ((0, 1/27), (2/27, 1/9), (2/9, 7/27), (8/27, 1/3),
           (2/3, 19/27), (20/27, 7/9), (8/9, 25/27), (26/27, 1)),
        )
        for j in range(4) {
          let row = levels.at(j)
          let y = 3 - j
          for k in range(row.len()) {
            let c = row.at(k)
            let a = c.at(0)
            let b = c.at(1)
            if j > 0 {
              let parent = levels.at(j - 1).at(calc.floor(k/2))
              let mid = (parent.at(0) + parent.at(1))/2
              line((4*mid, y + 1), (2*(a+b), y),
                stroke: 1pt + by-muted)
            }
            line((4*a, y), (4*b, y), stroke: 2pt + by-blue)
          }
        }
        content((2, 4), text(size: 9pt)[ordered thirds])
        content((2, -1), text(size: 9pt)[$"width"(g_w I)=3^(-|w|)$])
      })
    ],
    [
      #fletcher.diagram(
        node-stroke: none,
        edge-stroke: 1pt + by-black,
        spacing: (5em, 4em),
        node((0, 0), [fine local faces], stroke: none),
        node((2, 0), [fine joined region], stroke: none),
        node((0, 1), [coarse local face], stroke: none),
        node((2, 1), [coarse joined region], stroke: none),
        edge((0, 0), (2, 0), "->", [glue]),
        edge((0, 0), (0, 1), "->", [restrict]),
        edge((2, 0), (2, 1), "->", [restrict]),
        edge((0, 1), (2, 1), "->", [glue]),
      )
    ],
  )),
  caption: [
    *Fractal generator and the local/global descent square.*
    The exact addressed branches are $g_L(x)=x/3$ and
    $g_R(x)=(x+2)/3$. Each word has length $3^(-|w|)$;
    their combined child width is exactly $2/3$ of the parent.
    The right square asks whether spatial gluing commutes with
    grain restriction as a Holon law. A noncommuting face keeps its
    defect. The infinite receiver is a compatible continuation
    through the actual source tower, not an external majorant.
  ],
)


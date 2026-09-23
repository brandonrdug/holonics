#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "../../../lib/holonics.typ": rule-gray, open-gray

// Native Typst category diagrams. All vertices are mathematical labels.
// Black arrows are declared maps; a centre 2-cell names a comparison.
// Status is stated in the caption rather than implied by the drawing.

#set page(width: 7.6in, height: 3.1in, margin: (x: 0.46in, y: 0.25in), fill: white)
#set text(font: ("C059", "DejaVu Serif"), size: 10.5pt)
#set par(first-line-indent: 0pt, justify: false)
#show figure.caption: set text(size: 9pt)

#figure(
  placement: none,
  align(center, fletcher.diagram(
    node-stroke: none,
    edge-stroke: 0.78pt + black,
    spacing: (8.9em, 5.0em),
    node((0, 0), [$Omega_A times_M Omega_R$], stroke: none),
    node((1, 0), [$Omega_R$], stroke: none),
    node((0, 1), [$Omega_A$], stroke: none),
    node((1, 1), [$M$], stroke: none),
    edge((0, 0), (1, 0), "-|>", [$p_R$]),
    edge((0, 0), (0, 1), "-|>", [$p_A$]),
    edge((1, 0), (1, 1), "-|>", [$s_R$]),
    edge((0, 1), (1, 1), "-|>", [$t_A$]),
    node((0.19, 0.18), [⌟], stroke: none),
  )),
  caption: [
    *Serial Holon composition.* The occurrence population is the pullback
    $Omega_A times_M Omega_R$: only pairs with $t_A(omega_A)=s_R(omega_R)$ join.
    The paired source fibre remains present. *Formal scope:* proved for the occurrence Holon.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, fletcher.diagram(
    node-stroke: none,
    edge-stroke: 0.78pt + black,
    spacing: (8.6em, 5.0em),
    node((0, 0), [$X_f$], stroke: none),
    node((1, 0), [$X_f$], stroke: none),
    node((0, 1), [$X_c$], stroke: none),
    node((1, 1), [$X_c$], stroke: none),
    edge((0, 0), (1, 0), "-|>", [$T_f(a)$]),
    edge((0, 0), (0, 1), "-|>", [$pi$]),
    edge((1, 0), (1, 1), "-|>", [$pi$]),
    edge((0, 1), (1, 1), "-|>", [$T_c(a)$]),
  )),
  caption: [
    *Fine to coarse naturality.* A microscopic to macroscopic reduction is an instance
    when $pi T_f(a)=T_c(a) pi$ for the admitted action $a$.
    A coarse state in the image of $pi$ has a fine fibre $pi^(-1)(x_c)$; a later receiver may
    distinguish its members. *Formal scope:* the linear square propagates to every horizon
    under its stated hypothesis.
  ],
)

#pagebreak()

#figure(
  placement: none,
  align(center, fletcher.diagram(
    node-stroke: none,
    edge-stroke: 0.78pt + black,
    spacing: (11.7em, 5.3em),
    node((0, 0), [$H_A^f ⊗ H_R^f$], stroke: none),
    node((1, 0), [$H^f$], stroke: none),
    node((0, 1), [$H_A^c ⊗ H_R^c$], stroke: none),
    node((1, 1), [$H^c$], stroke: none),
    edge((0, 0), (1, 0), "-|>", [$J_(Sigma_f)$]),
    edge((0, 0), (0, 1), "-|>", [$pi_A ⊗ pi_R$]),
    edge((1, 0), (1, 1), "-|>", [$pi_H$]),
    edge((0, 1), (1, 1), "-|>", [$J_(Sigma_c)$]),
    node((0.5, 0.5), [⇓ $delta_Sigma$], stroke: none),
  )),
  caption: [
    *Interconnection versus restriction.* $J_Sigma$ joins two Holons at shared
    flow–effort ports. The centre symbol marks a proposed comparison 2-cell:
    it is an identity when the whole Holon descends; otherwise its typed defect and
    composition law remain to be supplied.
    *Status:* the whole-Holon interchange is open.
  ],
)

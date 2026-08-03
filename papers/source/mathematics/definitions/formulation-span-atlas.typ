#let formulation-span-atlas = (
  key: "definition:formulation-span-atlas",
  kind: [Definition],
  title: [Situated formulation-span atlas and exact rechart core],
  status: [Project definition; category-theoretic refinement],
  depends: (
    "definition:situated-formulation-family",
    "definition:comparison-face",
  ),
  claim: [
    Assume $cal(C)$ has pullbacks, fix a parameter base $B$, and choose
    formulation decorations stable under identity spans and pullback
    composition. A *formulation correspondence* from $cal(F)_B$ to
    $cal(G)_B$ is an admissibly decorated span in $cal(C)/B$,
    $
      U_cal(F) arrow.l^(ell) W arrow.r^r U_cal(G),
      quad
      u_cal(F) compose ell
      =
      u_cal(G) compose r.
    $
    Its apex $W$ is the supplied overlap or joint construction; its
    decorations state which laws, boundaries, and receiver comparisons are
    actually transported. It is *exact for* a declared receiver subfamily
    $cal(R)_0$ when
    $
      q_(rho,cal(F)) compose ell
      =
      q_(rho,cal(G)) compose r
      quad "for every" rho in cal(R)_0.
    $
    A 2-cell between parallel correspondences is a map of their apexes which
    commutes with both legs and preserves the declared decorations.

    These objects, correspondences, and 2-cells form the
    *situated formulation-span atlas* $op("FormSpan")_B$. Its maximal
    sub-bicategory containing only equivalence correspondences and invertible
    2-cells is the *exact rechart bigroupoid*. Identifying invertible
    2-isomorphic arrows gives an ordinary rechart groupoid. A map of parameter
    bases $f:B' arrow.r B$ acts by pullback wherever every required decoration
    also pulls back lawfully.
  ],
  proof: none,
  boundary: [
    Pullbacks of bare spans do not by themselves prove that a chosen
    decoration class is closed; that stability is a hypothesis of the atlas.
    A residual between receiver values is testimony about a failed
    comparison; it is not automatically a 2-cell. A one-way limit, quotient,
    projection, branch restriction, or compression may be a lawful
    correspondence without belonging to the rechart core. Base change gives
    an indexed bicategory; it is not called a stack without descent data and
    descent proofs.
  ],
)

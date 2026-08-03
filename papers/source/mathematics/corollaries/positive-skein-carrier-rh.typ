#let positive-skein-carrier-rh = (
  key: "corollary:positive-skein-carrier-rh",
  kind: [Corollary],
  title: [An exhaustive positive completed-zeta skein carrier would imply RH],
  status: [Conditional consequence; carrier not constructed],
  depends: (
    "definition:contextual-tangle-compression",
    "theorem:contextual-skein-compression",
    "theorem:natural-contraction-feasibility",
    "corollary:natural-contraction-rh",
  ),
  claim: [
    Let $cal(Z)$ be a boundary-typed involutive linear tangle category whose
    objects and morphisms present the complete completed-zeta test currents,
    prime admissions, support changes, archimedean returns, and receiver
    recharts.  Suppose:

    + proved local relations give a presentation-independent and exhaustive
      quotient of those currents;
    + an involution-preserving evaluation functor sends gluing to operator
      composition and closure to the complete Weil quadratic response;
    + each generating local relation supplies, independently of the desired
      sign, the natural contractive filler between the established amplitude
      functors $X$ and $Y$; and
    + these local fillers are compatible with every relation, so they
      descend to one natural transformation $Gamma$ on the quotient.

    Then
    $
      Y_j=Gamma_j X_j, quad norm(Gamma_j)<=1
    $
    for every completed test object $j$.  Hence
    $
      Q_W(f)=norm(X_j f)^2-norm(Y_j f)^2>=0
    $
    on the exhaustive Weil test space, and the Riemann Hypothesis follows by
    the Weil criterion.
  ],
  proof: [
    Presentation independence makes the component assigned to a current
    independent of its braid, diagram, or reduction path.  Compatibility
    with gluing and receiver arrows makes the components natural.  The
    assumed local contractivity therefore gives the natural contraction
    required by the natural-contraction RH corollary, which yields Weil
    positivity and RH.
  ],
  boundary: [
    No such completed-zeta skein category or positive evaluation functor has
    been constructed here.  Ordinary Reidemeister, Markov, Alexander,
    Conway, Jones, HOMFLY, or Kauffman relations do not satisfy the stated
    zeta trace identity by default.  A standard skein relation may have
    signed or complex coefficients and therefore supplies no positivity on
    its own.  The missing object remains the arithmetic--archimedean
    natural contraction, now with a possible local presentation grammar.
  ],
)

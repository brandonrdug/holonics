#let prime-power-hinge-cell-recurrence = (
  key: "theorem:prime-power-hinge-cell-recurrence",
  kind: [Theorem],
  title: [Prime-power hinge cells recur; conditioning creates their cross-axis Gram],
  status: [
    Exact successor combinatorics, signed edge factorization, and conditioned
    carrier-interference law; the effective-tension sign remains open
  ],
  depends: (
    "theorem:prime-power-aperture-incidence",
    "theorem:conditioned-support-quotient-shorting",
  ),
  claim: [
    Define the finite-prime part of the zeta screw kernel by
    $
      g_"fin"(t)
      =
      sum_(m>=2)
      c_m (abs(t)-ell_m)_+,
      quad
      c_m=frac(Lambda(m),sqrt(m)),
      quad
      ell_m=log m.
      quad "(HINGE POPULATION)"
    $
    The sum is locally finite.  For $R>1$, put $L_R=log R$,
    $I_R=[-L_R/2,L_R/2]$, and rescale
    $
      x=L_R xi,
      quad y=L_R eta,
      quad
      (xi,eta) in C=[-1/2,1/2]^2.
    $
    A prime-power hinge $m=p^k$ meets this receiver exactly when $m<R$.
    With
    $
      alpha_m(R)=frac(log m,log R),
    $
    its nonzero support in $C$ is the paired triangular region
    $
      T_(m,R)^+
      ={(xi,eta):xi-eta>alpha_m(R)},
    $
    $
      T_(m,R)^-
      ={(xi,eta):eta-xi>alpha_m(R)}.
      quad "(PAIRED CELL)"
    $
    Each triangle has normalized leg $1-alpha_m(R)$ and physical leg
    $log(R/m)$.  On their union the hinge is the affine face
    $
      c_m L_R
      (abs(xi-eta)-alpha_m(R)).
    $

    Let
    $
      cal(P)_R={m>=2:Lambda(m)>0, m<R}.
    $
    The lines
    $xi-eta=plus.minus alpha_m(R)$ for $m in cal(P)_R$ are parallel and
    divide $C$ into exactly
    $
      2 op("card")(cal(P)_R)+1
    $
    connected open strata.  At the integer support successor
    $I_n subset I_(n+1)$, the incidence poset changes if and only if
    $n=p^k$ is a prime power.  In that case one new pair of corner cells is
    born; otherwise every existing cell only deforms.  At the endpoint
    $I_(n+1)$, the number of traversals on the prime axis $p$ is
    $
      N_p(n+1)
      =
      floor(frac(log n,log p)),
    $
    and hence
    $
      op("card")(cal(P)_(n+1))
      =
      sum_(p<=n) floor(frac(log n,log p)).
      quad "(AXIS CENSUS)"
    $
    Along one prime axis, the cell positions and weights are
    $
      ell_(p^k)=k log p,
      quad
      c_(p^k)=(log p)p^(-k/2).
      quad "(LOG HARMONICS)"
    $
    Thus recurrence is equally spaced in logarithmic displacement and
    geometrically weighted in half-density.

    Distributionally,
    $
      g_"fin"''(t)
      =
      sum_(m>=2)c_m
      (delta_(ell_m)+delta_(-ell_m)).
      quad "(CROSSING MEASURE)"
    $
    Let $v in H_0^1(I_R)$ and extend it by zero to the real line.  With
    $
      (U_ell v)(x)=v(x-ell),
    $
    the $m=p^k$ hinge contributes to the localized Weil form exactly
    $
      q_(m,R)(v)
      =
      -2(log p)p^(-k/2)
      op("Re")chevron.l U_(k log p)v,v chevron.r.
      quad "(CROSSING ENERGY)"
    $
    Equivalently, if
    $
      Delta_m=I-m^(-1/2)U_(log m),
    $
    then
    $
      q_(m,R)(v)
      =
      (log p)
      (
        norm(Delta_m v)^2
        -(1+m^(-1))norm(v)^2
      ).
      quad "(SIGNED EDGE)"
    $
    The first term is a squared difference edge and the second is its exact
    diagonal potential.  Neither may be dropped.  Every active raw hinge has
    both signs: for a sufficiently small bump $f$ with disjoint translates,
    $
      v_+=f+U_(log m)f,
      quad
      v_-=f-U_(log m)f
    $
    give respectively negative and positive values of
    $q_(m,R)$.

    The raw additivity does not survive support conditioning as independent
    cellwise energy.  Fix a successor $n arrow.r n+1$, decompose its complete
    form on a common domain as
    $
      q_(n+1)=sum_(alpha in cal(A)_n)q_(alpha,n+1),
      quad
      cal(A)_n={infinity} union cal(P)_(n+1),
    $
    where $infinity$ denotes the complete non-finite-prime face.  Let
    $tilde(J)_n y$ be a conditioned quotient lift.  Assume the component
    cross functionals
    $
      ell_(alpha,y)(x)
      =
      q_(alpha,n+1)(x,tilde(J)_n y)
    $
    descend continuously to the old energy completion $cal(E)_n$, and let
    $c_(alpha,y)$ be their Riesz carriers.  Then the carrier of the complete
    cross is
    $
      c_y=sum_(alpha in cal(A)_n)c_(alpha,y),
    $
    and the exact conditioned short is
    $
      s_n(y)
      =
      sum_(alpha in cal(A)_n)
      q_(alpha,n+1)(tilde(J)_n y)
      -
      norm(
        sum_(alpha in cal(A)_n)c_(alpha,y)
      )^2_(cal(E)_n).
      quad "(COHERENT SHORT)"
    $
    Expanding the last term gives
    $
      s_n(y)
      =
      sum_alpha q_(alpha,n+1)(tilde(J)_n y)
      -
      sum_(alpha,beta)
      chevron.l c_(alpha,y),c_(beta,y) chevron.r_(cal(E)_n).
      quad "(CARRIER GRAM)"
    $
    Hence moment rebase and old-interior elimination create exact
    cross-axis incidences between distinct prime-power and archimedean
    carriers even though their raw threshold lines are parallel.
  ],
  proof: [
    Since $abs(x-y)<=L_R$ on $I_R^2$, the $m$-th hinge is nonzero exactly
    when $ell_m<L_R$.  After the displayed rescaling, its two strict
    inequalities cut congruent right triangles from the two opposed corners
    of $C$, proving ("PAIRED CELL").  Distinct positive threshold values
    produce parallel diagonal segments, so each pair adds two connected
    strata.  At $R=n$ the active integers satisfy $m<n$, whereas at
    $R=n+1$ they satisfy $m<=n$.  This proves the successor statement and
    ("AXIS CENSUS").  The identities in ("LOG HARMONICS") follow from
    $m=p^k$ and $Lambda(p^k)=log p$.

    The second distributional derivative of
    $(abs(t)-ell)_+$ is
    $delta_(ell)+delta_(-ell)$, proving ("CROSSING MEASURE").
    Integrating twice by parts against
    $v'(y)overline(v'(x))$ gives ("CROSSING ENERGY").  Since translation is
    unitary on the zero-extended whole-line carrier,
    $
      norm((I-a U)v)^2
      =
      (1+a^2)norm(v)^2
      -2a op("Re")chevron.l U v,v chevron.r.
    $
    Substitution of $a=m^(-1/2)$ proves ("SIGNED EDGE").  Choose $f$ so
    that $f,U_(log m)f,U_(2log m)f$ have pairwise disjoint supports and the
    first two lie in $I_R$.  Then
    $
      op("Re")chevron.l U_(log m)v_+,v_+ chevron.r
      =norm(f)^2,
    $
    while the same expression for $v_-$ is $-norm(f)^2$.  This proves the
    asserted raw indefiniteness.

    Finally, linearity of the form makes the complete cross functional the
    sum of its component cross functionals.  Uniqueness in the Riesz
    representation theorem therefore makes its carrier the sum of the
    component carriers.  Substitute that sum into the invariant form-short
    identity from the conditioned-support theorem and expand its squared
    norm.  This proves ("COHERENT SHORT") and ("CARRIER GRAM").
  ],
  boundary: [
    The prime-power incidence combinatorics now scales exactly; it is not the
    missing RH theorem.  The paired cells supply a signed graph-Schrödinger
    law—difference energy together with diagonal potential—not independent
    positive prime constituents.  Conditioning then couples every active
    constituent through the common old energy carrier.  Therefore a
    factorization of the form
    $sum_alpha partial_alpha^*W_alpha partial_alpha$ with independent
    $W_alpha>=0$ cannot be inferred from the hinge cells alone.

    The precise remaining inequality is nonnegativity of the effective
    tension after the old body relaxes:
    $
      sum_alpha q_(alpha,n+1)(tilde(J)_n y)
      >=
      norm(sum_alpha c_(alpha,y))^2_(cal(E)_n)
      quad "for every admitted "y,
    $
    together with cross descent when the old form has a radical.  At
    $n=2$ this is exactly $S_(2,3)>=0$.  A source-derived proof must couple
    the archimedean kernel, all active prime-power translations, the moment
    graph, and the old energy inverse.  Further cell enumeration cannot
    decide that sign.
  ],
)

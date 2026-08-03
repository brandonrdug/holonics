#let weil-support-induction-reduction = (
  key: "theorem:weil-support-induction-reduction",
  kind: [Theorem],
  title: [RH reduces to one uniform conditioned support-successor law],
  status: [
    Exact form-level induction reduction; the source-derived successor
    short remains open
  ],
  depends: (
    "theorem:archimedean-remainder-amplitude",
    "theorem:semilocal-sonin-prime-induction",
    "theorem:conditioned-support-quotient-shorting",
    "theorem:prime-power-hinge-cell-recurrence",
    "theorem:oriented-half-density-crossing",
  ),
  claim: [
    For every integer $n>=2$, let $cal(T)_n$ be the Mellin-conditioned
    amplitude fiber
    $
      cal(T)_n
      =
      {
        g in L^2(I_n):
        integral g=0,
        integral e^(sigma u/2)g(u)dif u=0
      },
      quad
      I_n=(-log(n)/2,log(n)/2),
      quad sigma^2=1.
      quad "(AMPLITUDE FIBER)"
    $
    Let $q_n$ be the completed Weil Hermitian form restricted to its
    natural dense domain in $cal(T)_n$, and put
    $
      P(n):
      q_n(g)>=0
      " for every admitted "g in cal(T)_n.
    $
    The archimedean theorem supplies $P(2)$ under these two amplitude
    conditions.  If $h=g ast g^*$, multiplicative convolution gives
    $
      op("supp")(h) subset [n^(-1),n].
    $

    The inclusion $cal(T)_n subset cal(T)_(n+1)$ is not a detached
    old--shell direct sum.  Moment conditioning identifies its quotient by
    a graph section
    $
      J_n:cal(B)_n arrow.r cal(T)_(n+1),
    $
    whose new-support face is accompanied by an old-region compensator.
    The exact section at $n=2$ is
    `theorem:conditioned-support-quotient-shorting`; the same finite-moment
    construction applies for arbitrary $n$.

    Assume $P(n)$, and choose a form-domain lift $tilde(J)_n$ of the Hilbert
    quotient section.  Let
    $
      cal(N)_n={x:q_n(x)=0}
    $
    and let $cal(E)_n$ be the completion of
    $cal(T)_n/cal(N)_n$ in the $q_n$-norm.  For every quotient direction
    $y in cal(B)_n$, define the cross functional
    $
      ell_(n,y)(x)=q_(n+1)(x,tilde(J)_n y).
    $
    Then
    $
      P(n) arrow.r P(n+1)
      quad "(SUCCESSOR)"
    $
    holds exactly when:

    - every $ell_(n,y)$ annihilates $cal(N)_n$ and is continuous in the
      $q_n$-norm, hence has a Riesz carrier $c_(n,y) in cal(E)_n$; and
    - the conditioned shorted shell
      $
        s_n(y)
        =
        q_(n+1)(tilde(J)_n y)-norm(c_(n,y))^2_(cal(E)_n)
        quad "(SHORTED SHELL)"
      $
      is nonnegative for every $y$.

    Equivalently, whenever the carriers assemble into linear maps, there
    are Hilbert spaces and source-derived maps $Z_n,Y_n,R_n$ such that
    $
      q_n(x)=norm(Z_n x)^2,
      quad
      c_(n,y)=Y_n y,
      quad
      s_n(y)=norm(R_n y)^2,
    $
    and therefore
    $
      q_(n+1)(x+tilde(J)_n y)
      =
      norm(Z_n x+Y_n y)^2+norm(R_n y)^2.
      quad "(POSITIVE SUCCESSOR)"
    $

    In an auxiliary bounded operator chart, with conditioned block
    $
      H_(n+1)=mat(H_n,&C_n;C_n^*,&D_n),
    $
    cross continuity is
    $
      op("Ran")(C_n) subset op("Ran")(H_n^(1/2)).
      quad "(RANGE)"
    $
    A bounded factor $C_n=H_n^(1/2)Y_n$ exists exactly when
    $
      C_n C_n^*<=c_n H_n
    $
    for some finite $c_n$, and the remaining condition is
    $
      D_n-Y_n^*Y_n>=0.
      quad "(OPERATOR SHORT)"
    $
    Only when the relevant range is closed may this be rewritten using a
    bounded Moore--Penrose inverse.  Radical annihilation by itself is not
    the successor theorem.

    In the logarithmic interval receiver, a prime translation by
    $ell_p=log p$ has normalized raw overlap
    $
      omega_p(R)
      =
      frac((log R-log p)_+,log R),
    $
    so
    $
      omega_p(p^2)=1/2.
      quad "(HALF CROSSING)"
    $
    This is the midpoint of that prime's support continuation, not its
    first admission.

    The first induction cell is $P(2) arrow.r P(3)$.  The raw $p=2$
    incidence has overlap
    $
      log 3-log 2=log(3/2),
      quad
      omega_2(3)=frac(log(3/2),log 3).
      quad "(FIRST STEP)"
    $
    It is off-diagonal in the unconditioned old--shell split, but moment
    conditioning returns it through the old face and generally contributes
    to both the conditioned cross and conditioned shell blocks.  At $R=4$,
    the dyadic arm reaches half-overlap while the prime $3$ is already
    present; the isolated dyadic character cell is a calibration, not the
    complete $P(4)$ receiver.

    The finite-prime support combinatorics itself is uniform.  In the
    normalized square $I_(n+1)^2$, the thresholds
    $
      abs(x-y)=log(p^k)
    $
    form parallel paired hinge cells.  The successor $n arrow.r n+1$ changes
    their incidence poset exactly when $n$ is a prime power.  Along one prime
    axis their positions are $k log p$ and their half-density weights are
    $(log p)p^(-k/2)$.

    This closure of the cell recurrence does not make the form cellwise
    positive.  If the complete conditioned cross is decomposed into its
    archimedean and active prime-power carriers
    $
      c_(n,y)=sum_alpha c_(alpha,n,y),
    $
    then the short contains their complete Gram:
    $
      s_n(y)
      =
      sum_alpha q_(alpha,n+1)(tilde(J)_n y)
      -
      sum_(alpha,beta)
      chevron.l
        c_(alpha,n,y),c_(beta,n,y)
      chevron.r_(cal(E)_n).
      quad "(COHERENT GRAM)"
    $
    Distinct raw hinge lines are parallel, but eliminating the common old
    interior creates their cross-axis terms.

    One uniform source-derived proof of ("RANGE") and
    ("OPERATOR SHORT"), or their form-level equivalents, for every $n>=2$
    proves RH.  Ordinary induction gives every $P(n)$, every compactly
    supported admissible amplitude lies in some $cal(T)_n$, and Weil's
    criterion then gives RH.
  ],
  proof: [
    The support statement follows because the quotient of two members of
    $[n^(-1/2),n^(1/2)]$ lies in $[n^(-1),n]$.  The base case is the
    published archimedean positivity theorem with its independently
    constructed Sonin/prolate remainder amplitude.

    The conditioned quotient theorem constructs $J_n$ by solving the two
    moment equations in the old region.  If the cross functional descends
    to the old energy completion, Riesz representation and completion of
    the square give
    $
      q_(n+1)(x+tilde(J)_n y)
      =
      norm([x]+c_(n,y))^2+s_n(y).
    $
    This proves necessity and sufficiency of the two form-level conditions,
    as well as ("POSITIVE SUCCESSOR").  Douglas's factorization theorem
    gives the bounded operator version.

    The overlap formula is the length of the intersection of an interval of
    length $log R$ with its translate by $log p$, divided by $log R$.
    Substitution of $R=p^2$ and $(p,R)=(2,3)$ gives the two displayed
    values.  The raw-to-conditioned block formula proves that raw
    off-diagonality does not survive the moment rechart.

    Finally, ordinary induction establishes the form on every integer
    aperture.  Compact support places each individual Weil test amplitude
    at one finite aperture, completing the criterion.
  ],
  boundary: [
    This theorem fixes the induction architecture but does not assert the
    missing positivity.  The first unresolved cell is now explicit in the
    continuous screw-kernel chart.  Positive definiteness and compact
    resolvent of the published $P(2)$ base already carry the conditioned
    $I_2 arrow.r I_3$ cross through the old energy space.  What remains is
    positivity of that cell's single shorted-shell operator.  Published
    Sonin transport supplies coherent space transport, and the explicit
    formula supplies the raw prime incidence; neither signs this conditional
    energy.

    A uniform proof must then show that the same construction survives every
    support successor.  Prime stages admit a new Euler difference/return
    pair; higher prime powers expose another traversal of an existing place;
    other stages move only the support boundary.  None of those distinctions
    changes the one form-level obligation above.  The prime-power cell
    recurrence and its exact census are now closed.  What remains is the
    effective-tension sign represented in coordinates by ("COHERENT GRAM"),
    not a further combinatorial enumeration or a sum of independently
    positive prime cells.
  ],
)

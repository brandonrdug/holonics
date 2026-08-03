#let prime-active-positivity-continuation = (
  key: "corollary:prime-active-positivity-continuation",
  kind: [Corollary],
  title: [Strict base positivity continues through a genuine first-prime interval],
  status: [
    Exact consequence of the published strict base gap and continuity of the
    localized Weil ground value; nonquantitative endpoint
  ],
  depends: (
    "theorem:conditioned-effective-tension",
    "theorem:prime-power-hinge-cell-recurrence",
  ),
  claim: [
    Let $q_a$ be the localized Weil form on $(-a,a)$ and let
    $
      lambda(a)
      =
      inf_(v!=0) frac(q_a(v),norm(v)^2)
    $
    be its attained lowest spectral value.  Put
    $
      a_2=frac(log 2,2),
      quad
      a_3=frac(log 3,2).
    $
    The published base theorem gives
    $
      lambda(a_2)>0,
    $
    and the published screw-function theorem gives continuity of
    $a mapsto lambda(a)$.  Therefore there is a
    $
      delta in (0,a_3-a_2)
    $
    such that
    $
      lambda(a)>0
      quad "for every"quad
      a in [a_2,a_2+delta].
      quad "(PRIME-ACTIVE CONTINUATION)"
    $
    Equivalently, with
    $
      R_*=exp(2(a_2+delta))=2e^(2delta)>2,
    $
    Weil positivity is proved on every aperture
    $
      2<=R<=R_*.
    $
    Every interior aperture in this interval contains the newly active
    $p=2$ crossing and no $p=3$ crossing.  Hence the result crosses the
    prime-free boundary; it is not merely another statement inside the
    archimedean cell.

    If RH is false, continuity and small-aperture positivity imply the
    existence of a first degeneracy parameter
    $
      a_* = inf{a>=a_2:lambda(a)<=0}
    $
    with
    $
      lambda(a_*)=0.
    $
    Relative to any earlier strictly positive aperture used as the old body,
    the conditioned effective tension at $a_*$ has a nonzero null mode.
    Thus the first possible failure of RH appears geometrically as a
    zero-tension standing mode of the source-derived support continuation,
    not as a change of receiver coordinates.
  ],
  proof: [
    Since $lambda(a_2)>0$ and $lambda$ is continuous, choose
    $delta>0$ small enough that
    $
      abs(lambda(a)-lambda(a_2))<lambda(a_2)/2
    $
    on $[a_2,a_2+delta]$, and also
    $delta<a_3-a_2$.  This proves
    ("PRIME-ACTIVE CONTINUATION").  The prime-power threshold law says that
    $p=2$ becomes active as soon as $2a>log 2$, whereas $p=3$ does not become
    active before $2a=log 3$.

    If RH fails, Weil's criterion supplies some aperture with a negative
    lowest value.  Continuity, together with positivity at the base, gives
    the first zero $a_*$.  The inertia split in the effective-tension theorem
    carries that first new null direction entirely into the shorted
    continuation after the earlier positive interior has relaxed.
  ],
  boundary: [
    The corollary proves a real prime-active interval but does not give a
    numerical value of $delta$ and therefore does not reach $a_3$.  Closing
    the full first cell now has a precise quantitative form: control the
    source-derived effective tension, or an equivalent modulus for
    $lambda(a)$, throughout
    $
      [log(2)/2,log(3)/2].
    $
    Continuity alone cannot provide that bound.
  ],
)

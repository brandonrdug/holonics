#let first-prime-fixed-domain-hinge = (
  key: "lemma:first-prime-fixed-domain-hinge",
  kind: [Lemma],
  title: [Before the third prime enters, the finite-place operator is one exact boundary-strip swap],
  status: [
    Exact specialization of the published fixed-domain screw form; exact
    partial-isometry spectrum; continuum domination remains open
  ],
  depends: (
    "theorem:prime-power-hinge-cell-recurrence",
    "theorem:conditioned-effective-tension",
  ),
  claim: [
    Put
    $
      a_2=frac(log 2,2),
      quad
      a_3=frac(log 3,2),
      quad
      h(a)=frac(log 2,a),
      quad
      alpha_2=frac(log 2,sqrt(2)).
    $
    For $a in (a_2,a_3)$ one has $1<h(a)<2$.  In
    $cal(H)=L^2(-1,1)$ define the disjoint boundary-strip fibers
    $
      cal(H)_L(a)=L^2(-1,1-h(a)),
      quad
      cal(H)_R(a)=L^2(-1+h(a),1),
    $
    and let $V_a:cal(H)_L(a) arrow.r cal(H)_R(a)$ be translation by
    $h(a)$, extended by zero on the orthogonal complement.  Then
    $
      T_a=V_a+V_a^*,
      quad
      T_a^2=P_L(a)+P_R(a),
      quad
      op("spec")(T_a)={-1,0,1}.
      quad "(HINGE SWAP)"
    $
    Its positive and negative faces are the paired boundary configurations
    $
      f⊕V_a f
      quad "and" quad
      f⊕(-V_a f),
    $
    while the central fiber is its zero face.

    Let $r$ and the closed form $cal(L)$ be the archimedean objects in the
    published fixed-domain expansion of the zeta screw function, and define
    $
      chevron.l cal(R)_a w,w chevron.r
      =
      integral_(-1)^1 integral_(-1)^1
      r''(a(x-y))w(y)overline(w(x))dif x dif y.
    $
    If
    $
      A_zeta=frac(1,2)(log(2 pi)+gamma-1),
    $
    the localized Weil form transported to $(-1,1)$ is exactly
    $
      overline(q)_a(w)
      =
      cal(L)(w)
      -(log a+2A_zeta+1)norm(w)^2
      -alpha_2 chevron.l T_a w,w chevron.r
      -a chevron.l cal(R)_a w,w chevron.r.
      quad "(ONE-PRIME FORM)"
    $
    At $a=a_2$ the two strips have zero measure and the hinge is born; at
    $a=a_3$ the prospective $p=3$ strip still has zero measure.  Hence no
    other finite-place operator occurs in the complete first open cell.

    Define the remaining archimedean operator form
    $
      cal(H)_a
      =
      cal(L)-(log a+2A_zeta+1)I-a cal(R)_a.
    $
    Positivity through the first prime-active interval is therefore exactly
    the source inequality
    $
      cal(H)_a-alpha_2 T_a>=0
      quad
      "for "
      a in [a_2,a_3].
      quad "(FIXED-DOMAIN WALL)"
    $
    In particular,
    $
      abs(lr(chevron.l T_a w,w chevron.r))<=norm(w)^2,
    $
    but this sharp hinge bound alone does not prove
    ("FIXED-DOMAIN WALL").
  ],
  proof: [
    For $a in (a_2,a_3)$, the prime-power threshold
    $log n<=2a$ admits only $n=2$.  Specializing the published scaled
    screw-form identity to that one term makes its two overlap integrals
    exactly
    $
      chevron.l (V_a+V_a^*)w,w chevron.r.
    $
    Because $h(a)>1$, the source and target strips are disjoint and $V_a$
    is a partial isometry with
    $
      V_a^* V_a=P_L(a),
      quad
      V_a V_a^*=P_R(a).
    $
    This proves ("HINGE SWAP") and its three spectral faces.  The
    coefficient of the $n=2$ von Mangoldt term is
    $Lambda(2)/sqrt(2)=alpha_2$.  The remaining terms of the published
    fixed-domain formula give $cal(H)_a$, proving ("ONE-PRIME FORM") and
    ("FIXED-DOMAIN WALL").  The quadratic bound follows from
    $norm(T_a)=1$.
  ],
  boundary: [
    This lemma removes all finite-place combinatorial ambiguity from the
    first cell.  It does not show that the archimedean form $cal(H)_a$
    dominates the positive hinge face.  The smooth-kernel dependence and the
    barely logarithmic form domain yield continuity of the lowest value, but
    the published argument supplies no quantitative modulus reaching
    $a_3$.  A valid next theorem must estimate this declared operator family,
    not replace it with a finite prime census or an independently chosen knot
    energy.
  ],
)

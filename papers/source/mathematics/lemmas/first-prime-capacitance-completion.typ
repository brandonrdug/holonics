#let first-prime-capacitance-completion = (
  key: "lemma:first-prime-capacitance-completion",
  kind: [Lemma],
  title: [The first-prime cross is an open capacitor with an exact endpoint-storage debit],
  status: [
    Exact fixed-domain identity and compact relative-passivity reduction;
    the resulting unit-gain bound remains the first-cell analytic wall
  ],
  depends: (
    "lemma:first-prime-fixed-domain-hinge",
    "theorem:passive-incidence-kron-composition",
  ),
  claim: [
    Retain the first-cell notation
    $
      a_2=frac(log 2,2),
      quad
      a_3=frac(log 3,2),
      quad
      alpha_2=frac(log 2,sqrt(2)),
    $
    together with the left and right strip projections $P_L(a),P_R(a)$
    and their translation partial isometry $V_a$.  Put
    $
      P_a=P_L(a)+P_R(a),
      quad
      T_a=V_a+V_a^*,
    $
    and define the oriented prime difference
    $
      delta_a w=P_R(a) w-V_a P_L(a) w.
      quad "(PRIME INCIDENCE)"
    $
    Then
    $
      delta_a^* delta_a=P_a-T_a.
      quad "(CAPACITOR COMPLETION)"
    $
    Hence the exact first-cell Weil form admits the identity
    $
      overline(q)_a
      =
      cal(H)_a-alpha_2T_a
      =
      alpha_2 delta_a^*delta_a
      +cal(K)_a,
      quad
      cal(K)_a=cal(H)_a-alpha_2P_a.
      quad "(OPEN CAPACITOR)"
    $
    The prime contribution supplies the mutual cross term of a capacitor.
    Completing it to the nonnegative branch energy
    $alpha_2 norm(delta_a w)^2$ exposes the equal endpoint-storage debit
    $alpha_2 norm(P_a w)^2$.  The original prime term is therefore not a
    passive branch by itself.

    The archimedean form occurring here already has the exact
    Beurling--Deny incidence/storage representation
    $
      cal(L)(w)
      =
      frac(1,4)
      integral_(-1)^1 integral_(-1)^1
      frac(abs(w(x)-w(y))^2,abs(x-y))
      dif x dif y
      +frac(1,2)integral_(-1)^1
      (-log(1-x^2))abs(w(x))^2 dif x.
      quad "(ARCHIMEDEAN NETWORK)"
    $
    If
    $
      c_a=log a+2A_zeta+1
    $
    and $cal(R)_a$ is the smooth-kernel operator in the fixed-domain screw
    form, define
    $
      cal(E)_a(w)
      =
      cal(L)(w)+alpha_2 norm(delta_a w)^2,
    $
    $
      cal(D)_a(w)
      =
      c_a norm(w)^2
      +a chevron.l cal(R)_a w,w chevron.r
      +alpha_2 norm(P_a w)^2.
      quad "(STORAGE AND LOAD)"
    $
    Then, exactly,
    $
      overline(q)_a(w)=cal(E)_a(w)-cal(D)_a(w).
      quad "(FIRST-CELL BALANCE)"
    $
    The first-cell sign is consequently equivalent to the one
    source-derived relative passivity inequality
    $
      cal(D)_a(w)<=cal(E)_a(w)
      quad
      "for every "w
      quad "and every "a in [a_2,a_3].
      quad "(UNIT-GAIN WALL)"
    $

    The closed positive form $cal(E)_a$ has a strict lower gap and compact
    resolvent.  The load form $cal(D)_a$ is a bounded Hermitian
    perturbation.  Therefore
    $
      Gamma_a
      =
      cal(E)_a^(-1/2)cal(D)_a cal(E)_a^(-1/2)
      quad "(RELATIVE LOAD)"
    $
    is compact and self-adjoint, and
    $
      overline(q)_a>=0
      quad arrow.l.r quad
      lambda_"max"(Gamma_a)<=1.
      quad "(RELATIVE PASSIVITY)"
    $
    If equality first occurs, its mode $w$ satisfies the complete weak
    balance
    $
      cal(D)_a(w,z)=cal(E)_a(w,z)
      quad "for every "z.
      quad "(UNIT-GAIN STANDING)"
    $
    Thus the possible zero is a unit-gain standing mode of the whole
    archimedean--prime circuit, not a scalar failure of one isolated prime
    edge.

    On the paired strips, the aligned face $f+V_a f$ lies in
    $ker(delta_a)$, whereas the opposed face $f-V_a f$ has
    $
      norm(delta_a(f-V_a f))^2=2 norm(f-V_a f)^2.
    $
    The prime branch therefore spends no difference energy on a transported
    recurrence and stiffens the opposed configuration by $2alpha_2$.
    Any negative part of $cal(K)_a$ can be repaired only through such an
    opposed component.  In particular,
    $
      cal(K)_a|_(ker delta_a)>=0
      quad "(COHERENT NECESSITY)"
    $
    is necessary for first-cell positivity, while the stronger global
    assertion $cal(K)_a>=0$ is sufficient but not necessary.
  ],
  proof: [
    Since $V_a^* V_a=P_L(a)$ and $V_a V_a^*=P_R(a)$, direct multiplication of
    ("PRIME INCIDENCE") gives
    $
      delta_a^* delta_a
      =
      P_R(a)+P_L(a)-V_a-V_a^*
      =
      P_a-T_a.
    $
    Rearranging proves ("OPEN CAPACITOR").  Substituting the published
    formula for $cal(H)_a$ and the exact difference-energy representation
    of $cal(L)$ proves ("FIRST-CELL BALANCE").

    The two terms in ("ARCHIMEDEAN NETWORK") are nonnegative.  If both
    vanish, the jump term makes $w$ constant almost everywhere, while the
    boundary-storage term then forces that constant to be zero.  Closedness
    and compact embedding therefore give a strict lower gap for
    $cal(L)$, hence also for $cal(E)_a$.  The scalar, projection, and
    continuous-kernel terms in $cal(D)_a$ are bounded.  The compact
    resolvent of $cal(E)_a$ makes ("RELATIVE LOAD") compact and
    self-adjoint.  Conjugating ("FIRST-CELL BALANCE") by
    $cal(E)_a^(-1/2)$ proves ("RELATIVE PASSIVITY") and its equality
    equation.

    The aligned and opposed formulas follow directly from the partial
    isometry relations.  Restricting ("OPEN CAPACITOR") to
    $ker(delta_a)$ proves ("COHERENT NECESSITY").
  ],
  boundary: [
    This identity locates the missing diagonal exactly.  The source supplies
    positive nonlocal archimedean incidence and boundary storage, but after
    its scalar and smooth-kernel loads are included it has not yet been
    proved to pay the endpoint debit on the complete first-cell domain.
    Treating $cal(K)_a$ as positive would add a stronger assumption and is
    not the proof.  The honest remaining obligation is
    ("UNIT-GAIN WALL"), equivalently the largest relative-load eigenvalue
    staying at most one through the complete first prime interval.
  ],
)

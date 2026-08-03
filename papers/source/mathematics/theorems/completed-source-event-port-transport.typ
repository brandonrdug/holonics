#let completed-source-event-port-transport = (
  key: "theorem:completed-source-event-port-transport",
  kind: [Theorem],
  title: [The completed source enters a shifted receiver through one bipolar boundary port],
  status: [
    Exact logarithmic receiver, inherited shift, integer-event triangles, and
    bipolar port balance; causal passivity remains RH-equivalent
  ],
  depends: (
    "definition:situated-event-correspondence",
    "theorem:completed-scattering-hankel-successor",
  ),
  claim: [
    Fix $omega>0$ and retain the source cut
    $hat(bold(H))_(omega,a)$ on $L^2(0,1)$ with kernel
    $a h_omega(a^2 x y)$.  Put
    $
      tau=2log a
    $
    and let
    $
      (cal(V)f)(s)=e^(-s/2)f(e^(-s)),
      quad
      cal(V):L^2(0,1) arrow.r L^2(0,infinity).
    $
    Then $cal(V)$ is unitary, and
    $
      cal(H)_(omega,tau)
      =
      cal(V)hat(bold(H))_(omega,a)cal(V)^(-1)
    $
    is the causal triangular Hankel operator
    $
      (cal(H)_(omega,tau)F)(s)
      =
      integral_0^infinity
      psi_omega(tau-s-t)F(t)dif t,
      quad "(LOGARITHMIC RECEIVER)"
    $
    where
    $
      psi_omega(u)
      =
      e^(u/2)h_omega(e^u)
      =
      j_omega'(u)
      =
      sum_(log n<=u)
      w_omega(n)phi_omega(u-log n)
      quad "(ACTION CURRENT)"
    $
    on the positive logarithmic ray and is zero for $u<0$.  Consequently
    $
      cal(H)_(omega,tau)
      =
      sum_(log n<tau)
      w_omega(n)cal(K)_(omega,tau-log n),
      quad "(INTEGER EVENT POPULATION)"
    $
    in its locally finite form sense, where
    $cal(K)_(omega,rho)$ has kernel
    $phi_omega(rho-s-t)$ and support
    $
      s+t<rho.
      quad "(EVENT TRIANGLE)"
    $
    An integer is therefore not an isolated value attached to an old
    operator.  At $tau=log n$ its response triangle is born at the receiver
    boundary $(s,t)=(0,0)$ and subsequently grows through the same source
    current.  For $tau<=0$,
    $
      cal(H)_(omega,tau)=0,
      quad
      cal(M)_(omega,tau)^epsilon
      :=
      I+epsilon cal(H)_(omega,tau)
      =
      I,
      quad epsilon in {plus.minus 1}.
      quad "(INHERITED REST)"
    $
    Thus the zero source face is not an empty mathematical object: the
    receiver space and both identity standing forms are already present.

    The old body is carried exactly through every later event.  For
    $tau_1<tau_2$, put
    $
      ell=frac(tau_2-tau_1,2)
    $
    and let $cal(S)_ell$ be the right-shift isometry
    $
      (cal(S)_ell F)(s)
      =
      cases(
        0,&0<=s<ell,
        F(s-ell),&s>=ell.
      )
    $
    Directly from ("LOGARITHMIC RECEIVER"),
    $
      cal(S)_ell^*
      cal(H)_(omega,tau_2)
      cal(S)_ell
      =
      cal(H)_(omega,tau_1),
    $
    $
      cal(S)_ell^*
      cal(M)_(omega,tau_2)^epsilon
      cal(S)_ell
      =
      cal(M)_(omega,tau_1)^epsilon.
      quad "(INHERITED SHIFT)"
    $
    Let
    $
      cal(B)_ell=L^2(0,ell)
    $
    be the exposed boundary strip and use the unitary
    $
      cal(W)_ell(F⊕b)=cal(S)_ell F+b
    $
    from
    $L^2(0,infinity)⊕cal(B)_ell$ onto $L^2(0,infinity)$.
    There are source-determined cross and boundary operators
    $C_e,D_e$ such that
    $
      cal(W)_ell^*
      cal(H)_(omega,tau_2)
      cal(W)_ell
      =
      mat(
        cal(H)_(omega,tau_1),&C_e;
        C_e^*,&D_e
      ).
      quad "(FINITE EVENT)"
    $
    Whenever the inherited polarity is invertible, the exact event
    factorization is
    $
      cal(W)_ell^*
      cal(M)_(omega,tau_2)^epsilon
      cal(W)_ell
      =
      L_(epsilon,e)^*
      mat(
        cal(M)_(omega,tau_1)^epsilon,&0;
        0,&S_(epsilon,e)
      )
      L_(epsilon,e),
      quad "(EVENT CONGRUENCE)"
    $
    with
    $
      L_(epsilon,e)
      =
      mat(
        I,&epsilon
        (cal(M)_(omega,tau_1)^epsilon)^(-1)C_e;
        0,&I
      ),
    $
    $
      S_(epsilon,e)
      =
      I_(cal(B)_ell)+epsilon D_e
      -C_e^*
      (cal(M)_(omega,tau_1)^epsilon)^(-1)
      C_e.
      quad "(BOUNDARY RETURN)"
    $
    This is the bipolar successor as one situated event: the old standing
    body is shifted intact, while the new strip, its old--new cross, and its
    returned short are co-present.

    The corresponding infinitesimal law is a source-derived boundary-port
    identity and uses no inverse or assumed factorization.  At a regular
    $tau$, for $F$ in a common smooth form core,
    $
      partial_tau
      chevron.l cal(H)_(omega,tau)F,F chevron.r
      =
      op("Re")
      chevron.l F',cal(H)_(omega,tau)F chevron.r
      +
      op("Re")[
        overline(F(0))
        (cal(H)_(omega,tau)F)(0)
      ].
      quad "(SOURCE GREEN IDENTITY)"
    $
    Put
    $
      u=F(0),
      quad
      y_epsilon=
      (cal(M)_(omega,tau)^epsilon F)(0),
      quad
      v_epsilon=y_epsilon-u
      =
      epsilon(cal(H)_(omega,tau)F)(0).
    $
    After subtracting the inherited right-shift transport
    $partial_tau F=-F'/2$, the standing energy
    $
      E_epsilon(tau,F)
      =
      chevron.l
        cal(M)_(omega,tau)^epsilon F,F
      chevron.r
    $
    obeys
    $
      nabla_tau E_epsilon
      =
      frac(1,2)
      (
        abs(y_epsilon)^2-abs(v_epsilon)^2
      ).
      quad "(BIPOLAR PORT BALANCE)"
    $
    The two orientations share the same boundary occurrence.  If
    $z=(cal(H)_(omega,tau)F)(0)$, then
    $
      y_+=u+z,
      quad y_-=u-z,
      quad
      nabla_tau E_+
      +
      nabla_tau E_-
      =
      abs(u)^2.
      quad "(ONE CURRENT TWO FACES)"
    $
    In particular, an inherited shifted state has $u=0$ and equal incoming
    and outgoing port sizes, so its standing energy is unchanged.  If a
    nonzero mode satisfies
    $cal(M)_(omega,tau)^epsilon F=0$, then its receiver-visible crossing is
    $
      nabla_tau E_epsilon
      =
      -frac(1,2)abs(F(0))^2.
      quad "(NULL PORT)"
    $
    A first singularity is therefore either a transverse outward event
    visible at the boundary or a port-dark null mode with $F(0)=0$.

    The published Fredholm chart supplies the same event as an explicit
    bipolar differential connection.  On an aperture interval where both
    $I+epsilon bold(H)_(omega,a)$ are invertible, let
    $phi.alt_(omega,a)^epsilon$ solve
    $
      phi.alt_(omega,a)^epsilon(x)
      +
      epsilon
      integral_0^a
      h_omega(x y)phi.alt_(omega,a)^epsilon(y)dif y
      =
      h_omega(a x),
      quad epsilon in {plus.minus 1}.
      quad "(BOUNDARY RESPONSE)"
    $
    Put
    $
      delta_x=x partial_x+frac(1,2),
      quad
      mu_omega(a)
      =
      a phi.alt_(omega,a)^+(a)
      +
      a phi.alt_(omega,a)^-(a).
      quad "(SHARED BOUNDARY FIELD)"
    $
    In the continuous-kernel range $omega>1$, Suzuki's source calculation
    gives
    $
      (
        a partial_a+frac(1,2)+epsilon mu_omega(a)
      )
      phi.alt_(omega,a)^epsilon(x)
      =
      delta_x phi.alt_(omega,a)^(-epsilon)(x).
      quad "(BIPOLAR RESOLVENT CONNECTION)"
    $
    Thus the two polarities are not independently propagated estimates.
    Dilation of either response turns into the oppositely oriented response,
    while their boundary values form one common connection coefficient.
    With
    $
      m_omega(a)
      =
      exp
      (
        integral_1^a mu_omega(b)frac(dif b,b)
      ),
      quad m_omega(1)=1,
      quad "(ACCUMULATED CONNECTION)"
    $
    the gauged return satisfies the canonical system with Hamiltonian
    $
      op("diag")(
        m_omega(a)^(-2),
        m_omega(a)^2
      ).
      quad "(CANONICAL INTERIOR)"
    $
    For $omega>1$ this agrees with
    $
      m_omega(a)
      =
      frac(
        det(I+bold(H)_(omega,a)),
        det(I-bold(H)_(omega,a))
      ).
      quad "(DETERMINANT RETURN)"
    $
    The identity is source-derived on its invertibility interval; it does
    not assume either standing form positive.
  ],
  proof: [
    Substitute $x=e^(-s)$ and $y=e^(-t)$ in the fixed-receiver kernel.  The
    two half-density factors give
    $
      a e^(-(s+t)/2)h_omega(a^2e^(-(s+t)))
      =
      e^((tau-s-t)/2)
      h_omega(e^(tau-s-t))
      =
      psi_omega(tau-s-t).
    $
    The log-time current formula in
    `theorem:completed-scattering-hankel-successor` proves
    ("ACTION CURRENT") and ("INTEGER EVENT POPULATION").  Its one-sided
    support gives ("EVENT TRIANGLE") and ("INHERITED REST").

    For $ell=(tau_2-tau_1)/2$,
    $
      psi_omega(tau_2-(s+ell)-(t+ell))
      =
      psi_omega(tau_1-s-t).
    $
    This proves ("INHERITED SHIFT").  Splitting the target into the shifted
    range and its orthogonal boundary strip gives ("FINITE EVENT").
    Ordinary block elimination gives ("EVENT CONGRUENCE") and
    ("BOUNDARY RETURN"); no sign is used in that algebra.

    Away from the locally finite admission seams,
    $
      partial_tau
      psi_omega(tau-s-t)
      =
      -frac(1,2)
      (partial_s+partial_t)
      psi_omega(tau-s-t).
    $
    Integrate the two derivatives by parts on the positive quadrant.  The
    two exposed faces at $s=0$ and $t=0$ give the boundary term in
    ("SOURCE GREEN IDENTITY"), while the interior derivatives give
    $op("Re")chevron.l F',cal(H)F chevron.r$.  The weak source seams use the
    corresponding one-sided form identity.

    Since
    $
      op("Re")chevron.l F',F chevron.r
      =
      -frac(1,2)abs(F(0))^2,
    $
    replacing $epsilon cal(H)$ by $cal(M)^epsilon-I$ gives
    $
      partial_tau E_epsilon
      =
      op("Re")
      chevron.l F',cal(M)^epsilon F chevron.r
      +
      op("Re")(overline(u)y_epsilon)
      -frac(1,2)abs(u)^2.
    $
    The state derivative $partial_tau F=-F'/2$ cancels the first term.
    Finally,
    $
      op("Re")(overline(u)y_epsilon)
      -frac(1,2)abs(u)^2
      =
      frac(1,2)
      (
        abs(y_epsilon)^2-abs(y_epsilon-u)^2
      ),
    $
    proving ("BIPOLAR PORT BALANCE").  The parallelogram identity for
    $u+z$ and $u-z$ proves ("ONE CURRENT TWO FACES"), and setting
    $y_epsilon=0$ proves ("NULL PORT").

    Finally, differentiate ("BOUNDARY RESPONSE") with respect to $a$ and
    apply $delta_x$.  The product-kernel identity
    $
      x partial_x h_omega(x y)
      =
      y partial_y h_omega(x y)
    $
    moves the Euler derivative to the response variable.  Integration by
    parts exposes the two endpoint values in
    ("SHARED BOUNDARY FIELD").  Subtracting the equations with opposed
    signs and using uniqueness of the Fredholm solutions gives
    ("BIPOLAR RESOLVENT CONNECTION").  Gauging its common scalar connection
    by ("ACCUMULATED CONNECTION") gives ("CANONICAL INTERIOR").
    Differentiation of the two Fredholm determinants gives their boundary
    resolvent values, hence ("DETERMINANT RETURN").
  ],
  boundary: [
    This theorem removes the initialization circle.  The receiver does not
    arise from the first integer cell: it begins as the nonempty identity
    standing pair, carries every old direction by the exact shift
    ("INHERITED SHIFT"), and admits new source material only through the
    boundary strip.  The integer population, continuous Gamma response,
    old--new cross, and receiver motion are different faces of that one
    event.

    The theorem does not prove the remaining causal inequality.  RH is now
    equivalently the assertion that both port relations are passive on every
    finite logarithmic interval:
    $
      integral abs(v_epsilon)^2dif tau
      <=
      integral abs(y_epsilon)^2dif tau
      +2E_epsilon("initial")
      quad
      "for "epsilon=plus.minus 1,
      quad "(BIPOLAR CAUSAL PASSIVITY)"
    $
    or, event by event, that every explicit
    $S_(epsilon,e)$ in ("BOUNDARY RETURN") is nonnegative.  Boundary
    unitarity gives an all-time equality but does not imply this causal
    inequality.  A proof must derive ("BIPOLAR CAUSAL PASSIVITY") from the
    convolution current
    $psi_omega=nu_omega ast phi_omega$ without first inverting or taking a
    square root of the desired positive form.  The remaining analytic
    alternatives are correspondingly precise: rule out every boundary-visible
    unit mode and every port-dark null mode, or construct the two causal
    port contractions directly.

    The canonical system does not close this gap by notation.  Its published
    unconditional construction above is in the regular range $omega>1$,
    where innerness is already known.  Extending the boundary response,
    determinant return, and coupled connection through every finite
    aperture for $0<omega<1/2$ without assuming innerness is exactly the
    target-range continuation problem.  If a determinant vanishes, the
    corresponding response and $mu_omega$ become singular; declaring the
    positive Hamiltonian past that point would simply assume the desired
    result.
  ],
)

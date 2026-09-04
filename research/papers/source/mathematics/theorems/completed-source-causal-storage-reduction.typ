#let completed-source-causal-storage-reduction = (
  key: "theorem:completed-source-causal-storage-reduction",
  kind: [Theorem],
  title: [The completed zeta source has an exact shift state and a local storage criterion],
  status: [
    Exact causal state realization and sufficient KYP storage reduction;
    construction of the required source-native storage remains open
  ],
  depends: (
    "definition:causal-time-parity",
    "theorem:causal-parity-kirchhoff-return",
    "theorem:completed-source-volterra-frame-defect",
    "corollary:causal-impedance-rh",
  ),
  claim: [
    Fix $0<omega<1/2$ and let $psi_omega$ be the completed causal source
    current from `theorem:completed-source-volterra-frame-defect`.  On
    $cal(X)=L^2(0,infinity)$ let
    $
      (T_tau x)(r)=x(r+tau),
      quad
      A x=partial_r x,
      quad
      B_omega u=psi_omega u,
      quad
      C x=x(0)
    $
    on the natural smooth reachable core.  For a smooth compactly supported
    input $u$, define
    $
      x_tau(r)
      =
      integral_0^tau
      psi_omega(tau+r-s)u(s)dif s.
      quad "(SOURCE SHIFT STATE)"
    $
    Then
    $
      dot(x)_tau
      =
      A x_tau+B_omega u(tau),
      quad
      y(tau)=C x_tau
      =
      (psi_omega ast u)(tau),
      quad x_0=0.
      quad "(SOURCE STATE LAW)"
    $
    Its transfer on $op("Re")p>0$ is
    $
      C(p I-A)^(-1) B_omega
      =
      hat(psi)_omega(p)
      =
      frac(Xi(omega-p),Xi(omega+p)).
      quad "(COMPLETED TRANSFER)"
    $

    Suppose there is a nonnegative self-adjoint storage operator $P_omega$
    whose form domain contains the reachable core and on which the block
    form
    $
      mat(
        A^*P_omega+P_omega A+C^*C,
        &P_omega B_omega;
        B_omega^*P_omega,
        &-I
      )
      <=0
      quad "(SOURCE STORAGE INEQUALITY)"
    $
    is well-defined.  Then every finite causal cut is contractive:
    $
      integral_0^tau abs(y(r))^2dif r
      <=
      integral_0^tau abs(u(r))^2dif r
      quad "for every "tau>0.
      quad "(FINITE SOURCE PASSIVITY)"
    $
    Equivalently, the source Hankel cuts obey both polarities
    $I plus.minus cal(H)_(omega,a)>=0$.

    If such a source-native $P_omega$ is constructed for every
    $0<omega<1/2$, the Riemann Hypothesis follows.
  ],
  proof: [
    The variation-of-constants formula for the left-shift semigroup is
    $
      x_tau
      =
      integral_0^tau
      T_(tau-s)B_omega u(s)dif s,
    $
    which is ("SOURCE SHIFT STATE").  Differentiating on the smooth core
    proves ("SOURCE STATE LAW").  Since
    $C T_t B_omega=psi_omega(t)$, Laplace transformation gives
    ("COMPLETED TRANSFER").

    Put
    $cal(H)_omega(x)=chevron.l P_omega x,x chevron.r$.
    Along a reachable trajectory,
    $
      frac(dif,dif tau)cal(H)_omega(x_tau)
      +
      abs(y(tau))^2
      -
      abs(u(tau))^2
    $
    is the quadratic form of ("SOURCE STORAGE INEQUALITY") on
    $(x_tau,u(tau))$, and is therefore nonpositive.  Integration from
    $0$ to $tau$, together with $x_0=0$ and $P_omega>=0$, proves
    ("FINITE SOURCE PASSIVITY").  The shared causal-defect factorization
    turns contraction of the Volterra source into positivity of both
    Hankel polarities.  Their established equivalence for every
    $0<omega<1/2$ then gives RH.
  ],
  boundary: [
    The theorem identifies a local source equation, not a way to define
    $P_omega$ from the already-assumed norm of the transfer.  A proof must
    construct its kernel or feature map directly from the completed
    theta--Euler--Gamma source and verify the form domains, integer-event
    seams, and limit in $omega$.  The identity storage $P=I$ does not solve
    the problem: the source injection contributes an uncompensated positive
    rank-one term.
  ],
)

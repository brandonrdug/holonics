#let completed-source-volterra-frame-defect = (
  key: "theorem:completed-source-volterra-frame-defect",
  kind: [Theorem],
  title: [The bipolar source defect is the Gram deficit of one causal action-current frame],
  status: [
    Exact reflection--Volterra factorization and null-mode reduction;
    the causal frame bound remains RH-equivalent
  ],
  depends: (
    "theorem:completed-source-event-port-transport",
  ),
  claim: [
    Fix $omega>0$ and a logarithmic cut $tau>0$.  On
    $
      cal(E)_tau=L^2(0,tau)
    $
    retain the completed source current
    $
      psi_omega(u)
      =
      j_omega'(u)
      =
      sum_(log n<=u)
      w_omega(n)phi_omega(u-log n),
      quad
      psi_omega(u)=0 " for "u<0.
    $
    Define causal transport and receiver reflection by
    $
      (cal(V)_(omega,tau)F)(r)
      =
      integral_0^r
      psi_omega(r-s)F(s)dif s,
      quad "(CAUSAL TRANSPORT)"
    $
    and
    $
      (cal(R)_tau F)(s)=F(tau-s).
      quad "(RECEIVER REFLECTION)"
    $
    Then $cal(R)_tau$ is a self-adjoint unitary and the logarithmic Hankel
    cut from `theorem:completed-source-event-port-transport` factors as
    $
      cal(H)_(omega,tau)
      =
      cal(R)_tau cal(V)_(omega,tau).
      quad "(REFLECTED CURRENT)"
    $
    Self-adjointness of $cal(H)_(omega,tau)$ consequently gives
    $
      cal(R)_tau cal(V)_(omega,tau)cal(R)_tau
      =
      cal(V)_(omega,tau)^*,
    $
    $
      cal(H)_(omega,tau)^2
      =
      cal(V)_(omega,tau)^*
      cal(V)_(omega,tau).
      quad "(ROUND TRIP)"
    $
    Hence the two standing orientations have one exact shared defect:
    $
      cal(D)_(omega,tau)
      :=
      (
        I-cal(H)_(omega,tau)
      )
      (
        I+cal(H)_(omega,tau)
      )
      =
      I-cal(V)_(omega,tau)^*
      cal(V)_(omega,tau).
      quad "(BIPOLAR DEFECT)"
    $
    Since $cal(H)_(omega,tau)$ is compact and self-adjoint, the following
    are equivalent:
    $
      I+epsilon cal(H)_(omega,tau)>=0
      quad "for both "epsilon=plus.minus 1;
      quad "(TWO ORIENTATIONS)"
    $
    $
      cal(D)_(omega,tau)>=0;
      quad "(ROUND-TRIP PASSIVITY)"
    $
    $
      norm(cal(V)_(omega,tau))<=1.
      quad "(CAUSAL CONTRACTION)"
    $

    This defect has a source-native continuous Gram factorization.  For
    $0<r<tau$, let
    $
      k_(omega,r)(s)
      =
      overline(psi_omega(r-s))
      bold(1)_(0<s<r).
      quad "(ACTION-CURRENT FACE)"
    $
    Then
    $
      (cal(V)_(omega,tau)F)(r)
      =
      chevron.l F,k_(omega,r)chevron.r,
    $
    and define the rank-one current operator by
    $
      cal(P)_(omega,r)F
      =
      chevron.l F,k_(omega,r)chevron.r
      k_(omega,r).
    $
    Then
    $
      cal(V)_(omega,tau)^*cal(V)_(omega,tau)
      =
      integral_0^tau
      cal(P)_(omega,r)dif r
      quad "(CURRENT GRAM)"
    $
    as a weak operator integral.  Therefore the complete bipolar law at
    the cut is exactly the continuous Bessel inequality
    $
      integral_0^tau
      abs(
        lr(chevron.l F,k_(omega,r)chevron.r)
      )^2
      dif r
      <=
      norm(F)^2
      quad "for every "F in cal(E)_tau.
      quad "(ACTION-CURRENT CAPACITY)"
    $
    No detached edge, independently selected mode, or later positivity
    carrier has entered: each $k_(omega,r)$ is the whole arithmetic--Gamma
    current visible at causal time $r$.

    The causal factorization also gives a noncircular strict departure
    from rest.  Young's inequality yields
    $
      norm(cal(V)_(omega,tau))
      <=
      integral_0^tau abs(psi_omega(u))dif u.
      quad "(LOCAL SOURCE BOUND)"
    $
    The locally integrable endpoint behavior of the completed source makes
    the right side tend to zero as $tau arrow.r 0^+$.  Hence every fixed
    $omega>0$ has a nonempty interval $0<tau<tau_omega$ on which the
    bipolar defect is strictly positive.  This uses the actual source
    current and no hypothesis about its whole-ray continuation.

    The former split between boundary-visible and port-dark null modes is
    not a split in the remaining proof object.  If
    $
      (
        I+epsilon cal(H)_(omega,tau)
      )F=0
      quad
      (F!=0),
    $
    then
    $
      cal(V)_(omega,tau)F
      =
      -epsilon cal(R)_tau F,
    $
    $
      cal(V)_(omega,tau)^*
      cal(V)_(omega,tau)F
      =
      F,
      quad
      norm(cal(V)_(omega,tau)F)=norm(F).
      quad "(UNIT-GAIN SATURATION)"
    $
    Conversely, every nonzero vector satisfying
    $
      cal(V)_(omega,tau)^*cal(V)_(omega,tau)F=F
    $
    lies in the orthogonal sum of the $+1$ and $-1$ eigenspaces of
    $cal(H)_(omega,tau)$.  When ("ROUND-TRIP PASSIVITY") holds, this is
    exactly equality in ("ACTION-CURRENT CAPACITY").  Its value at the
    exposed port determines whether the crossing is visible in the
    infinitesimal chart; it does not define another kind of obstruction.

    Finally let $cal(V)_(omega,infinity)$ denote causal convolution by
    $psi_omega$ on the whole positive logarithmic ray.  All finite
    inequalities ("ACTION-CURRENT CAPACITY") hold if and only if this
    whole causal transport is a contraction.  In the initial convergence
    half-plane its Laplace transfer is
    $
      hat(psi)_omega(p)
      =
      integral_0^infinity
      psi_omega(u)e^(-p u)dif u
      =
      Theta_omega(i p)
      =
      frac(
        Xi(omega-p),
        Xi(omega+p)
      ).
      quad "(CAUSAL TRANSFER)"
    $
    Thus whole-ray contraction is equivalent to this transfer extending
    as a Schur function on $op("Re")p>0$.  Under $z=i p$, this is exactly
    innerness of $Theta_omega$ on the upper half-plane.  Requiring it for
    every $omega>0$ is therefore equivalent to RH.  More locally, if
    $
      p=x+i y,
      quad 0<x<omega,
    $
    and the displayed normal segment avoids a zero, the finite
    normal-sweep identity gives
    $
      -log abs(hat(psi)_omega(x+i y))
      =
      integral_(omega-x)^(omega+x)
      op("Re")[
        frac(Xi'(r+i y),Xi(r+i y))
      ]
      dif r.
      quad "(NORMAL CAUSAL FLUX)"
    $
    At regular points, pointwise interior contractivity is therefore the
    nonnegative orientation of this normal flux.  Global Schur conduct
    additionally requires the pole-free analytic continuation; neither
    property follows from the unit-modulus boundary face.
  ],
  proof: [
    The support of $psi_omega$ reduces the logarithmic Hankel operator to
    $cal(E)_tau$.  Directly,
    $
      (
        cal(R)_tau cal(V)_(omega,tau)F
      )(s)
      =
      integral_0^(tau-s)
      psi_omega(tau-s-t)F(t)dif t
      =
      (
        cal(H)_(omega,tau)F
      )(s),
    $
    which proves ("REFLECTED CURRENT").  Since the source kernel is real,
    $cal(H)_(omega,tau)$ is self-adjoint.  Taking the adjoint of
    $cal(H)=cal(R)cal(V)$ and using $cal(R)^2=I$ proves the reflected
    adjoint identity and ("ROUND TRIP").  The two factors
    $I-cal(H)$ and $I+cal(H)$ commute, so their product is
    ("BIPOLAR DEFECT").  The spectral theorem for the compact
    self-adjoint $cal(H)$ proves the equivalence of
    ("TWO ORIENTATIONS"), ("ROUND-TRIP PASSIVITY"), and
    ("CAUSAL CONTRACTION").

    The definition of $k_(omega,r)$ gives
    $
      cal(V)F(r)=chevron.l F,k_(omega,r)chevron.r.
    $
    Integrating the squared amplitudes proves ("CURRENT GRAM") weakly and
    turns nonnegativity of $I-cal(V)^*cal(V)$ into
    ("ACTION-CURRENT CAPACITY").
    Young's convolution inequality proves ("LOCAL SOURCE BOUND"), and
    local integrability of $psi_omega$ proves its strict small-cut
    consequence.

    If $(I+epsilon cal(H))F=0$, then
    $cal(H)F=-epsilon F$.  Multiplication by $cal(R)$ and
    $cal(H)=cal(R)cal(V)$ gives
    $cal(V)F=-epsilon cal(R)F$, hence ("UNIT-GAIN SATURATION").
    Conversely, equality in the positive operator
    $I-cal(H)^2$ places a vector in
    $ker(I-cal(H)^2)=ker(I-cal(H))⊕ker(I+cal(H))$.

    Zero-extension and monotone convergence show that contraction of the
    whole causal convolution implies every finite compression and that
    uniform contraction of all finite compressions defines the whole
    contraction.  The completed source Mellin identity is
    $
      Theta_omega(z)
      =
      integral_0^infinity
      psi_omega(u)e^(i z u)dif u
    $
    in its convergence half-plane.  Substitution $z=i p$ proves
    ("CAUSAL TRANSFER").  The Laplace--Hardy correspondence identifies
    contractive causal convolution with a Schur transfer on the right
    half-plane.  The rotation $z=i p$ carries that half-plane to the upper
    half-plane, where Suzuki's inner-family criterion is equivalent to RH.
    Finally, substitute $z=-y+i x$ into the completed normal-sweep identity
    from `theorem:completed-scattering-hankel-successor`; because
    $i(x+i y)=-y+i x$, this gives ("NORMAL CAUSAL FLUX").
  ],
  boundary: [
    This theorem removes a false continuation.  Boundary-visible unit
    modes and port-dark null modes must not be pursued as separate
    populations.  They are the same possible equality case of one
    source-derived continuous frame.  The exact proof-bearing statement
    is now
    $
      I-
      integral_0^tau
      cal(P)_(omega,r)dif r
      >=0
      quad
      "for every "tau>0,\ omega>0.
      quad "(SOURCE FRAME DEFICIT)"
    $
    Its initial body is the identity, not an empty receiver, and its
    entire load is the causal current
    $psi_omega=nu_omega ast phi_omega$.

    The factorization does not prove ("SOURCE FRAME DEFICIT").  Through
    ("CAUSAL TRANSFER"), that inequality at every cut is exactly the RH
    Schur/innerness condition already sought; invoking generic
    contractive-system realization would merely return the desired sign
    as an assumption.  A genuinely new proof must derive the continuous
    Bessel bound from the arithmetic admissions $w_omega(n)$ and the
    common archimedean response $phi_omega$, or equivalently prove
    positivity of the source kernel
    $
      frac(
        1-
        hat(psi)_omega(p)
        overline(hat(psi)_omega(q)),
        p+overline(q)
      )
      quad
      (op("Re")p,op("Re")q>0)
      quad "(SOURCE SCHUR KERNEL)"
    $
    without assuming its analytic contractive continuation.  This is the
    present analytic obligation.  The local source bound proves that this
    obligation starts from a genuine strict body; ("NORMAL CAUSAL FLUX")
    shows exactly what can fail as the receiver grows.  Another Schur
    block, crossing census, or null-mode taxonomy would not advance it.
  ],
)

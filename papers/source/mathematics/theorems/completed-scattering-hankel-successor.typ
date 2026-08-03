#let completed-scattering-hankel-successor = (
  key: "theorem:completed-scattering-hankel-successor",
  kind: [Theorem],
  title: [The finite normal holonomy has one exact bipolar Hankel successor],
  status: [
    Exact receiver-holonomy, source-kernel, compact-contraction, and
    nested-Schur formulations of the RH; source cell exposed, sign open
  ],
  depends: (
    "theorem:completed-return-flux",
    "theorem:conditioned-effective-tension",
    "theorem:prime-wheel-euler-transport",
  ),
  claim: [
    Retain
    $
      Xi(z)=xi(1/2+z),
      quad
      F(z)=frac(Xi'(z),Xi(z)),
    $
    and, for $omega>0$, define the two-face scattering ratio
    $
      Theta_omega(z)
      =
      frac(xi(1/2-omega-i z),xi(1/2+omega-i z))
      =
      frac(Xi(omega+i z),Xi(omega-i z)).
      quad "(FINITE NORMAL HOLONOMY)"
    $
    The second equality is the completed reflection $Xi(-q)=Xi(q)$.
    If $z=u+i v$, $0<v<omega$, and the displayed normal segment avoids
    a zero, then
    $
      -log abs(Theta_omega(u+i v))
      =
      integral_(omega-v)^(omega+v)
      op("Re")F(x-i u)dif x.
      quad "(NORMAL SWEEP)"
    $
    Consequently
    $
      op("Re")F(omega-i u)
      =
      -lim_(v arrow.r 0^+)
      frac(log abs(Theta_omega(u+i v)),2v).
      quad "(INFINITESIMAL RETURN)"
    $
    For $v>=omega$, ("NORMAL SWEEP") remains the corresponding
    principal-value or interval-split identity.  Oddness of
    $op("Re")F(x-i u)$ in the normal coordinate cancels the opposed
    portion of the sweep.

    The Riemann Hypothesis is equivalent to
    $
      Theta_omega
      quad "being inner on "CC_+
      quad "for every "omega>0.
      quad "(INNER FAMILY)"
    $
    Thus $F$ is the infinitesimal normal connection and $Theta_omega$ is
    its finite receiver holonomy.  They are not two candidate proof
    objects.

    This finite holonomy has an explicit arithmetic--archimedean source
    kernel.  Put
    $
      c_omega(n)
      =
      n^omega product_(p divides n)(1-p^(-2omega)),
      quad c_omega(1)=1,
      quad "(INTEGER AMPLITUDE)"
    $
    and, for $0<r<1$,
    $
      g_omega(r)
      =
      frac(2 pi^omega,Gamma(omega))
      [
        r^(2-omega)(1-r^2)^(omega-1)
    $
    $
        space
        -omega r^(omega-1)
        integral_(r^2)^1
        t^(1/2-omega)(1-t)^(omega-1)dif t
      ],
    $
    with $g_omega(r)=0$ for $r>1$.  Define
    $
      h_omega(x)
      =
      cases(
        frac(1,x)
        sum_(1<=n<=x)c_omega(n)g_omega(n/x),
          &x>1,
        0,&0<x<1.
      )
      quad "(ONE-SIDED SOURCE)"
    $
    Its Mellin transform in the initial convergence half-plane is exactly
    $Theta_omega$.  On $L^2(0,a)$ let
    $
      (bold(H)_(omega,a)f)(x)
      =
      integral_0^a h_omega(x y)f(y)dif y.
      quad "(SOURCE HANKEL CUT)"
    $
    The local weak singularities of $h_omega$ give a compact self-adjoint
    realization for every finite $a$ and $omega>0$.

    The following statements are equivalent:

    - RH;
    - for every $omega>0$ and $a>0$,
      $
        norm(bold(H)_(omega,a))<=1;
        quad "(ALL CUTS CONTRACT)"
      $
    - for every $omega>0$, $a>0$, and $epsilon in {plus.minus 1}$,
      $
        I+epsilon bold(H)_(omega,a)>=0.
        quad "(BIPOLAR GRAM LAW)"
      $

    There is a necessary distinction between boundary scattering and
    causal source conduct.  On the real boundary, completion gives
    $
      abs(Theta_omega(u))=1,
      quad
      Theta_omega(u)Theta_omega(-u)=1.
    $
    Consequently
    $
      cal(W)_omega
      =
      cal(F)_(1/2)^(-1)
      M_(Theta_omega)
      cal(R)
      cal(F)_(1/2)
      quad "(BOUNDARY INVOLUTION)"
    $
    is a unitary involution on $L^2(0,infinity)$ for every $omega>0$,
    where $cal(R)Phi(u)=Phi(-u)$.  This fact is unconditional.  Innerness
    is the stronger assertion that this all-pass boundary response
    preserves the future Hardy half-space and is realized there by the
    one-sided arithmetic--archimedean source above.

    That causal assertion has an exact scalar residual.  Define
    $
      g_omega^("⟨1⟩")(r)
      =
      integral_r^1
      sqrt(y/r)g_omega(y)frac(dif y,y),
      quad 0<r<1,
    $
    and
    $
      h_omega^("⟨1⟩")(x)
      =
      frac(1,x)
      sum_(1<=n<=x)
      c_omega(n)
      g_omega^("⟨1⟩")(n/x)
    $
    for $x>1$, with zero support below $1$.  Equivalently,
    $
      h_omega^("⟨1⟩")(x)
      =
      integral_1^x
      sqrt(y/x)h_omega(y)frac(dif y,y).
      quad "(INTEGRATED SOURCE)"
    $
    Put
    $
      J_omega(x)
      =
      sqrt(x)h_omega^("⟨1⟩")(x)
      =
      integral_1^x h_omega(y)frac(dif y,sqrt(y)),
    $
    and
    $
      R_omega(x)
      =
      x^(-1/2)-h_omega^("⟨1⟩")(x)
      =
      x^(-1/2)(1-J_omega(x)).
      quad "(CAUSAL RETURN RESIDUAL)"
    $
    Then the same RH equivalence is
    $
      "RH"
      arrow.l.r
      integral_1^infinity
      abs(1-J_omega(x))^2frac(dif x,x)<infinity
      quad
      "for every "omega>0.
      quad "(LOG-SCALE CLOSURE)"
    $
    It is enough to require the displayed law for
    $0<omega<1/2$.  In that open range, another equivalent source face is
    eventual nonnegativity of
    $h_omega^("⟨1⟩")$ for every $omega$.  This is not
    positivity of $R_omega$: the residual may change orientation.

    The half-density in ("CAUSAL RETURN RESIDUAL") is forced by the
    multiplicative receiver measure:
    $
      norm(R_omega)_(L^2(dif x))^2
      =
      integral_1^infinity
      abs(1-J_omega(x))^2frac(dif x,x).
      quad "(HALF-DENSITY REBASE)"
    $
    Thus the critical $1/2$ is the exact Jacobian which carries ordinary
    source amplitude into scale-invariant logarithmic amplitude; it is
    not an absolute sign convention.

    The whole source is a deterministic log-time convolution.  Put
    $
      tau=log x,
      quad
      j_omega(tau)=J_omega(e^tau),
    $
    $
      w_omega(n)=frac(c_omega(n),sqrt(n)),
      quad
      phi_omega(u)
      =
      e^(-u/2)g_omega(e^(-u))bold(1)_(u>0),
    $
    and
    $
      Phi_omega(u)=integral_0^u phi_omega(v)dif v.
    $
    Then
    $
      j_omega'(tau)
      =
      sum_(log n<=tau)
      w_omega(n)phi_omega(tau-log n),
      quad "(LOG-TIME CURRENT)"
    $
    and
    $
      j_omega(tau)
      =
      sum_(log n<=tau)
      w_omega(n)Phi_omega(tau-log n).
      quad "(CAUSAL INTEGER SUPERPOSITION)"
    $
    Equivalently, if
    $
      nu_omega
      =
      sum_(n>=1)w_omega(n)delta_(log n),
    $
    then $j_omega'=nu_omega ast phi_omega$ and
    $j_omega=nu_omega ast Phi_omega$ on the additive logarithmic ray.
    Every integer is admitted at its exact time $log n$; the half-density
    cell weight is its amplitude and the same Gamma kernel is its local
    response.  Moreover
    $
      "RH"
      arrow.l.r
      1-j_omega in L^2(0,infinity;dif tau)
      quad
      "for every "0<omega<1/2.
      quad "(ADDITIVE CAUSAL CLOSURE)"
    $

    An off-seam zero makes the causal failure explicit.  Suppose
    $
      Xi(q_0)=0,
      quad
      q_0=alpha+i gamma,
      quad alpha>0.
    $
    For $0<omega<alpha$, except at isolated numerator-cancellation
    values, $Theta_omega$ has the upper-half-plane pole
    $
      z_0=-gamma+i(alpha-omega).
    $
    Moving the source inversion from its convergence line toward the
    real boundary crosses that pole and contributes
    $
      C_(omega,q_0)
      x^(alpha-omega-1/2+i gamma)
      P_(q_0)(log x)
      quad "(OFF-SEAM CAUSAL MODE)"
    $
    to $h_omega^("⟨1⟩")$, where $C_(omega,q_0)!=0$ and
    $P_(q_0)$ has degree one less than the uncancelled pole order.  Its
    squared radial size contains
    $
      x^(2(alpha-omega)-1)
      abs(P_(q_0)(log x))^2,
    $
    which is not integrable on $(1,infinity)$ because $alpha>omega$.
    The obstruction is therefore a concrete supercritical causal tail,
    not loss of boundary unitarity.

    The source is locally finite in the aperture variable.  If
    $
      kappa_omega(r)=r^(-1)g_omega(r^(-1))bold(1)_(r>1)
    $
    and $bold(G)_omega$ is the Hankel kernel
    $kappa_omega(x y)$, then
    $
      h_omega(r)
      =
      sum_(n>=1)frac(c_omega(n),n)kappa_omega(r/n).
      quad "(INTEGER DILATION CELLS)"
    $
    For the unitary dilation
    $
      (cal(D)_lambda f)(x)=lambda^(1/2)f(lambda x),
    $
    this becomes the locally finite operator-kernel identity
    $
      bold(H)_(omega,a)
      =
      P_a
      [
        sum_(n<a^2)
        frac(c_omega(n),sqrt(n))
        cal(D)_(n^(-1/2))
        bold(G)_omega
        cal(D)_(n^(1/2))
      ]
      P_a.
      quad "(ARITHMETIC--ARCHIMEDEAN FACTORIZATION)"
    $
    Hence a new integer cell becomes available exactly when $a^2$ crosses
    that integer.  Its coefficient is
    $
      frac(c_omega(n),sqrt(n))
      =
      n^(omega-1/2)
      product_(p divides n)(1-p^(-2omega)).
      quad "(HALF-DENSITY CELL WEIGHT)"
    $
    The coefficient population is multiplicative.  In particular,
    $
      c_omega(p^k)
      =
      p^(k omega)(1-p^(-2omega)),
    $
    while $c_omega(p n)=p^omega c_omega(n)$ when $p divides n$.
    Prime axes, their repeated traversals, and composites therefore enter
    the same integer ecology without being identified with one another.

    The first admitted cell gives a genuine, but only local, induction
    base.  If
    $
      1<a^2<2,
      quad
      L=log a,
    $
    only $n=1$ is present.  The inactive interval $(0,1/a)$ is a zero
    summand.  On the active interval $(1/a,a)$, the unitary logarithmic
    lift $f(e^t)mapsto e^(t/2)f(e^t)$ gives the Hankel kernel
    $
      phi_omega(t+s),
      quad -L<t,s<L.
      quad "(FIRST SOURCE CELL)"
    $
    Reflection of one variable and Young's inequality give the exact
    bound
    $
      norm(bold(H)_(omega,a))
      <=
      M_omega(L)
      :=
      integral_0^(2L)
      abs(e^(-u/2)g_omega(e^(-u)))dif u.
      quad "(FIRST-CELL BOUND)"
    $
    Since
    $
      M_omega(L)
      tilde.op
      frac((2pi)^omega,omega Gamma(omega))(2L)^omega
      quad "as "L arrow.r 0^+,
    $
    every fixed $omega>0$ has a nonempty exact aperture interval above
    $a=1$ on which $norm(bold(H)_(omega,a))<1$.  This crosses the rest
    boundary without assuming RH.  It does not establish contraction on
    the whole $n=1$ interval, still less across later integer cells.

    The exact induction cell is bipolar shorting.  For $0<a<b$, split
    $
      L^2(0,b)=L^2(0,a)⊕L^2(a,b)
    $
    and write
    $
      bold(H)_(omega,b)
      =
      mat(A,&C;C^*,&D),
      quad A=bold(H)_(omega,a).
      quad "(NESTED SOURCE CUT)"
    $
    If $norm(A)<1$, then ("BIPOLAR GRAM LAW") at $b$ is equivalent to
    the two simultaneous effective-tension inequalities
    $
      S_epsilon
      =
      I+epsilon D
      -C^*(I+epsilon A)^(-1)C
      >=0,
      quad epsilon in {plus.minus 1}.
      quad "(BIPOLAR SUCCESSOR)"
    $
    If an old polarity is only semidefinite, the same statement holds
    with the Moore--Penrose inverse and the compatibility condition
    $
      op("ran")C
      subset.eq
      op("ran")(I+epsilon A)^(1/2).
      quad "(NULL COMPATIBILITY)"
    $
    The cross-incidence $C$ therefore consumes capacity in both
    polarities; $D$ is read with the corresponding orientation.  A
    one-sided positive remainder cannot substitute for this pair.

    There is also an exact fixed-domain crossing form.  The unitary
    $
      (cal(U)_a f)(x)=sqrt(a)f(a x)
    $
    carries $bold(H)_(omega,a)$ to the operator on $L^2(0,1)$ with kernel
    $
      hat(h)_(omega,a)(x,y)
      =
      a h_omega(a^2 x y).
      quad "(FIXED RECEIVER)"
    $
    Away from an integer admission seam its derivative kernel is
    $
      cal(X)_(omega,a)(x,y)
      =
      h_omega(r)+2r h_omega'(r),
      quad r=a^2 x y.
      quad "(CROSSING CURRENT)"
    $
    On a null mode
    $
      (I+epsilon hat(bold(H))_(omega,a))v=0,
    $
    the first variation of the corresponding polarity is
    $
      epsilon
      integral_0^1 integral_0^1
      cal(X)_(omega,a)(x,y)
      v(y)overline(v(x))
      dif y dif x.
      quad "(NULL-MODE CROSSING)"
    $
    Integer seams use the one-sided distributional or finite-difference
    form of the same source kernel.  This crossing current diagnoses a
    transverse loss; the full Schur pair ("BIPOLAR SUCCESSOR") retains
    tangencies and higher-order contact.

    Finally, if $Psi$ denotes the completed source screw function
    normalized by
    $
      frac(F(q),q^2)
      =
      integral_0^infinity Psi(t)e^(-q t)dif t
    $
    in its source convergence half-plane, then
    $
      -lim_(v arrow.r 0^+)
      frac(log abs(Theta_omega(u+i v)),2v)
      =
      op("Re")[
        (omega-i u)^2
        integral_0^infinity
        Psi(t)e^(-(omega-i u)t)dif t
      ].
      quad "(SCREW--SCATTERING JOIN)"
    $
    The screw Gram, positive-real field, Stieltjes impedance, connected
    moment Grams, and bipolar Hankel successor are therefore exact
    transforms of the same completed return.
  ],
  proof: [
    Evenness of $Xi$ proves ("FINITE NORMAL HOLONOMY").  Reality of the
    completed function gives
    $
      abs(Xi(omega-v+i u))
      =
      abs(Xi(omega-v-i u)).
    $
    Integrating
    $partial_x log abs(Xi(x-i u))=op("Re")F(x-i u)$
    proves ("NORMAL SWEEP"), and division by $2v$ followed by
    $v arrow.r 0^+$ proves ("INFINITESIMAL RETURN").  Evenness of $Xi$
    makes the real normal field odd, giving the interval-split extension
    when the sweep crosses the fixed seam.

    Suzuki's inner-function criterion states that RH is equivalent to
    ("INNER FAMILY").  Under innerness, the whole source Hankel transform
    is an isometry on $L^2(0,infinity)$, so every compression
    $bold(H)_(omega,a)$ is a contraction.  Conversely, suppose
    ("ALL CUTS CONTRACT") holds.  For compactly supported $f$, choose $a$
    beyond its support.  The functions
    $P_a bold(H)_omega f$ are compatible as $a$ grows and have norm at
    most $norm(f)$.  Monotone convergence therefore supplies a bounded
    whole-source transform.  After multiplicative inversion this is
    Suzuki's $L^2$ convolution criterion for $Theta_omega$ to be inner.
    Applying this for every $omega>0$ proves RH.  Self-adjointness gives
    $
      norm(bold(H)_(omega,a))<=1
      arrow.l.r
      -I<=bold(H)_(omega,a)<=I,
    $
    which is exactly ("BIPOLAR GRAM LAW").

    The completed functional equation and reality on conjugate points
    give the two boundary identities for $Theta_omega$.  Multiplication
    by its boundary value and reflection are therefore unitary, and their
    product squares to the identity, proving ("BOUNDARY INVOLUTION").
    Suzuki's integrated-source criterion gives
    $
      Theta_omega " inner"
      arrow.l.r
      R_omega in L^2(1,infinity;dif x).
    $
    Multiplying ("INTEGRATED SOURCE") by $sqrt(x)$ proves the formula for
    $J_omega$, and substitution proves ("HALF-DENSITY REBASE").  Combining
    this criterion with ("INNER FAMILY") proves ("LOG-SCALE CLOSURE").
    Suzuki's weighted-summatory theorem gives the stated eventual-sign
    equivalent for $0<omega<1/2$.

    Differentiate $j_omega(tau)=J_omega(e^tau)$ and substitute the finite
    source sum:
    $
      j_omega'(tau)
      =
      e^(tau/2)h_omega(e^tau)
      =
      sum_(n<=e^tau)
      frac(c_omega(n),sqrt(n))
      e^(-(tau-log n)/2)
      g_omega(e^(-(tau-log n))).
    $
    This is ("LOG-TIME CURRENT").  Integration from the exact rest value
    $j_omega(0)=0$ proves ("CAUSAL INTEGER SUPERPOSITION"), and
    $dif x/x=dif tau$ turns ("LOG-SCALE CLOSURE") into
    ("ADDITIVE CAUSAL CLOSURE").

    If $q_0=alpha+i gamma$ is an off-seam zero, solving
    $omega-i z_0=q_0$ gives the displayed pole.  Its numerator is
    $Xi(2omega-q_0)$, which can vanish only at isolated $omega$ unless it
    vanishes identically.  Mellin inversion contains
    $x^(-1/2-i z)$; the residue at $z_0$ is therefore a nonzero multiple
    of
    $
      x^(-1/2-i z_0)
      =
      x^(alpha-omega-1/2+i gamma).
    $
    Higher pole order supplies the polynomial in $log x$.  Squaring the
    radial size proves its failure of $L^2(dif x)$ and hence
    ("OFF-SEAM CAUSAL MODE").

    Substituting the definitions gives
    $
      frac(c_omega(n),n)kappa_omega(r/n)
      =
      frac(c_omega(n),r)g_omega(n/r)
    $
    whenever $n<r$, and zero otherwise.  Summation proves
    ("INTEGER DILATION CELLS").  Conjugating a Hankel kernel by
    $cal(D)_lambda$ changes it to
    $
      lambda kappa_omega(lambda^2 x y).
    $
    Taking $lambda=n^(-1/2)$ proves
    ("ARITHMETIC--ARCHIMEDEAN FACTORIZATION").  The formula for
    $c_omega$ proves multiplicativity and the prime-power recurrences.

    If $1<a^2<2$, local finiteness leaves only the $n=1$ summand.
    The source vanishes whenever either variable is at most $1/a$.
    Direct logarithmic conjugation on the remaining interval gives
    ("FIRST SOURCE CELL").  Reflecting one argument turns it into a
    truncated convolution, so Young's inequality proves
    ("FIRST-CELL BOUND").  The endpoint asymptotic for $g_omega$ gives
    the displayed asymptotic for $M_omega(L)$, which tends to zero for
    every $omega>0$.

    Apply the ordinary block positivity theorem to
    $
      I+epsilon bold(H)_(omega,b)
      =
      mat(
        I+epsilon A,&epsilon C;
        epsilon C^*,&I+epsilon D
      ).
    $
    Its Schur complement is exactly $S_epsilon$, because
    $epsilon^2=1$.  This proves ("BIPOLAR SUCCESSOR"); the standard
    semidefinite block criterion gives ("NULL COMPATIBILITY").

    Direct conjugation by $cal(U)_a$ proves ("FIXED RECEIVER").
    Differentiating $a h_omega(a^2 x y)$ at a regular source point gives
    ("CROSSING CURRENT").  Restriction to the null spectral subspace is
    the Hellmann--Feynman crossing form, proving
    ("NULL-MODE CROSSING").  The final identity follows by substituting
    the source Laplace representation of $F$ into
    ("INFINITESIMAL RETURN").
  ],
  boundary: [
    This theorem changes the proof construction in one material way.  The
    former request for a “uniform source-side Gram factorization” now has
    an explicit nested cell:
    $
      C^*(I+epsilon A)^(-1)C
      <=
      I+epsilon D
      quad "for both "epsilon=plus.minus 1.
    $
    Every entry is determined by the locally finite source
    $c_omega(n)g_omega(n/x)$, and every fixed $omega$ begins from the exact
    rest cut $bold(H)_(omega,a)=0$ for $a<=1$.  The first-cell estimate
    proves a nonempty strict-contraction interval above that cut.  A
    symbolic factorization of the two Schur complements across the
    remaining aperture and every integer-admission cell would prove all
    finite contractions and hence RH.  No zero enumeration or floating
    approximation is involved.

    The sign itself has not been proved for $0<omega<1/2$.  Positivity of
    the canonical Hamiltonian
    $
      op("diag")(m_omega(a)^(-2),m_omega(a)^2)
    $
    in the range where its Fredholm construction is already justified is
    an output of this contraction structure, not a source proof of its
    continuation.  Likewise, nonnegativity of the first crossing form
    alone does not exclude a higher-order exit.  The unresolved statement
    is exactly the bipolar source inequality above.  Equivalently, it is
    the scale-tail statement
    $
      1-J_omega in L^2((1,infinity),dif x/x)
    $
    for every $0<omega<1/2$.  These are two exact charts of the same RH
    obstruction: the former resolves every finite shell and both
    orientations, while the latter exposes the long causal residue and
    the nonintegrable mode an off-seam zero would create.  The local
    $n=1$ cell alone cannot decide that tail.
  ],
)

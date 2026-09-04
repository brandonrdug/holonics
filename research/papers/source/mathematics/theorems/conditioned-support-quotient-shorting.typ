#let conditioned-support-quotient-shorting = (
  key: "theorem:conditioned-support-quotient-shorting",
  kind: [Theorem],
  title: [Conditioning returns every new shell direction through the old face],
  status: [
    Exact conditioned quotient, raw-to-conditioned block rechart, and
    source-native shorting criterion; the first analytic residual remains open
  ],
  depends: (
    "theorem:archimedean-remainder-amplitude",
    "theorem:prime-admission-cross-shell",
  ),
  claim: [
    Put
    $
      a_R=frac(log R,2),
      quad I_R=(-a_R,a_R),
    $
    and fix $sigma^2=1$ according to the Fourier convention.  In the final
    convention of the archimedean source, $sigma=-1$; reflection of the
    interval exchanges the two signs.  Define
    $
      M_R g
      =
      (
        integral_(I_R)g(u)dif u,
        integral_(I_R)e^(sigma u/2)g(u)dif u
      ),
      quad
      cal(T)_R=op("ker")(M_R) subset L^2(I_R).
      quad "(MOMENT FIBER)"
    $
    These, rather than $cal(Q)C_c^infinity(I_R)$, are the Hilbert amplitude
    fibers carrying the source's conditions
    $hat(g)(0)=hat(g)(sigma i/2)=0$.  The differential operator
    $
      cal(Q)=-(rho partial_rho)^2+frac(1,4)
    $
    instead imposes the two half-character conditions on a returned
    convolution.

    For the first successor let
    $
      I_o=I_2,
      quad I=I_3,
      quad S=I without I_o,
      quad
      cal(H)_o=L^2(I_o),
      quad cal(H)_s=L^2(S).
    $
    Write $M_o,M_s$ for the restrictions of $M_3$ to these two regions and
    $
      G_o=M_o M_o^*.
    $
    The two moment vectors $1,e^(sigma u/2)$ are independent on $I_o$, so
    $G_o$ is positive definite.  With $alpha=log(2)/2$, its exact matrix is
    $
      G_o
      =
      mat(
        log 2,&4sinh(log(2)/4);
        4sinh(log(2)/4),&1/sqrt(2)
      ).
      quad "(OLD MOMENT GRAM)"
    $
    Define
    $
      L=-M_o^* G_o^(-1) M_s,
      quad
      J y=(L y)⊕y.
      quad "(CONDITIONED LIFT)"
    $
    Then the amplitude successor has the exact orthogonal decomposition
    $
      cal(T)_3=cal(T)_2⊕J cal(H)_s
      quad "inside "L^2(I_3),
      quad
      J^*J=I+M_s^* G_o^(-1) M_s.
      quad "(CONDITIONED QUOTIENT)"
    $
    Thus shell restriction identifies the quotient
    $cal(T)_3/cal(T)_2$ with $cal(H)_s$, but a conditioned representative is
    never the detached shell $0⊕y$: it carries the old compensating face
    $L y$.

    Let a Hermitian operator or form on the raw split
    $cal(H)_o⊕cal(H)_s$ have, on a common core, the block expression
    $
      K=mat(A,&B;B^*,&D).
    $
    Let $P_o$ be the orthogonal projection of $cal(H)_o$ onto
    $cal(T)_2$.  In the conditioned coordinates
    $cal(T)_2⊕J cal(H)_s$, the same object has blocks
    $
      H_2=P_o A|_(cal(T)_2),
      quad
      C=P_o(A L+B),
    $
    $
      D_"cond"
      =
      L^* A L+L^* B+B^* L+D.
      quad "(CONDITIONED BLOCK)"
    $
    In particular, if a newly admitted prime is raw off-diagonal,
    $
      K_p=mat(0,&B_p;B_p^*,&0),
    $
    then
    $
      C_p=P_o B_p,
      quad
      D_(p,"cond")=L^* B_p+B_p^* L.
      quad "(RETURNED PRIME FACE)"
    $
    The prime has zero diagonal only before the moment fiber is imposed.

    Now let $q_3$ be the completed Weil form on its conditioned form domain
    and let $q_2=q_3|_(cal(T)_2)>=0$.  Shell restriction identifies the
    form-domain quotient with a dense subspace $cal(B)_2^circle$ of the
    Hilbert quotient above.  Choose any form-domain section
    $
      tilde(J):cal(B)_2^circle arrow.r op("dom")(q_3) inter cal(T)_3.
    $
    It need not equal the sharp $L^2$ section $J$, because a sharp
    old--shell cut need not preserve the form domain.  Put
    $
      cal(N)_2={x:q_2(x)=0}
    $
    and let $cal(E)_2$ be the completion of
    $cal(T)_2/cal(N)_2$ in the norm $sqrt(q_2)$.  For a quotient direction
    $y$, define
    $
      ell_y(x)=q_3(x,tilde(J) y).
    $
    The successor is nonnegative exactly when:

    - $ell_y$ annihilates $cal(N)_2$ and is continuous in the $q_2$-norm;
    - its Riesz carrier $c_y in cal(E)_2$, defined by
      $
        ell_y(x)=chevron.l [x],c_y chevron.r_(cal(E)_2),
      $
      exists for every admitted $y$; and
    - the invariant shorted shell
      $
        s_2(y)=q_3(tilde(J) y)-norm(c_y)^2_(cal(E)_2)
        quad "(FORM SHORT)"
      $
      is nonnegative.

    This criterion does not depend on the chosen form-domain lift.  Replacing
    $tilde(J) y$ by $tilde(J) y+k_y$ with $k_y in cal(T)_2$ translates $c_y$
    by $[k_y]$ and leaves $s_2(y)$ exact.

    In a bounded operator chart with old carrier $H_2>=0$ and cross operator
    $C_2$, continuity of every cross face is the range condition
    $
      op("Ran")(C_2) subset op("Ran")(H_2^(1/2)).
      quad "(RANGE)"
    $
    A bounded carrier $Y_2$ with $C_2=H_2^(1/2)Y_2$ exists exactly when,
    for some finite $c$,
    $
      C_2 C_2^*<=c H_2.
      quad "(DOUGLAS)"
    $
    The short is then $D_"cond"-Y_2^*Y_2$.  The weaker radical identity
    $C_2^*op("ker")(H_2)=0$ is not sufficient when
    $op("Ran")(H_2^(1/2))$ is not closed.

    There is a source-native continuous-kernel chart.  Let
    $D=i dif/dif u$ with Dirichlet boundary conditions and let $G_R$ be the
    localized screw-kernel operator.  For $v in H_0^1(I_R)$ and $w=D v$,
    $
      q_R(v)=chevron.l G_R w,w chevron.r.
    $
    The two amplitude moments become three exact current moments:
    $
      cal(K)_R
      =
      {
        w:
        integral w=0,
        integral u w(u)dif u=0,
        integral e^(sigma u/2)w(u)dif u=0
      }.
      quad "(CURRENT FIBER)"
    $
    Repeating ("CONDITIONED LIFT") with the three current-moment vectors
    gives the exact first current lift $J_D$, cross operator $C_(2,3)$, and
    conditioned shell operator $D_(2,3)$.

    The published base is positive definite, and the localized form has
    compact resolvent.  Hence its attained ground value satisfies
    $
      q_2(v)>=lambda_2 norm(v)^2,
      quad lambda_2>0.
      quad "(BASE GAP)"
    $
    The localized successor form is closed and lower-semibounded.  These two
    facts force every first-step cross functional to be $q_2$-continuous.
    In the bounded current chart this proves, rather than assumes,
    $
      op("Ran")(C_(2,3)) subset op("Ran")(G_2^(1/2)),
      quad
      C_(2,3) C_(2,3)^*<=c G_2
      quad "for some finite "c.
      quad "(FIRST CROSS CARRIED)"
    $
    Let $Y_(2,3)$ be the Douglas reduced solution
    $C_(2,3)=G_2^(1/2)Y_(2,3)$.  The only remaining sign in the first
    induction cell is
    $
      S_(2,3)
      =
      D_(2,3)-Y_(2,3)^*Y_(2,3)>=0.
      quad "(FIRST RESIDUAL)"
    $
    Equivalently, for every form-domain quotient direction,
    $
      chevron.l S_(2,3)y,y chevron.r
      =
      inf_x q_3(x+tilde(J) y),
      quad x in op("dom")(q_2).
      quad "(CONDITIONAL ENERGY)"
    $
  ],
  proof: [
    The matrix in ("OLD MOMENT GRAM") consists of the three elementary
    integrals of $1,e^(sigma u/2),e^(sigma u)$.  It is positive definite
    because the first two functions are linearly independent.  Moreover,
    $
      M_o L=-M_s,
    $
    so $J y$ is conditioned.  Every conditioned $(x,y)$ decomposes uniquely
    as
    $
      (x,y)=(x-L y,0)+J y.
    $
    The first term lies in $cal(T)_2$, while $L y$ lies in
    $op("Ran")(M_o^*)=cal(T)_2^perp$.  This proves the orthogonal
    decomposition and the metric formula.

    Substitute $(x+L y,y)$ into the raw quadratic form.  Collecting the
    old, cross, and shell terms gives ("CONDITIONED BLOCK").  Setting
    $A=D=0$ proves ("RETURNED PRIME FACE").

    For the form statement, Riesz representation gives $c_y$ precisely when
    the cross functional descends through the old radical and is continuous
    in the old form norm.  Completing the square in $cal(E)_2$ gives
    $
      q_3(x+tilde(J) y)
      =
      norm([x]+c_y)^2
      +
      s_2(y).
    $
    This proves necessity and sufficiency.  The same identity proves
    invariance under changing the quotient lift.  Douglas's factorization
    theorem gives the equivalence of ("RANGE") and ("DOUGLAS") with the
    bounded factorization.

    Finally, integration by parts with $v$ zero at both endpoints gives
    $
      integral D v=0,
      quad
      integral u D v=-i integral v,
      quad
      integral e^(sigma u/2)D v
      =-frac(i sigma,2)integral e^(sigma u/2)v.
    $
    This proves ("CURRENT FIBER").  The published screw representation then
    gives the bounded current chart.

    Positive definiteness of the attained base ground state proves
    ("BASE GAP").  If $q_3(z)>=-beta norm(z)^2$, its shifted form
    $
      a_3=q_3+(beta+1)chevron.l dot,dot chevron.r
    $
    is positive.  For $x$ in the old domain and fixed successor direction
    $z$, Cauchy--Schwarz in $a_3$ gives
    $
      abs(q_3(x,z))
      <=
      K_z sqrt(q_2(x)),
    $
    because ("BASE GAP") controls the old $L^2$ norm.  For
    $z=D^(-1)J_D y$, boundedness of $J_D$, $D^(-1)$, and the continuous screw
    kernel makes $K_z<=K norm(y)$.  Riesz representation followed by
    Douglas factorization proves ("FIRST CROSS CARRIED").  Completing the
    square gives ("CONDITIONAL ENERGY"), so the first successor is positive
    exactly when ("FIRST RESIDUAL") is positive.
  ],
  boundary: [
    The quotient, cross carriage, and shorting law are closed here; their
    missing datum is no longer an unspecified “positive successor.”  What
    remains is the single analytic theorem ("FIRST RESIDUAL") for the
    explicit zeta screw kernel. Published Sonin transport identifies the
    nested spaces, and the explicit formula identifies the raw prime cross,
    but neither source proves that this conditional shell energy is
    nonnegative. Proving it would close the first nontrivial
    $P(2) arrow.r P(3)$ cell. A Moore--Penrose inverse or a raw-shell
    calculation does not determine its sign.
  ],
)

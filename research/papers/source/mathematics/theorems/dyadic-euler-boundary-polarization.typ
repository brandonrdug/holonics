#let dyadic-euler-boundary-polarization = (
  key: "theorem:dyadic-euler-boundary-polarization",
  kind: [Theorem],
  title: [The first dyadic Euler contact is the polarization of two positive boundary channels],
  status: [Exact $R=4$, $p=2$ operator cell; no semilocal positivity conclusion],
  depends: (
    "lemma:normalized-euler-resolvent-return",
    "theorem:prime-power-aperture-incidence",
  ),
  claim: [
    Put
    $
      ell=log 2,
      quad
      a=2^(-1/2),
      quad
      I_4=[-ell,ell],
    $
    and divide $I_4$ into the four half-prime cells
    $
      A_1=[-ell,-ell/2],
      quad
      A_2=[-ell/2,0],
      quad
      A_3=[0,ell/2],
      quad
      A_4=[ell/2,ell].
    $
    Let $U=U_ell$ be logarithmic translation,
    $(U f)(v)=f(v+ell)$.  Choose normalized smooth vectors $e_3,e_4$
    supported in the interiors of $A_3,A_4$, respectively, and set
    $
      e_1=U e_3,
      quad
      e_2=U e_4,
      quad
      cal(V)_4=op("span"){e_1,e_2,e_3,e_4}.
    $
    These vectors are orthonormal.  If $P_4$ is multiplication by
    $1_(I_4)$, then the compressed translation
    $
      T=(P_4 U P_4)|_(cal(V)_4)
    $
    satisfies
    $
      T e_3=e_1,
      quad
      T e_4=e_2,
      quad
      T e_1=T e_2=0,
      quad
      T^2=0,
    $
    and therefore has the matrix
    $
      T=
      mat(
        0,0,1,0;
        0,0,0,1;
        0,0,0,0;
        0,0,0,0
      )
    $
    in the displayed basis.

    Let
    $
      cal(R)_2
      =
      a(I-a U)^(-1)
      =
      a sum_(n>=0)a^n U^n
    $
    be the normalized $p=2$ Euler resolvent, and put
    $
      r_4=(P_4 cal(R)_2 P_4)|_(cal(V)_4),
      quad
      z_4=((I-P_4)cal(R)_2P_4)|_(cal(V)_4).
    $
    Since $a=sqrt(1-a^2)$ and $T^2=0$,
    $
      r_4=a(I+a T).
      quad "(INTERIOR RETURN)"
    $
    For $x=sum_(j=1)^4 x_j e_j$, define the two exact boundary amplitudes
    $
      B_- x
      =
      (
        a x_1-a^2 x_3,
        a x_2-a^2 x_4
      ),
    $
    $
      B_+ x
      =
      (
        a x_1+a^2 x_3,
        a x_2+a^2 x_4
      ).
    $
    Then
    $
      I-r_4^*r_4=B_-^*B_-,
      quad
      z_4^*z_4=B_+^*B_+,
      quad "(TWO CHANNELS)"
    $
    and orthogonal aperture decomposition gives
    $
      P_4 cal(R)_2^* cal(R)_2 P_4-r_4^*r_4
      =
      z_4^*z_4.
      quad "(DEPARTURE)"
    $
    Consequently
    $
      I-P_4 cal(R)_2^* cal(R)_2 P_4
      =
      B_-^*B_--B_+^*B_+
      =
      -a(T+T^*).
      quad "(POLARIZATION)"
    $

    Whenever $x$ is the logarithmic current of an admitted returned test
    current $h$, the complete $p=2$ response on this cell is therefore
    $
      W_2(h)
      =
      ell(
        norm(B_+x)^2-norm(B_-x)^2
      ).
      quad "(PRIME FACE)"
    $
  ],
  proof: [
    Translation by $ell$ carries $A_3$ to $A_1$ and $A_4$ to $A_2$.
    A second translation leaves $I_4$ up to measure-zero boundary, proving
    the matrix for $T$ and $T^2=0$.  Compressing the Neumann series therefore
    gives ("INTERIOR RETURN").

    Direct multiplication gives
    $
      r_4^*r_4
      =
      a^2 I+a^3(T+T^*)+a^4 T^*T.
    $
    Since $a^2=1/2$, the restriction of $I-r_4^*r_4$ to each translated
    pair $(e_1,e_3)$ and $(e_2,e_4)$ is
    $
      mat(
        a^2,-a^3;
        -a^3,a^4
      )
      =
      mat(a;-a^2)mat(a,-a^2).
    $
    This is $B_-^*B_-$.

    Put $Q_4=I-P_4$.  Since $P_4$ and $Q_4$ are orthogonal,
    $
      P_4 cal(R)_2^* cal(R)_2 P_4
      =
      r_4^*r_4+z_4^*z_4.
    $
    The two departing tails satisfy
    $
      z_4e_3=a z_4e_1,
      quad
      z_4e_4=a z_4e_2,
      quad
      norm(z_4e_1)^2=norm(z_4e_2)^2=a^2.
    $
    Hence the Gram matrix of $z_4$ on either translated pair is
    $
      mat(
        a^2,a^3;
        a^3,a^4
      )
      =
      mat(a;a^2)mat(a,a^2),
    $
    proving ("TWO CHANNELS") and ("DEPARTURE").

    The Poisson-kernel metric of $cal(R)_2$, compressed to $cal(V)_4$, is
    $
      P_4 cal(R)_2^* cal(R)_2 P_4
      =
      I+a(T+T^*),
    $
    because no higher prime-power translate overlaps this cell.  Subtracting
    the two positive Gram matrices proves ("POLARIZATION").  Taking its
    quadratic form and applying the normalized Euler-resolvent response
    identity proves ("PRIME FACE").
  ],
  boundary: [
    This theorem does not make the prime response positive.  It identifies
    its sign-indefinite part exactly: the same core/shell incidence has a
    difference polarization $B_-$ retained by the compressed return and a
    sum polarization $B_+$ carried by the departing tail.  In the completed
    defect, $B_-$ contributes on the positive side and $B_+$ on the negative
    side.

    The equality $a^2=1-a^2=1/2$ is special to the first prime.  For the
    analogous $R=p^2$ two-cell chain, the determinant of
    $I-r^*r$ is $a^2(2a^2-1)$; it vanishes at $p=2$ and is negative for
    $p>2$.  This dyadic half is an exact normalization balance, not by itself
    the critical-line theorem.

    The calculation also fixes one ambient logarithmic Hilbert fiber, one
    aperture $P_4$, one translation law, and one receiver metric.  It is
    therefore an exact local edge face, not a complete three-frame counting
    return.  Arithmetic place admission, archimedean
    Fourier--Poisson--Mellin transport, and receiver/aperture change still
    owe an actual common incidence and the other cross-frame transports.
    Recasting this cell as a triangle without constructing those maps would
    only rename the missing relation.

    Global Poisson summation intertwines additive Fourier return with
    multiplicative inversion on a constrained Schwartz domain, and the
    semilocal Sonin isomorphism intertwines Fourier at fixed support.  Neither
    established map carries the outgoing amplitude $B_+$ into the
    independently constructed base remainder amplitude $A_2$, nor extends
    $A_2$ from $I_2$ to $I_4$.  The remaining proof-bearing datum is therefore
    a mixed support/place intertwiner coupling this explicit departing
    channel to the enlarged archimedean/Sonin carrier.
  ],
)

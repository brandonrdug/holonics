#let mellin-half-density-chart = (
  key: "lemma:mellin-half-density-chart",
  kind: [Lemma],
  title: [The critical half-density is the square-root Jacobian of logarithmic transport],
  status: [Classical change-of-variables and Fourier--Mellin identity],
  depends: ("lemma:mellin-return-seam",),
  claim: [
    Let $r=e^u$ and define
    $
      (cal(U)F)(u)=e^(u/2)F(e^u).
    $
    Then $cal(U)$ is unitary from
    $L^2(RR_(>0),dif r)$ to $L^2(RR,dif u)$ because
    $
      integral_0^infinity abs(F(r))^2 dif r
      =
      integral_(-infinity)^infinity
      abs(e^(u/2)F(e^u))^2 dif u.
    $
    With the Mellin convention
    $
      cal(M)F(s)
      =
      integral_0^infinity F(r)r^s frac(dif r,r),
    $
    the ordinary Fourier transform of $cal(U)F$ is
    $
      hat(cal(U)F)(t)
      =
      cal(M)F(1/2-i t).
    $
    Moreover, for
    $
      F^sharp(r)=r^(-1)overline(F(r^(-1))),
    $
    one has
    $
      cal(U)(F^sharp)(u)=overline((cal(U)F)(-u)).
    $
  ],
  proof: [
    Substitute $r=e^u$, so $dif r=e^u dif u$.  The factor $e^(u/2)$ is the
    square root of that Jacobian and gives the norm identity.  Substitution
    in the Fourier integral gives
    $
      integral_RR e^(u/2)F(e^u)e^(-i t u)dif u
      =
      integral_0^infinity
      F(r)r^(1/2-i t)frac(dif r,r).
    $
    Applying the same logarithmic change to $F^sharp$ gives the final
    reflection formula.
  ],
  boundary: [
    On multiplicative Haar measure $dif r/r$, the logarithmic chart already
    has unit Jacobian.  The half-density appears when that multiplicative
    geometry is related to the additive $L^2(dif r)$ normalization.  The
    identity explains the unitary status of the line
    $op("Re")(s)=1/2$; it does not locate the zeros of zeta.
  ],
)

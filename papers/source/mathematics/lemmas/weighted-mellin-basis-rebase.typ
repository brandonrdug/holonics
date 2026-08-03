#let weighted-mellin-basis-rebase = (
  key: "lemma:weighted-mellin-basis-rebase",
  kind: [Lemma],
  title: [The displayed Mellin midpoint is the half-weight of the transported measure],
  status: [Classical weighted change of variables; exact rebase family],
  depends: (
    "lemma:mellin-half-density-chart",
    "lemma:critical-seam-conjugacy",
  ),
  claim: [
    For $beta in RR$, give $RR_(>0)$ the weighted multiplicative measure
    $
      dif mu_beta(r)=r^beta frac(dif r,r).
    $
    Under $r=e^u$, define
    $
      (cal(U)_beta F)(u)=e^(beta u/2)F(e^u).
    $
    Initially for compactly supported smooth $F$, and then in the
    Plancherel sense on the corresponding $L^2$ completion,
    $
      cal(U)_beta:
      L^2(RR_(>0),dif mu_beta)
      arrow.r
      L^2(RR,dif u)
    $
    is unitary, and with the Mellin convention
    $
      cal(M)F(s)=integral_0^infinity F(r)r^s frac(dif r,r),
    $
    one has
    $
      hat(cal(U)_beta F)(t)
      =
      cal(M)F(beta/2-i t).
      quad "(WEIGHTED HALF)"
    $

    The weighted reciprocal-conjugate
    $
      F^(sharp_beta)(r)
      =
      r^(-beta)overline(F(r^(-1)))
    $
    becomes ordinary reflected conjugation:
    $
      cal(U)_beta(F^(sharp_beta))(u)
      =
      overline((cal(U)_beta F)(-u)).
    $
    Its Mellin involution is
    $
      J_beta(s)=beta-overline(s),
      quad
      op("Fix")(J_beta)={s:op("Re")(s)=beta/2}.
      quad "(WEIGHTED SEAM)"
    $

    For another weight $beta'$, multiplication by
    $
      (R_(beta arrow.r beta')F)(r)
      =
      r^((beta-beta')/2)F(r)
    $
    is a unitary rechart
    $
      L^2(dif mu_beta) arrow.r L^2(dif mu_(beta'))
    $
    satisfying
    $
      cal(U)_(beta')R_(beta arrow.r beta')=cal(U)_beta.
    $
    It transports the seam $op("Re")(s)=beta/2$ to
    $op("Re")(s')=beta'/2$ by the affine spectral rebase
    $
      s=s'+(beta-beta')/2.
    $
  ],
  proof: [
    On the stated dense domain, substitution $r=e^u$ gives
    $
      dif mu_beta=e^(beta u)dif u,
    $
    so $e^(beta u/2)$ is exactly its square-root density and proves
    unitarity.  The same substitution in the Fourier integral gives
    ("WEIGHTED HALF").  Direct substitution in $F^(sharp_beta)$ gives the
    reflected-conjugate identity, while changing variables $r arrow.r r^(-1)$
    in its Mellin transform gives
    $
      cal(M)(F^(sharp_beta))(s)
      =
      overline(cal(M)F(beta-overline(s))).
    $
    The fixed seam follows.  The norm of $R_(beta arrow.r beta')F$ against
    $dif mu_(beta')$ equals the norm of $F$ against $dif mu_beta$, and the
    displayed logarithmic and spectral identities follow by collecting
    powers of $r$.
  ],
  boundary: [
    The rational glyph $beta/2$ is typed by a measure and reciprocal law.
    It is not a numeral-radix effect and it is unrelated to the finite
    character factor $1/q$ unless another construction supplies a relation.
    Transporting the function, measure, and involution together is a
    rechart; changing only the measure or only the function is a different
    receiver problem.  The completed zeta normalization in the present paper
    uses $beta=1$.  This lemma explains the resulting $1/2$ chart but does
    not place any zero on its fixed seam.
  ],
)

#let mellin-return-seam = (
  key: "lemma:mellin-return-seam",
  kind: [Lemma],
  title: [Mellin return and its fixed seam],
  status: [Exact derivation from classical Mellin identities],
  depends: (),
  claim: [
    On $G=RR_(>0)^times$ with $dif^times x=dif x/x$, define
    $
      cal(M)f(s)=integral_0^infinity f(x)x^s dif^times x
    $
    and
    $
      f^sharp(x)=x^(-1) overline(f(x^(-1))).
    $
    For $h=f ast f^sharp$, $z=s-1/2$,
    $A_f(z)=cal(M)f(1/2+z)$, and $J(z)=-overline(z)$,
    $
      cal(M)h(1/2+z)
      =A_f(z) overline(A_f(J(z))).
    $
    The response is the norm square $abs(A_f(z))^2$ exactly on the fixed
    locus $J(z)=z$, equivalently $op("Re")(s)=1/2$.
  ],
  proof: [
    Multiplicative convolution gives
    $cal(M)(f ast g)=cal(M)f cal(M)g$. Substitution $y=x^(-1)$ gives
    $
      cal(M)(f^sharp)(s)
      =overline(cal(M)f(1-overline(s))).
    $
    Evaluating at $s=1/2+z$ yields the displayed factorization. Finally,
    $J(z)=z$ iff $z=-overline(z)$, which is exactly $op("Re")(z)=0$.
  ],
  boundary: [
    This identity explains why the critical line is the adjoint fixed seam.
    It does not imply that every nontrivial zeta zero lies there; that
    implication requires positivity of the completed explicit-formula return
    on the full admissible test family.
  ],
)

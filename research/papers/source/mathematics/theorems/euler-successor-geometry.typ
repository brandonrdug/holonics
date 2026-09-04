#let euler-successor-geometry = (
  key: "theorem:euler-successor-geometry",
  kind: [Theorem],
  title: [One-prime Euler successor geometry],
  status: [Exact laboratory derivation over published semilocal intertwiners],
  depends: ("lemma:mellin-return-seam",),
  claim: [
    Let $S$ be a finite set of places containing $infinity$, let
    $S'=S union {p}$, and suppose the semilocal Sonin intertwiners
    $theta_S$ and $theta_(S')$ are bounded Hilbert-space isomorphisms.
    Define
    $
      J_(S,p)=theta_(S') theta_S^(-1).
    $
    In the logarithmic spectral chart this successor is multiplication by
    $
      D_p(t)=1-p^(-1/2-i t),
    $
    equivalently $Delta_p=I-a_p U_p$ with
    $a_p=p^(-1/2)$ and $U_p=T_(log p)$ unitary. Its pulled-back metric is
    $
      G_p=J_(S,p)^*J_(S,p)
      =(1+a_p^2)I-a_p(U_p+U_p^*),
    $
    and obeys
    $
      (1-a_p)^2 I <= G_p <= (1+a_p)^2 I.
    $
    If $P$ is the predecessor Sonin projection and the successor Sonin
    range pulls back to $op("range")(P)$, then the pulled-back successor
    orthogonal projection is
    $
      Pi_p
      =((P G_p P)|_(op("range")(P)))^(-1) P G_p.
    $
    For every successor operator $A'=J_(S,p) A J_(S,p)^(-1)$,
    $
      J_(S,p)^(-1) A'^* J_(S,p)=G_p^(-1)A^*G_p.
    $
  ],
  proof: [
    The spectral multiplier gives the log-time finite difference directly.
    Expanding $Delta_p^*Delta_p$ gives $G_p$. The spectral range of
    $U_p+U_p^*$ lies in $[-2,2]$, which yields the two operator bounds and
    bounded invertibility. The displayed $Pi_p$ is the unique projection
    onto $op("range")(P)$ whose kernel is $G_p$-orthogonal to that range.
    The adjoint identity follows by substituting
    $A'=J_(S,p) A J_(S,p)^(-1)$ and $G_p=J_(S,p)^*J_(S,p)$.
  ],
  boundary: [
    The semilocal spaces, intertwiners, and Euler multiplier are inherited
    from Connes--Consani--Moscovici. The pulled-back metric, projection, and
    adjoint package is the laboratory's receiver-covariant synthesis. It
    proves neither a sign for the completed Weil form nor the Riemann
    Hypothesis.
  ],
)

#let positive-remainder-resolution-squeeze = (
  key: "theorem:positive-remainder-resolution-squeeze",
  kind: [Theorem],
  title: [A positive receiver remainder makes the resolution squeeze exact],
  status: [Exact Hilbert-space factorization; the semilocal remainder hypothesis remains open],
  depends: (
    "theorem:completed-defect-recurrence",
    "lemma:nested-aperture-deficit-persistence",
  ),
  claim: [
    Fix one final receiver $(S,R)$.  Let
    $
      A_S(f)=Theta_S(f)P_S
    $
    be Hilbert--Schmidt, so that
    $
      Sigma_S(f)=norm(A_S(f))_"HS"^2.
    $
    Suppose the completed defect has an independently constructed positive
    carrier: there are a Hilbert space $cal(K)_(S,R)$ and a linear map
    $C_(S,R)$ such that
    $
      Q_W(f)-Sigma_S(f)
      =
      norm(C_(S,R)f)^2
      quad "for every admitted" f.
    $

    Let $L_n$ and $M_n$ be increasing finite-rank orthogonal projections
    converging strongly to the identities on $H_S$ and $cal(K)_(S,R)$.
    Define
    $
      hat(Sigma)_n(f)
      =
      norm(L_n A_S(f))_"HS"^2
      +
      norm(M_n C_(S,R)f)^2
    $
    and
    $
      E_n(f)
      =
      norm((I-L_n)A_S(f))_"HS"^2
      +
      norm((I-M_n)C_(S,R)f)^2.
    $
    Then
    $
      hat(Sigma)_n(f)>=0,
      quad
      Q_W(f)-hat(Sigma)_n(f)=E_n(f)>=0,
      quad
      E_n(f) arrow.r 0.
    $

    If the receiver is enlarged by one prime and
    $
      c_(S,p)(f)
      =
      W_p(f ast f^sharp)+kappa_(S,p)(f),
    $
    then its remainder form obeys
    $
      K_(S union {p},R)=K_(S,R)-C_(S,p),
    $
    where these symbols denote the Hermitian forms representing the
    corresponding quadratic responses.  The positive carrier propagates
    exactly when
    $
      C_(S,p)<=K_(S,R)
    $
    in form order.
  ],
  proof: [
    Orthogonality of $L_n$ and $I-L_n$ in the output space gives the
    Hilbert--Schmidt Pythagorean identity
    $
      norm(A_S(f))_"HS"^2
      =
      norm(L_n A_S(f))_"HS"^2
      +
      norm((I-L_n)A_S(f))_"HS"^2.
    $
    The same identity for $M_n$ and $C_(S,R)f$, added to the assumed
    positive-remainder factorization, gives the exact equality with $E_n$.
    Strong convergence of finite-rank projections gives convergence of the
    vector tail, and gives convergence of the Hilbert--Schmidt tail after
    summing over any orthonormal basis.

    The final formula is the completed-defect recurrence
    $D_(S union {p})=D_S-c_(S,p)$ written in Hermitian-form language.
    Its successor is nonnegative exactly when
    $c_(S,p)(f)<=D_S(f)$ for every admitted $f$, which is the displayed form
    order.  The form $C_(S,p)$ need not itself be nonnegative.
  ],
  boundary: [
    The theorem constructs the complete vanishing error once the positive
    remainder carrier exists; it does not manufacture that carrier.
    Finite-rank refinement of the Sonin square alone converges to
    $Sigma_S$, leaving the structural defect
    $D_S=Q_W-Sigma_S$ unchanged.  Proving
    $C_(S,p)<=K_(S,R)$ through every support and place transition is the
    RH-bearing semilocal domination problem.  A covariant coarea carrier may
    be nonnegative at both contemporary endpoints while this signed
    connection/seam difference points in either direction; the theorem does
    not impose monotonicity per prime.
  ],
)

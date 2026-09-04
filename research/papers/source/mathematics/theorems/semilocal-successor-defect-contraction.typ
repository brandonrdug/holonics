#let semilocal-successor-defect-contraction = (
  key: "theorem:semilocal-successor-defect-contraction",
  kind: [Theorem],
  title: [A semilocal successor carrier is exactly a cross-channel defect contraction],
  status: [Exact equivalence; the arithmetic contraction remains the RH-bearing construction],
  depends: (
    "lemma:normalized-euler-resolvent-return",
    "theorem:completed-defect-recurrence",
    "theorem:metric-half-jacobian-aperture",
    "theorem:archimedean-remainder-amplitude",
  ),
  claim: [
    Fix one receiver $S$, support aperture $R$, and prime $p ∉ S$.
    Let $cal(T)_(S,R)$ be a Hilbert space of admitted currents.  Suppose the
    predecessor completed defect has an independently constructed amplitude
    $
      C_(S,R):cal(T)_(S,R) arrow.r cal(K)_(S,R),
      quad
      D_S(f)=norm(C_(S,R) f)^2.
    $
    Let $L_R f$ be the logarithmic current entering the exact prime-amplitude
    identity, and write $Theta_S(f)$ for the Hilbert--Schmidt scale-action
    current.  Assume the displayed current-to-amplitude maps are bounded
    and linear on $cal(T)_(S,R)$.

    In the receiver chart, let $P_S$ be the predecessor orthogonal Sonin
    projection, $G_p$ the Euler successor metric, $Pi_p$ the
    $G_p$-orthogonal successor projection, and
    $
      tilde(P)_p=G_p^(1/2) Pi_p G_p^(-1/2).
    $
    Then $tilde(P)_p$ is orthogonal.  If $Theta_S(f)$ commutes with $G_p$,
    the aperture connection has the exact endpoint-amplitude form
    $
      kappa_(S,p)(f)
      =
      norm(Theta_S(f) tilde(P)_p)_"HS"^2
      -
      norm(Theta_S(f) P_S)_"HS"^2.
      quad "(APERTURE)"
    $

    Put $ell_p=log p$, let $cal(R)_p$ be the normalized Euler resolvent on
    the logarithmic-current channel, and define the two direct-sum amplitude
    maps
    $
      X_(S,p,R) f
      =
      (
        C_(S,R) f,
        sqrt(ell_p) L_R f,
        Theta_S(f) P_S
      ),
    $
    $
      Y_(S,p,R) f
      =
      (
        sqrt(ell_p) cal(R)_p L_R f,
        Theta_S(f) tilde(P)_p
      ).
    $
    Their exact balance is
    $
      norm(X_(S,p,R) f)^2
      -
      norm(Y_(S,p,R) f)^2
      =
      D_S(f)-W_p(f ast f^sharp)-kappa_(S,p)(f)
      =
      D_(S union {p})(f).
      quad "(BALANCE)"
    $

    The following are equivalent:

    - $D_(S union {p})(f)>=0$ for every admitted current $f$;
    - $norm(Y_(S,p,R) f)<=norm(X_(S,p,R) f)$ for every $f$;
    - the rule
      $
        Gamma_(S,p,R)(X_(S,p,R) f)=Y_(S,p,R) f
      $
      is well-defined on $op("range")(X_(S,p,R))$ and extends to a
      contraction on its closure; and
    - there is a successor amplitude $C_(S union {p},R)$ satisfying
      $
        norm(C_(S union {p},R) f)^2=D_(S union {p})(f).
      $

    When the contraction is constructed independently, the canonical
    successor amplitude is
    $
      C_(S union {p},R)
      =
      (I-Gamma_(S,p,R)^*Gamma_(S,p,R))^(1/2)
      X_(S,p,R).
      quad "(DEFECT)"
    $
  ],
  proof: [
    Because $tilde(P)_p$ is orthogonal,
    $
      norm(Theta_S(f) tilde(P)_p)_"HS"^2
      =
      op("Tr")(
        Theta_S(f) tilde(P)_p Theta_S(f)^*
      ).
    $
    Trace cyclicity and commutation of $Theta_S(f)^*Theta_S(f)$ with $G_p$
    turn this into
    $
      op("Tr")(
        Theta_S(f) Pi_p Theta_S(f)^*
      ).
    $
    Subtracting the predecessor Hilbert--Schmidt square proves
    ("APERTURE").

    The normalized Euler-resolvent lemma gives
    $
      ell_p(
        norm(cal(R)_p L_R f)^2-norm(L_R f)^2
      )
      =
      W_p(f ast f^sharp).
    $
    Adding this identity to ("APERTURE") and the predecessor carrier norm
    proves ("BALANCE") by the completed-defect recurrence.

    The first two equivalent statements are ("BALANCE").  The norm
    inequality implies that $X f=0$ forces $Y f=0$, so the displayed rule for
    $Gamma$ is well-defined and contractive on the range of $X$; continuity
    extends it to the closure.  Conversely, a contractive $Gamma$ gives the
    norm inequality.

    Finally, the positive defect operator
    $
      D_Gamma=(I-Gamma^*Gamma)^(1/2)
    $
    obeys
    $
      norm(D_Gamma X f)^2
      =
      norm(X f)^2-norm(Gamma X f)^2
      =
      norm(X f)^2-norm(Y f)^2.
    $
    This proves ("DEFECT") and the successor-amplitude equivalence.
  ],
  boundary: [
    The theorem does not construct $Gamma_(S,p,R)$.  Defining it only after
    assuming the norm inequality would restate the desired positivity.
    Since $cal(R)_p$ is expansive on part of the translation spectrum and
    the aperture endpoint may change in either direction, a successful
    $Gamma$ cannot be a block-diagonal passage which treats the prime,
    Sonin, and predecessor-remainder channels independently.  It must mix
    them in one arithmetic colligation.

    The global Poisson map is the known source relation joining local Euler
    factors, additive Fourier return, multiplicative inversion, and
    principal-value normalization; the isolated Euler and Sonin operators
    do not supply the required mixing blocks.  Moreover, this theorem
    assumes a predecessor carrier at the same support $R$.  The published
    archimedean carrier supplies it only at its bounded base aperture, so a
    compatible support-growth contraction remains a second axis of the
    proof.
  ],
)

#let prime-admission-cross-shell = (
  key: "theorem:prime-admission-cross-shell",
  kind: [Theorem],
  title: [A newly admitted prime is raw old--shell cross incidence],
  status: [
    Exact raw support-incidence geometry before Mellin-moment conditioning
  ],
  depends: (
    "theorem:prime-power-aperture-incidence",
  ),
  claim: [
    Let $p>=2$, put
    $
      ell=log p,
      quad
      r=log(p+1),
      quad
      delta=frac(r-ell,2)=frac(1,2)log frac(p+1,p),
    $
    and define the old aperture, successor aperture, and new shell by
    $
      I_p=[-ell/2,ell/2],
      quad
      I_(p+1)=[-r/2,r/2],
      quad
      B_p={u in I_(p+1):u ∉ I_p}.
    $
    Let $P$ and $B$ denote multiplication by $1_(I_p)$ and $1_(B_p)$ in
    $L^2(I_(p+1))$, and let
    $
      (U_p f)(u)=f(u-ell).
    $
    Since $p+1<=p^2$, the compressed prime shift has no old--old or
    shell--shell incidence:
    $
      P U_p P=0,
      quad
      B U_p B=0,
      quad
      (P+B)U_p(P+B)=P U_p B+B U_p P.
      quad "(PURE CROSS)"
    $

    More precisely, translation carries
    $
      [-r/2,-ell/2]
      arrow.r^(+ell)
      [ell-r/2,ell/2]
    $
    from the left shell to the right old boundary strip, and
    $
      [-ell/2,r/2-ell]
      arrow.r^(+ell)
      [ell/2,r/2]
    $
    from the left old boundary strip to the right shell.  All four intervals
    have length $delta$.

    At the support step $R=p+1$, no higher power of the newly admitted prime
    is present because $p^2>p+1$.  Thus its complete first finite-place
    response on the *raw* split is the Hermitian off-diagonal form
    $
      cal(W)_(p,"first")
      =
      (log p)p^(-1/2)
      (U_p+U_p^*)
      quad "compressed to "I_(p+1),
      quad "(PRIME CROSS)"
    $
    with zero diagonal blocks relative to the unconditioned decomposition
    $L^2(I_p) ⊕ L^2(B_p)$.
  ],
  proof: [
    The old interval has length $ell$, so its translate by $ell$ meets it
    only at one endpoint, a null set. This proves $P U_p P=0$.

    A source point contributes to the compressed shift exactly when it lies
    in
    $
      I_(p+1) inter (I_(p+1)-ell)
      =
      [-r/2,r/2-ell].
    $
    The point $-ell/2$ divides this interval into the two displayed pieces.
    Translating them by $ell$ gives the two target pieces. Their common
    length is $(r-ell)/2$. Since $r<=2ell$, neither source shell can land in
    the opposite shell, proving $B U_p B=0$ and ("PURE CROSS").

    The prime-power aperture formula has coefficient
    $(log p)p^(-m/2)$ on the Hermitian shift
    $U_p^m+(U_p^*)^m$. At $R=p+1<p^2$, only $m=1$ meets the aperture. This
    proves ("PRIME CROSS").
  ],
  boundary: [
    This theorem computes the finite-prime incidence before the source's
    Mellin moments are imposed; it does not provide the conditioned successor
    block.  A conditioned shell direction carries an old-region compensator,
    so recharting ("PRIME CROSS") generally creates a shell-diagonal term.
    The conditioned quotient and that returned prime face are calculated in
    `theorem:conditioned-support-quotient-shorting`.  A raw pure-cross form
    still takes either sign as the relative phase changes, and no argument
    assigning an independent positive constituent to the new prime can prove
    the induction step.
  ],
)
